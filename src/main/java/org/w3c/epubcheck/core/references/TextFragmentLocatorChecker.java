package org.w3c.epubcheck.core.references;

import java.text.BreakIterator;

import java.io.IOException;
import java.io.InputStream;
import java.io.UnsupportedEncodingException;
import java.net.URLDecoder;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.Arrays;
import java.util.regex.Pattern;
import java.text.Normalizer;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.Attributes;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import com.adobe.epubcheck.api.EPUBLocation;
import com.adobe.epubcheck.api.Report;
import com.adobe.epubcheck.messages.MessageId;
import com.adobe.epubcheck.ocf.OCFContainer;

import io.mola.galimatias.URL;

/**
 * Validates text fragment locators in media overlay text references.
 *
 * <p>Text fragment locators (e.g., {@code :~:text=hello,world}) allow media overlays
 * to reference specific text passages without requiring element IDs in the content
 * document. This checker validates that referenced text can be unambiguously
 * located in the target document.</p>
 *
 * @see <a href="https://wicg.github.io/scroll-to-text-fragment/">Text Fragments spec</a>
 */
public final class TextFragmentLocatorChecker {

  private static final char BLOCK_BOUNDARY = '\u0000';
  private static final char SENTINEL_PLACEHOLDER = '\u0001';
  private static final Pattern WHITESPACE = Pattern.compile("\\p{IsWhite_Space}+");
  private static final Pattern MULTI_SPACE = Pattern.compile("  +");
  private static final int CONTEXT_WINDOW = 1024;

  private static final Set<String> BLOCK_ELEMENTS = buildBlockElementSet();

  private final Map<URL, DocumentCache> documentCache = new HashMap<>();
  private final OCFContainer container;
  private final Report report;

  public TextFragmentLocatorChecker(OCFContainer container, Report report) {
    this.container = container;
    this.report = report;
  }

  /**
   * Check a text fragment locator reference.
   *
   * @param fragment     the fragment identifier (starting with :~:text=)
   * @param documentURL  URL of the target XHTML document within the container
   * @param location     the location of the reference for error reporting
   */
  public void check(String fragment, URL documentURL, EPUBLocation location) {
    if (fragment == null || !fragment.startsWith(":~:text=")) {
      return;
    }

    DocumentCache cached = getDocumentCache(documentURL);
    if (cached == null) {
      // Document couldn't be parsed; error already reported elsewhere
      return;
    }

    String normalizedText = cached.normalizedText;

    for (String rawSelector : splitTextDirectives(fragment)) {
      TextSelector selector = parseTextSelector(rawSelector);
      if (selector == null) {
        report.message(MessageId.MED_019, location, rawSelector);
        continue;
      }

      MatchResult result = countMatches(normalizedText, selector);

      if (result.count == 0) {
        report.message(MessageId.MED_020, location, rawSelector);
      } else if (result.count > 1) {
        report.message(MessageId.MED_021, location, rawSelector, result.count);
      } else if (result.boundaryCrossing) {
        report.message(MessageId.MED_022, location, rawSelector);
      }
    }
  }

  // -------------------------------------------------------------------------
  // Matching
  // -------------------------------------------------------------------------

  private MatchResult countMatches(String docNorm, TextSelector sel) {
    boolean hasEnd = sel.end != null;
    boolean hasSuffix = sel.suffix != null;

    String start = collapseAndStripEdges(sel.start, true, !(hasEnd || hasSuffix));
    String end = hasEnd ? collapseAndStripEdges(sel.end, false, !hasSuffix) : null;
    String prefix = sel.prefix != null ? collapseWhitespace(sel.prefix) : null;
    String suffix = sel.suffix != null ? collapseWhitespace(sel.suffix) : null;

    if (start.isEmpty()) {
      return new MatchResult(0, false);
    }

    // Fast path: no context terms and no end range
    if (end == null && prefix == null && suffix == null) {
      int count = 0;
      int p = 0;
      while (count < 2 && (p = docNorm.indexOf(start, p)) >= 0) {
        count++;
        p++;
      }
      return new MatchResult(count, false);
    }

    int matches = 0;
    int pos = 0;
    int lastMatchStart = -1;
    int lastMatchEnd = -1;

    while (true) {
      int i = docNorm.indexOf(start, pos);
      if (i < 0) {
        break;
      }

      if (end != null) {
        // Check word boundary at start of match (only if no prefix)
        if (prefix == null && isWordChar(start.codePointAt(0)) && !isWordBoundary(docNorm, i)) {          pos = i + 1;
          continue;  // Try next start position
        }

        // Find the earliest end occurrence after start, satisfying context
        int j = docNorm.indexOf(end, i + start.length());
        boolean matched = false;

        while (j >= 0) {
          int matchEnd = j + end.length();

          // Check word boundary at end
          if (suffix == null && isWordChar(end.codePointBefore(end.length())) && !isWordBoundary(docNorm, matchEnd)) {
            j = docNorm.indexOf(end, j + 1);
            continue;
          }

          // Check prefix (tied to start position)
          if (prefix != null && !prefixMatches(docNorm, i, prefix)) {
            break;
          }

          // Check suffix
          if (suffix != null && !suffixMatches(docNorm, matchEnd, suffix)) {
            j = docNorm.indexOf(end, j + 1);
            continue;
          }

          matched = true;
          lastMatchStart = i;
          lastMatchEnd = matchEnd;
          break;
        }

        if (matched) {
          matches++;
          if (matches >= 2) {
            return new MatchResult(matches, false);
          }
        }
        pos = i + 1;
      } else {
        int matchEnd = i + start.length();

        // Check word boundary at start (only if no prefix)
        if (prefix == null && isWordChar(start.codePointAt(0)) && !isWordBoundary(docNorm, i)) {
          pos = i + 1;
          continue;
        }

        // Check word boundary at end
        if (suffix == null && isWordChar(start.codePointBefore(start.length())) && !isWordBoundary(docNorm, matchEnd)) {
          pos = i + 1;
          continue;
        }

        // Check prefix
        if (prefix != null && !prefixMatches(docNorm, i, prefix)) {
          pos = i + 1;
          continue;
        }

        // Check suffix
        if (suffix != null && !suffixMatches(docNorm, matchEnd, suffix)) {
          pos = i + 1;
          continue;
        }

        matches++;
        lastMatchStart = i;
        lastMatchEnd = matchEnd;
        if (matches >= 2) {
          return new MatchResult(matches, false);
        }
        pos = i + 1;
      }
    }

    if (matches != 1) {
      return new MatchResult(matches, false);
    }

    // Exactly one match - check each parameter span for boundary crossings
    boolean crossing = false;

    // Check prefix span
    if (sel.prefix != null) {
      String p = collapseWhitespace(sel.prefix);
      String before = docNorm.substring(0, lastMatchStart);
      int beforeEnd = rstripSpaceAndSentinel(before);
      String pNorm = stripRight(p);
      int pStartInBefore = beforeEnd - pNorm.length();
      crossing = hasBoundaryCrossing(docNorm, Math.max(0, pStartInBefore), beforeEnd);
    }

    // Check start term span
    String startNorm = collapseAndTrim(sel.start);
    crossing = crossing || hasBoundaryCrossing(docNorm, lastMatchStart,
            lastMatchStart + startNorm.length());

    // Check end term span (between end of start and end of match)
    if (sel.end != null) {
      crossing = crossing || hasBoundaryCrossing(docNorm,
              lastMatchStart + startNorm.length(), lastMatchEnd);
    }

    // Check suffix span
    if (sel.suffix != null) {
      String s = collapseWhitespace(sel.suffix);
      String after = docNorm.substring(lastMatchEnd);
      int suffixStart = lstripSpaceAndSentinel(after);
      String sNorm = stripRight(s);
      crossing = crossing || hasBoundaryCrossing(docNorm,
              lastMatchEnd + suffixStart, lastMatchEnd + suffixStart + sNorm.length());
    }

    return new MatchResult(matches, crossing);
  }

  private boolean prefixMatches(String docNorm, int pos, String prefix) {
    int windowStart = Math.max(0, pos - prefix.length() - CONTEXT_WINDOW);
    String before = docNorm.substring(windowStart, pos).replace(BLOCK_BOUNDARY, ' ');
    before = MULTI_SPACE.matcher(before).replaceAll(" ");
    String p = stripRight(prefix);

    if (!stripRight(before).endsWith(p)) {
      return false;
    }

    // If prefix has trailing space, require space in document before textStart
    if (prefix.endsWith(" ")) {
      if (stripRight(before).length() >= before.length()) {
        return false;
      }
    }

    // Ensure the prefix starts at a word boundary
    String beforeStripped = stripRight(before);
    int preStart = beforeStripped.length() - p.length();
    if (preStart > 0 && isWordChar(p.codePointAt(0)) && !isWordBoundary(beforeStripped, preStart)) {
      return false;
    }

    return true;
  }

  private boolean suffixMatches(String docNorm, int pos, String suffix) {
    int windowEnd = Math.min(docNorm.length(), pos + suffix.length() + CONTEXT_WINDOW);
    String after = docNorm.substring(pos, windowEnd).replace(BLOCK_BOUNDARY, ' ');
    after = MULTI_SPACE.matcher(after).replaceAll(" ");
    String s = stripLeft(suffix);

    if (!stripLeft(after).startsWith(s)) {
      return false;
    }

    // If suffix has leading space, require space in document after textEnd
    if (suffix.startsWith(" ")) {
      if (stripLeft(after).length() >= after.length()) {
        return false;
      }
    }

    // Ensure the suffix ends at a word boundary
    String afterStripped = stripLeft(after);
    int sufEnd = s.length();
    if (isWordChar(s.codePointBefore(s.length())) && !isWordBoundary(afterStripped, sufEnd)) {
      return false;
    }

    return true;
  }

  private boolean hasBoundaryCrossing(String docNorm, int start, int end) {
    if (start < 0 || end > docNorm.length() || start >= end) {
      return false;
    }
    return docNorm.substring(start, end).indexOf(BLOCK_BOUNDARY) >= 0;
  }


  /**
   * Check if position is a word boundary per UAX #29.
   */
  private boolean isWordBoundary(String text, int position) {
    if (position <= 0 || position >= text.length()) {
      return true;
    }

    int prevCodePoint = text.codePointBefore(position);
    int nextCodePoint = text.codePointAt(position);

    // If either adjacent character is not a letter/digit, it's a boundary
    if (!Character.isLetterOrDigit(prevCodePoint) || !Character.isLetterOrDigit(nextCodePoint)) {
      return true;
    }

    // Both sides are letters/digits - use UAX #29 for cases like contractions
    BreakIterator wordBreaker = BreakIterator.getWordInstance(Locale.ROOT);
    wordBreaker.setText(text);
    return wordBreaker.isBoundary(position);
  }
  /**
   * Check if character is a word character (Unicode letter or digit).
   * Used for quick boundary heuristics where full UAX #29 isn't needed.
   */
  private boolean isWordChar(int codePoint) {
    return Character.isLetterOrDigit(codePoint);
  }


  // -------------------------------------------------------------------------
  // Parsing
  // -------------------------------------------------------------------------

  private DocumentCache getDocumentCache(URL documentURL) {
    DocumentCache cached = documentCache.get(documentURL);
    if (cached != null) {
      return cached;
    }

    try (InputStream is = container.openStream(documentURL)) {
      if (is == null) {
        return null;
      }

      String text = parseDocumentText(is);
      String normalized = normalizeDocument(text);

      DocumentCache entry = new DocumentCache(normalized);
      documentCache.put(documentURL, entry);
      return entry;
    } catch (IOException | SAXException | ParserConfigurationException e) {
      // Parse errors are reported elsewhere
      return null;
    }
  }

  private String parseDocumentText(InputStream is)
          throws SAXException, IOException, ParserConfigurationException {
    SAXParserFactory factory = SAXParserFactory.newInstance();
    factory.setNamespaceAware(true);
    factory.setFeature("http://xml.org/sax/features/external-general-entities", false);
    factory.setFeature("http://xml.org/sax/features/external-parameter-entities", false);
    SAXParser parser = factory.newSAXParser();

    TextContentHandler handler = new TextContentHandler();
    parser.parse(new InputSource(is), handler);
    return handler.getText();
  }

  private static class TextContentHandler extends DefaultHandler {

    private final StringBuilder text = new StringBuilder();
    private int skipDepth = 0;

    @Override
    public void startElement(String uri, String localName, String qName, Attributes attributes) {
      String name = localName.toLowerCase();

      if (skipDepth > 0) {
        skipDepth++;
        return;
      }

      if ("head".equals(name) || "script".equals(name) || "style".equals(name)) {
        skipDepth = 1;
        return;
      }

      if (BLOCK_ELEMENTS.contains(name)) {
        text.append(' ').append(BLOCK_BOUNDARY).append(' ');
      }
    }

    @Override
    public void endElement(String uri, String localName, String qName) {
      String name = localName.toLowerCase();

      if (skipDepth > 0) {
        skipDepth--;
        return;
      }

      if (BLOCK_ELEMENTS.contains(name)) {
        text.append(' ').append(BLOCK_BOUNDARY).append(' ');
      }
    }

    @Override
    public void characters(char[] ch, int start, int length) {
      if (skipDepth == 0) {
        text.append(ch, start, length);
      }
    }

    public String getText() {
      return text.toString();
    }
  }

  // -------------------------------------------------------------------------
  // Text normalization
  // -------------------------------------------------------------------------

  private String normalizeDocument(String text) {
    text = text.replace(BLOCK_BOUNDARY, SENTINEL_PLACEHOLDER);
    text = collapseAndTrim(text);
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < text.length(); i++) {
      char c = text.charAt(i);
      if (c == SENTINEL_PLACEHOLDER) {
        sb.append(' ').append(BLOCK_BOUNDARY).append(' ');
      } else {
        sb.append(c);
      }
    }
    return sb.toString();
  }

  private String collapseWhitespace(String text) {
    return WHITESPACE.matcher(caseFold(text)).replaceAll(" ");
  }

  private String collapseAndTrim(String text) {
    return collapseWhitespace(text).trim();
  }

  private String collapseAndStripEdges(String text, boolean stripLeft, boolean stripRight) {
    String result = collapseWhitespace(text);
    if (stripLeft) {
      result = stripLeft(result);
    }
    if (stripRight) {
      result = stripRight(result);
    }
    return result;
  }

  private String caseFold(String text) {
    String decomposed = Normalizer.normalize(text.toLowerCase(), Normalizer.Form.NFD);
    return decomposed.replaceAll("\\p{M}", "");
  }

  private String stripLeft(String s) {
    int i = 0;
    while (i < s.length() && s.charAt(i) == ' ') {
      i++;
    }
    return s.substring(i);
  }

  private String stripRight(String s) {
    int i = s.length();
    while (i > 0 && s.charAt(i - 1) == ' ') {
      i--;
    }
    return s.substring(0, i);
  }

  /**
   * Strip space and sentinel characters from the right of a string.
   * Returns the length of the string after stripping (index into original).
   */
  private int rstripSpaceAndSentinel(String s) {
    int i = s.length();
    while (i > 0 && (s.charAt(i - 1) == ' ' || s.charAt(i - 1) == BLOCK_BOUNDARY)) {
      i--;
    }
    return i;
  }

  /**
   * Strip space and sentinel characters from the left of a string.
   * Returns the number of characters stripped (offset into original).
   */
  private int lstripSpaceAndSentinel(String s) {
    int i = 0;
    while (i < s.length() && (s.charAt(i) == ' ' || s.charAt(i) == BLOCK_BOUNDARY)) {
      i++;
    }
    return i;
  }

  // -------------------------------------------------------------------------
  // URL/selector parsing
  // -------------------------------------------------------------------------

  private List<String> splitTextDirectives(String fragment) {
    List<String> result = new ArrayList<>();

    // Find the :~: directive delimiter
    int idx = fragment.indexOf(":~:");
    if (idx < 0) {
      return result;
    }

    String directives = fragment.substring(idx + 3);
    for (String part : directives.split("&")) {
      if (part.startsWith("text=")) {
        result.add(part.substring(5));
      }
    }
    return result;
  }

  private TextSelector parseTextSelector(String raw) {
    String s = raw;

    // Extract suffix (,-suffix)
    String suffix = null;
    int sufIdx = s.lastIndexOf(",-");
    if (sufIdx >= 0) {
      suffix = decodeComponent(s.substring(sufIdx + 2));
      s = s.substring(0, sufIdx);
    }

    // Extract prefix (prefix-,)
    String prefix = null;
    int preIdx = s.indexOf("-,");
    if (preIdx >= 0) {
      prefix = decodeComponent(s.substring(0, preIdx));
      s = s.substring(preIdx + 2);
    }

    // Extract start and optional end (start,end)
    String startRaw = s;
    String end = null;
    int commaIdx = s.indexOf(',');
    if (commaIdx >= 0) {
      startRaw = s.substring(0, commaIdx);
      String endRaw = s.substring(commaIdx + 1);
      if (!endRaw.isEmpty()) {
        end = decodeComponent(endRaw);
      }
    }

    String start = decodeComponent(startRaw);
    if (start == null || start.isEmpty()) {
      return null;
    }

    return new TextSelector(raw, prefix, start, end, suffix);
  }

  private String decodeComponent(String s) {
    if (s == null) {
      return null;
    }
    try {
      return URLDecoder.decode(s.replace("+", " "), "UTF-8");
    } catch (UnsupportedEncodingException e) {
      return s;
    }
  }


  // -------------------------------------------------------------------------
  // Supporting types
  // -------------------------------------------------------------------------

  private static final class TextSelector {

    final String raw;
    final String prefix;
    final String start;
    final String end;
    final String suffix;

    TextSelector(String raw, String prefix, String start, String end, String suffix) {
      this.raw = raw;
      this.prefix = prefix;
      this.start = start;
      this.end = end;
      this.suffix = suffix;
    }
  }

  private static final class MatchResult {

    final int count;
    final boolean boundaryCrossing;

    MatchResult(int count, boolean boundaryCrossing) {
      this.count = count;
      this.boundaryCrossing = boundaryCrossing;
    }
  }

  private static Set<String> buildBlockElementSet() {
    return new HashSet<>(Arrays.asList(
            "address", "article", "aside", "blockquote", "caption", "colgroup",
            "dd", "details", "dialog", "div", "dl", "dt",
            "fieldset", "figcaption", "figure", "footer", "form",
            "h1", "h2", "h3", "h4", "h5", "h6", "header", "hgroup", "hr",
            "legend", "li", "main", "menu", "nav", "ol", "p", "pre",
            "search", "section", "summary",
            "table", "tbody", "td", "tfoot", "th", "thead", "tr", "ul",
            "br"
    ));
  }
}


final class DocumentCache {
  final String normalizedText;

  DocumentCache(String normalizedText) {
    this.normalizedText = normalizedText;
  }
}