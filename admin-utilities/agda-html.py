#!/usr/bin/env python3
"""Render TypeTopology to html, with the urls and module references linked.

Agda's --html backend escapes the prose and the comments as plain text, so
a url in them comes out as something to copy by hand rather than to click,
and a mention of another module is just a name. Nothing in the Agda
sources can change that, and so this script renders the library in the
usual way and then rewrites the result.

Typical use, from anywhere:

    agda-html.py

which runs

    agda --html --html-dir=<out> AllModulesIndex.lagda

in TypeTopology/source, and rewrites the pages in <out>, by default the
html directory beside this script. To rewrite a rendering you already
have, without waiting for Agda:

    agda-html.py --html <dir>

That copies <dir> into <out> first, so the rendering given is never
written to.

What gets linked, in the prose of a literate file and in an Agda comment,
and nowhere else:

    http://, https:// and ftp:// urls
    doi:10.…                        to doi.org
    arXiv:…                         to arxiv.org
    Ordinals.CumulativeHierarchy    to the page of that module
    Ordinals.Notions.lagda          the same, with the suffix removed
    Locales.Frame.opens-are-sets    to the page of the module part
    FinitePigeon.agda               to the module with that file name
    [1] and [1, 2]                  to the references on the same page

A module reference is linked only when a page of that name is there to
link to, so a name that points at nothing is left as it is, and reported
by --unresolved. Those are worth reading: most are references that went
stale when a module was renamed. Email addresses are deliberately left
alone.

A page with links in it reads exactly as it did. Agda's own stylesheet
already gives every link no underline and a green background under the
cursor, which is what an identifier in the code does, so the links need
nothing of their own there.

There are two additions. Three buttons in the top right corner of every
page, which stay there while the page scrolls. A magnifying glass leads to
the search page for the whole library, an arrow leads up to the index of
the nearest directory above the module, and a house leads to the index of
the library. A button is left out where the page is the one it would lead
to, so the index of the library itself has none and a directory index has
only the arrow. --search-url says where the search page is, and
--search-url none leaves that button out and keeps the other two. And a
little markdown in the prose and the comments is rendered, `code`,
*emphasis*, **bold**, [text](url) and fenced blocks, with its markup
characters hidden by the stylesheet rather than removed. --no-markdown
leaves it as plain text.

The space that the universe dot needs before a closing bracket in the
source, as in (X : 𝓤 ̇ ), is hidden by the stylesheet in the same way,
so that the page reads (X : 𝓤 ̇) while its text stays as Agda wrote it.
--no-tighten leaves the space showing, and takes the markup off a page
that has it. The space between a universe and its successor, as in 𝓤 ⁺,
is hidden in the same way, so that the page reads 𝓤⁺, except on a line
that defines a name ending in ⁺, such as 𝓤⁺ = 𝓤 ⁺, and --no-tighten-plus
leaves it showing.

Because the markup is hidden, a line of prose with a link in it renders
narrower than it is in the source, by the length of the url and the
brackets, so prose is wrapped by the text the reader sees, and the text
of a link, of emphasis or of code may run over one line break. The
script measures every page as rendered and reports the lines wider than
80 characters, and the lines that hidden markup leaves short in the
middle of a paragraph; --overflow lists them and --width changes the
limit.
"""

import argparse, collections, glob, html, os, re, shutil, subprocess, sys
import unicodedata

HERE = os.path.dirname(os.path.abspath(__file__))

# Agda puts the whole document in one <pre>, as a flat sequence of <a>
# elements with no nesting: a prose block between two code blocks is a
# single <a id="1" class="Background">…</a>, and an Agda comment is a
# single <a class="Comment">…</a>. The body of one of those is escaped
# text with no markup in it whatsoever, which is what makes matching the
# elements with a regular expression, rather than parsing the page, a
# reasonable thing to do here.
#
# The <span> case is this script reading back a page it rewrote before,
# for which see below. Agda emits no span of its own anywhere.

ELEMENT = re.compile(r'<(a|span)\b([^>]*)>(.*?)</\1>', re.S)
CLASS = re.compile(r'class="([^"]*)"')
TAG = re.compile(r'<[^>]+>')

LINKABLE_CLASSES = {"Background", "Comment"}

# The links this script makes, and no others: Agda gives every link of its
# own an id and a class as well as an href.

OURS = re.compile(r'<a href="([^"]*)">')
OUR_LINK = re.compile(r'<a href="[^"]*">[^<]*</a>')

# A link to a page of the library, with the text it was made from. When
# that text is not the module it points to, the link rests on a reading of
# the name rather than on the name itself, and is reported.

TO_A_PAGE = re.compile(r'<a href="([^"]*)\.html(#\d+)?">([^<]*)</a>')

# The defining occurrence of a name, which Agda writes as a link to its
# own anchor on its own page. Every other occurrence of the name links to
# that anchor, so this is the one place the name is defined.

DEFINITION = re.compile(r'<a id="(\d+)" href="([^"]*)#(\d+)" class="[^"]*">([^<]*)</a>')

# A module declared inside the page itself, which Agda writes as a link to
# an anchor of the same page. A bare name in the prose is far more likely
# to mean one of these than a file elsewhere with the same last component,
# so those names are left alone.

OWN_MODULE = re.compile(r'<a id="\d+" href="([^"]*)#\d+" class="Module">([^<]*)</a>')

# An <a> cannot contain another <a>: a browser closes the outer one when it
# meets the inner, which would throw the rest of the prose block out of its
# element and leave a stray end tag behind. So an element that gains a link
# becomes a <span> with the same attributes. The id still serves as a
# fragment target, and the stylesheet selects on the class, so this changes
# neither where a link lands nor what the page looks like.

SPAN = "span"

# Three buttons fixed to the top right corner of the window, held in one
# container so that a later run replaces the cluster whole. From the corner
# inwards: the search page for the whole library, the index of the nearest
# directory above the module, and the index of the library. Each shows no
# text, so a reader sees the same characters as before, and the classes,
# which Agda never uses, are what identify them.

SEARCH_URL = "https://www.cs.bham.ac.uk/~mhe/TypeTopologySearch.html"

MAIN_INDEX = "index"

CORNER = ('<div class="TypeTopologyCorner" style="position:fixed; top:8px; '
          'right:8px; z-index:1; display:flex; gap:8px">{buttons}</div>')

BUTTON = ('<a class="TypeTopologyCornerButton" href="{href}" title="{title}" '
          'aria-label="{title}" style="padding:8px; line-height:0; '
          'background:white; border:2px solid #008B00; border-radius:8px; '
          'color:#008B00; box-shadow:0 2px 6px rgba(0,0,0,0.25)">{glyph}</a>')

GLYPH = ('<svg width="28" height="28" viewBox="0 0 24 24" fill="none" '
         'stroke="currentColor" stroke-width="2.5" stroke-linecap="round" '
         'stroke-linejoin="round">{shape}</svg>')

GLASS = '<circle cx="10" cy="10" r="7"/><path d="M15 15 L21 21"/>'
ARROW = '<path d="M12 20 V5"/><path d="M5 12 L12 5 L19 12"/>'
HOUSE = '<path d="M3 11 L12 3 L21 11"/><path d="M6 10 V20 H18 V10"/>'

# The cluster, and the single anchor that runs before there was more than
# one button left behind, both have to come off before the new cluster goes
# on, or a page keeps a magnifying glass belonging to nothing.

CORNERS = re.compile(r'<div class="TypeTopologyCorner".*?</div>'
                     r'|<a class="TypeTopologySearch"[^>]*>.*?</a>')

LINKABLE = re.compile(r"""  (?P<url>(?:https?|ftp)://\S+)
                          | (?P<doi>\bdoi:10\.\S+)
                          | (?P<arxiv>\b[Aa]r[Xx]iv:\S+)
                          | (?P<module>\b[A-Za-z][A-Za-z0-9'_-]*
                                       (?:\.[A-Za-z][A-Za-z0-9'_-]*)+)
                          | (?P<path>\b(?:[A-Za-z][A-Za-z0-9'_-]*/)+
                                       [A-Za-z][A-Za-z0-9'_-]*
                                       (?:\.[A-Za-z][A-Za-z0-9'_-]*)*)
                          | (?P<bare>\b(?:files?|modules?|submodules?)\s+
                                       (?:`|\\texttt\{)?
                                       (?P<word>[A-Z][A-Za-z0-9'_-]*)
                                       (?![A-Za-z0-9'_-]|\.[A-Za-z]|/))
                       """, re.X)

# An arXiv identifier, new style (1412.7148, 2304.06000v2) or old
# (math/0123456, math.CT/0123456). Anything else after arXiv: is left as
# it is rather than pointed at a page that will not exist.

ARXIV_ID = re.compile(r'\d{4}\.\d{4,5}(?:v\d+)?$'
                      r'|[a-z-]+(?:\.[A-Z]{2})?/\d{7}(?:v\d+)?$')

# Trailing punctuation belongs to the sentence, not to the url. A closing
# bracket is a special case: it belongs to the url when the url opens it
# itself, as in doi.org/10.1016/S0049-237X(08)71989-X, and to the prose
# when it does not, as in (arxiv.org/abs/1904.09193).

CLOSERS = {")": "(", "]": "[", "}": "{"}
TRAILING = ".,;:!?'\"`"
PUNCT_ENTITY = re.compile(r'&(?:gt|lt|quot|apos|#39|nbsp);$')

# How a module is named when a file rather than a module is meant.

SUFFIX = re.compile(r'\.(?:lagda|agda|html)$')


def trim(text):
    "Drop what belongs to the surrounding prose from the end of a match."
    while text:
        entity = PUNCT_ENTITY.search(text)
        if entity:
            text = text[:entity.start()]
            continue
        last = text[-1]
        if last in TRAILING:
            text = text[:-1]
            continue
        if last in CLOSERS and text.count(CLOSERS[last]) < text.count(last):
            text = text[:-1]
            continue
        break
    return text


def target(kind, text):
    """Where a url, doi or arXiv match points, or None to leave it alone.

    The text comes from the page and so is escaped already, in the same way
    that an attribute value is, which is why a url can be used as its own
    href unchanged: an & in a query string is &amp; on both sides.
    """
    if kind == "url":
        if text.endswith("//"):
            return None
        return text.replace('"', "&quot;")
    if kind == "doi":
        return "https://doi.org/" + text[len("doi:"):]
    ident = text.split(":", 1)[1] if ":" in text else ""
    return "https://arxiv.org/abs/" + ident if ARXIV_ID.fullmatch(ident) else None


def by_last_component(name, tails, here):
    """The module whose last component is this name, when there is one.

    Several modules can end in the same component, since the library has
    79 modules called index, 19 called Type and so on, and then the one in
    the same directory as the page doing the referring is taken. Failing
    that, nothing: a guess between two strangers is worse than no link.

    A name of several components, such as BrouwerOrdinals.Order, first
    narrows the candidates to the modules whose names end with all of
    them, so that a partial path picks out its module among those sharing
    the last component. When no module ends that way, the candidates are
    kept as they were, which lets a reference survive its module moving
    to another directory.
    """
    candidates = tails.get(name.rsplit(".", 1)[-1], set())
    if "." in name:
        ending = {c for c in candidates
                  if c == name or c.endswith("." + name)}
        if ending:
            candidates = ending
    if len(candidates) > 1:
        home = here.rsplit(".", 1)[0] + "."
        near = {c for c in candidates if c.startswith(home)}
        if len(near) == 1:
            candidates = near
    return next(iter(candidates)) if len(candidates) == 1 else None


def module_target(name, pages, tails, here):
    """Where a dotted name points, how much of it the link covers, and how.

    A name can name a module outright, with or without a file suffix. It
    can be an identifier qualified by its module, in which case the module
    part is found here and the caller extends the link over the identifier
    when that page defines it, and otherwise leaves the rest of the name
    outside the link. Failing
    both, its last component is tried, which is what lets a reference
    survive its module moving to another directory, and what resolves a
    file name written without its directory.

    Returns the href, the length of the text to link, and how it was
    resolved, or None when no page of the library answers to the name. The
    how "short qualified" is a module named by its last components, which
    the caller keeps only when the identifier after it is defined there.
    The how is "exact" when the text names a page as it stands, and
    "last component" when the link rests on the reading above, which the
    run reports separately so that it can be checked.
    """
    base = SUFFIX.sub("", name)
    if base in pages:
        return base + ".html", len(name), "exact"
    parts = base.split(".")
    for k in range(len(parts) - 1, 0, -1):
        prefix = ".".join(parts[:k])
        if prefix in pages:
            return prefix + ".html", len(prefix), "exact"
    found = by_last_component(base, tails, here)
    if found:
        return found + ".html", len(name), "last component"
    # An identifier qualified by its module written short, as in
    # RectApply.rect-ssub for a module whose page is
    # DialogueTreesHeight.BrouwerOrdinals.RectApply. The module part is
    # resolved by its last component, and accepted only when the page
    # found ends with the whole of that part, so that Foo.RectApply.x does
    # not reach a RectApply outside a directory Foo. Even so, a short
    # name such as J or Idempotents is weak evidence, being as likely an
    # initial, as in J.D. Christensen, or a file of another system, as in
    # Idempotents.v, so the caller keeps the link only when the page found
    # defines the identifier after the dot.
    for k in range(len(parts) - 1, 0, -1):
        prefix = ".".join(parts[:k])
        found = by_last_component(prefix, tails, here)
        if found and (found == prefix or found.endswith("." + prefix)):
            return found + ".html", len(prefix), "short qualified"
    return None


def definitions(htmldir):
    """The names each page defines, with the anchor of each, read lazily.

    A name defined more than once in a page, in two submodules say, is
    left out, since a link to one of the two would be a guess.
    """
    cache = {}

    def defined(page):
        if page not in cache:
            names, twice = {}, set()
            path = os.path.join(htmldir, page + ".html")
            text = open(path, encoding="utf-8").read() if os.path.exists(path) else ""
            for ident, href, anchor, name in DEFINITION.findall(text):
                if ident == anchor and href == page + ".html":
                    if name in names:
                        twice.add(name)
                    names[name] = anchor
            cache[page] = {n: a for n, a in names.items() if n not in twice}
        return cache[page]

    return defined


# What may follow an identifier in a sentence: the end of the word, the
# punctuation of the sentence, a closing bracket, or an escaped quote.

AFTER_IDENTIFIER = TRAILING + ")]}"
QUOTE_ENTITIES = ("&quot;", "&#39;", "&apos;")


def identifier_after(text, defined):
    """The longest name that the page defines and the text begins with.

    The text is what follows the dot after a module name, up to the next
    space. An identifier can contain characters that a module name cannot,
    such as < (escaped as &lt;) and Unicode symbols, which is why the
    names are looked up rather than matched by a pattern.
    """
    word = re.match(r'\S*', text).group(0)
    best = None
    for name in defined:
        if word.startswith(name) and (best is None or len(name) > len(best)):
            rest = word[len(name):]
            if (not rest or rest[0] in AFTER_IDENTIFIER
                    or rest.startswith(QUOTE_ENTITIES)):
                best = name
    return best


def path_target(name, pages):
    """Where a reference written as a path, such as MLTT/Id.lagda, points.

    A path is required to name a module outright, since the shapes that a
    dotted name is also tried in would, on a name with a slash in it, be
    guesswork. The library is under source, so a path written from the
    root of the development resolves as well as one written from source.
    """
    last = name.rsplit("/", 1)[1]
    if not (last[0].isupper() or SUFFIX.search(name)):
        return None
    module = SUFFIX.sub("", name).replace("/", ".")
    if module.startswith("source."):
        module = module[len("source."):]
    return (module + ".html", len(name), "exact") if module in pages else None


def linkify(text, pages, tails, here, own, defined):
    """Link everything linkable in one stretch of escaped text.

    Returns the text, the links made, each with how it was resolved, and
    the names that look like references and answer to nothing.
    """
    out, pos, links, unresolved = [], 0, [], []
    for m in LINKABLE.finditer(text):
        name, start = m.group(0), m.start()
        if start < pos:
            # Inside an identifier that an earlier link has taken in,
            # which the pattern stopped short of at a symbol.
            continue
        if m.lastgroup == "bare":
            # "the module Frame", a name with no directory and no suffix,
            # which is worth resolving because a reference written that
            # way survives its module moving to another directory.
            name, start = m.group("word"), m.start("word")
            # A submodule of this very file is what a bare name usually
            # means when the file declares one, so it is left alone.
            found = None if name in own else by_last_component(name, tails, here)
            if found is None:
                # Worth reporting only when some module does end that way,
                # so that it is an ambiguity rather than an ordinary word,
                # as in "the file I wrote".
                if name in tails and name not in own:
                    unresolved.append(name)
                continue
            href, length, how = found + ".html", len(name), "bare name"
            linked = name
            out.append(text[pos:start])
            out.append(f'<a href="{href}">{linked}</a>')
            pos = start + len(linked)
            links.append((href, how))
            continue
        if m.lastgroup in ("module", "path"):
            if m.lastgroup == "module":
                found = module_target(name, pages, tails, here)
            else:
                found = path_target(name, pages)
                if found is None and "." in name.rsplit("/", 1)[1]:
                    # Something like TypeTopology/UF.Sets.lagda, where the
                    # part after the last slash is a module named in the
                    # ordinary way. Without this the path would swallow it
                    # and neither shape would link.
                    tail = name.rsplit("/", 1)[1]
                    found = module_target(tail, pages, tails, here)
                    if found is not None:
                        start, name = start + len(name) - len(tail), tail
            if found is None:
                # What is worth reporting as a reference that has gone
                # stale, as against the abbreviations (i.e, e.g, w.r.t),
                # the mail domains and the notation that this necessarily
                # also matches. A module has a capital letter somewhere in
                # it, since only the directories deprecated and gist are
                # lower case, and a file name says outright what it is.
                # A path that is not a file name is left out on the same
                # grounds.
                if SUFFIX.search(name) or (m.lastgroup == "module"
                                           and any(part[:1].isupper()
                                                   for part in name.split("."))):
                    unresolved.append(name)
                continue
            href, length, how = found
            linked = name[:length]
            # A qualified identifier links to its definition, as a whole,
            # when the page of its module defines it. Otherwise the module
            # part alone is linked, as before, unless the module was named
            # short, in which case nothing is.
            after, ident = start + length, None
            if m.lastgroup == "module" and text[after:after + 1] == ".":
                page = href[:-len(".html")]
                ident = identifier_after(text[after + 1:], defined(page))
                if ident is not None:
                    href = f"{href}#{defined(page)[ident]}"
                    linked = text[start:after + 1 + len(ident)]
            if how == "short qualified":
                if ident is None:
                    # Reported on the same terms as any other name that
                    # answers to nothing, so a path is not.
                    if m.lastgroup == "module":
                        unresolved.append(name)
                    continue
                how = "last component"
        else:
            linked = trim(name)
            href = target(m.lastgroup, linked)
            how = "exact"
            if href is None:
                continue
        out.append(text[pos:start])
        out.append(f'<a href="{href}">{linked}</a>')
        pos = start + len(linked)
        links.append((href, how))
    out.append(text[pos:])
    return "".join(out), links, unresolved


def transform(page, pages, tails, here, own, defined):
    """Rewrite one page.

    Returns the new page, the links added to it, and the names in it that
    look like module references but answer to no page.
    """
    links, unresolved = [], []

    def element(m):
        tag, attrs, body = m.group(1), m.group(2), m.group(3)
        # A link Agda made itself has an href and is left as it is.
        if "href" in attrs:
            return m.group(0)
        found = CLASS.search(attrs)
        if not found or found.group(1) not in LINKABLE_CLASSES:
            return m.group(0)
        # The body is escaped text, except that in a page rewritten
        # before it also holds the links of that earlier run, which are
        # kept as they are while the text around them is looked at again.
        # That is what lets a rendering be brought up to date with a later
        # version of this script without being made afresh.
        out, added, pos = [], [], 0
        for keep in list(OUR_LINK.finditer(body)) + [None]:
            gap = body[pos:keep.start()] if keep else body[pos:]
            if "<" in gap:
                return m.group(0)
            done, made, missing = linkify(gap, pages, tails, here, own, defined)
            out.append(done)
            added.extend(made)
            unresolved.extend(missing)
            if keep:
                out.append(keep.group(0))
                pos = keep.end()
        if not added:
            return m.group(0)
        links.extend(added)
        return f'<{SPAN}{attrs}>{"".join(out)}</{SPAN}>'

    return ELEMENT.sub(element, page), links, unresolved


def visible(page):
    "The text of a page with all the markup taken out."
    return TAG.sub("", page)


# What the reader sees. The stylesheet hides <md-mark>, <dot-space>,
# <universe-dot> and <plus-space> with their contents, so those go, and
# the tags of everything else, and the entities Agda wrote for < > & are
# read back.

HIDDEN = re.compile(r'<(md-mark|dot-space|universe-dot|plus-space)>.*?</\1>',
                    re.S)
HIDDEN_MARK = re.compile(r'<md-mark>')


OPENS = re.compile(r'<(?:a|span)\b[^>]*class="(\w+)"[^>]*>|</(?:a|span)>')


def shown_lines(page):
    """The lines of a page as the reader sees them, each with its source
    line and whether it holds hidden markdown in the prose, that is, in
    a Background element and outside a fenced block. A comment is a
    unit of its own, so what it hides never leaves a paragraph short.
    """
    pre = re.search(r'<pre class="Agda">(.*?)</pre>', page, re.S)
    body = pre.group(1) if pre else page
    # A hidden element may span a line break, as the fence of a block
    # does, so its line breaks are kept, and the two lists stay in step.
    kept = HIDDEN.sub(lambda m: "\n" * m.group(0).count("\n"), body)
    seen = html.unescape(TAG.sub("", kept)).split("\n")
    source = html.unescape(TAG.sub("", body)).split("\n")
    marked, depth, cls = [], 0, None
    for line in body.split("\n"):
        inside = depth > 0 or "<md-block>" in line
        depth += line.count("<md-block>") - line.count("</md-block>")
        prose, pos = False, 0
        for m in OPENS.finditer(line):
            if HIDDEN_MARK.search(line, pos, m.start()) and cls == "Background":
                prose = True
            cls = m.group(1) if m.group(1) else (None if cls else cls)
            pos = m.end()
        if HIDDEN_MARK.search(line, pos) and cls == "Background":
            prose = True
        marked.append(not inside and prose)
    return list(zip(seen, source, marked))


def overflow(htmldir, width):
    """The lines that render wider than the width, and the lines that
    hidden markup leaves short before a continuation of their paragraph.

    Returns (page, line number, shown width, source width, text) tuples,
    the wide ones and the short ones as two lists.
    """
    wide, short = [], []
    for path in sorted(glob.glob(os.path.join(htmldir, "*.html"))):
        here = os.path.basename(path)[:-len(".html")]
        lines = shown_lines(open(path, encoding="utf-8").read())
        for n, (seen, source, marked) in enumerate(lines, 1):
            if len(seen) > width:
                wide.append((here, n, len(seen), len(source), seen))
            elif (marked and seen.strip() and len(source) - len(seen) >= 10
                  and n < len(lines) and lines[n][0].strip()
                  and lines[n][0].strip()[0].islower()):
                # A line with a url or more hidden in it, which the hiding
                # leaves well short of the limit, or which was wrapped onto
                # a line of its own because of its url, leaving the line
                # before it short. The next line beginning in lower case is
                # what says the paragraph continues.
                before = lines[n - 2][0] if n > 1 else ""
                if (len(seen) < width - 25
                    or (before.strip() and len(before) < width - 25
                        and len(source) > width - 10)):
                    short.append((here, n, len(seen), len(source), seen))
    return wide, short


# A little markdown in the prose and the comments: `code`, *emphasis*,
# **bold**, [text](target) and fenced blocks. The markup characters stay in
# the page, inside <md-mark>, which the stylesheet hides, so the text of the
# page is unchanged. Agda emits none of the tags used here, and so all of it
# can be taken off again exactly, which is done before the links are made
# and the markdown put back after, so that every run starts from the same
# page. Lists, underscores and runs of three or more asterisks are left as
# they are. The text of a piece may run over one line break, so that a
# paragraph can be wrapped by the text the reader sees, with the url of a
# link falling where it may. A piece of code may do so only when it is
# short, at most 32 characters with the break, which fits an expression
# and keeps a stray backtick, or the TeX quotes `like this', from pairing
# with a backtick on the next line.

MARKDOWN = [
    ("block", re.compile(r'(?m)^([ \t]*(`{3,})[^`\n]*\n)'
                         r'((?:(?![ \t]*\2).*\n)*?(?:(?![ \t]*\2).*))'
                         r'(\n[ \t]*\2`*[ \t]*)$')),
    ("code", re.compile(r'(?<!`)(`)([^`\n]+|(?=[^`]{1,32}`)[^`\n]*\n[ \t]*[^`\n]+)'
                        r'(`)(?!`)')),
    ("link", re.compile(r'(\[)((?:[^\]\n]*\n[ \t]*)?[^\]\n]+)(\]\(([^)\s]+)\))')),
    ("strong", re.compile(r'(?<!\*)(\*\*)([^\s*](?:[^*\n]*(?:\n[ \t]*[^*\n]*)?[^\s*])?)'
                          r'(\*\*)(?!\*)')),
    ("em", re.compile(r'(?<![*\w`])(\*)([A-Za-z][^*\n`]{0,60}?'
                      r'(?:\n[ \t]*[^*\n`]{0,60}?)?[A-Za-z.])(\*)(?![*\w])')),
]

MARKDOWN_TAGS = re.compile(r'</?(?:md-mark|md-block|code|em|strong)>')
MARKDOWN_LINK = re.compile(r'<a class="Markdown" href="[^"]*">([^<]*)</a>')
URL = re.compile(r'(?:https?|ftp)://')


def markdown_target(target, pages):
    "Where a [text](target) points, a url or a page by its file name, or None."
    if URL.match(target):
        return target.replace('"', "&quot;")
    name = SUFFIX.sub("", target.rsplit("/", 1)[-1])
    return name + ".html" if name in pages else None


def positions(body):
    """The visible text of an element body, where each of its characters
    is in the body, and whether it is inside a link.
    """
    text, where, inside, depth, i = [], [], [], 0, 0
    while i < len(body):
        if body[i] == "<":
            j = body.index(">", i) + 1
            depth += body.startswith("<a ", i) - body.startswith("</a>", i)
            i = j
        else:
            text.append(body[i]), where.append(i), inside.append(depth > 0)
            i += 1
    return "".join(text), where, inside


def mark(body, pages):
    """Put the markdown in one element's body, which may hold links already.

    Returns the new body and what was rendered, as (kind, text) pairs.
    """
    text, where, inside = positions(body)
    taken = [False] * len(text)
    inserts, rendered = [], []
    for kind, rx in MARKDOWN:
        for m in rx.finditer(text):
            s, e = m.start(), m.end()
            body_group = 3 if kind == "block" else 2
            first, last = m.end(1), m.start(body_group + 1)
            # Every tag goes in outside a link, so that the tags nest.
            if any(taken[s:e]) or any(inside[k] for k in (s, first - 1,
                                                          last, e - 1)):
                continue
            if kind == "block":
                open_, close = "<md-block>", "</md-block>"
            elif kind == "link":
                href = markdown_target(m.group(4), pages)
                if href is None or any(inside[m.start(2):m.end(2)]):
                    continue
                open_, close = f'<a class="Markdown" href="{href}">', "</a>"
            else:
                open_, close = f"<{kind}>", f"</{kind}>"
            for k in range(s, e):
                taken[k] = True
            # A start goes before its character and an end right after the
            # character before it, so that neither crosses a tag.
            inserts += [(where[s], 2, "<md-mark>"),
                        (where[first - 1] + 1, 1, "</md-mark>" + open_),
                        (where[last], 1, close + "<md-mark>"),
                        (where[e - 1] + 1, 0, "</md-mark>")]
            rendered.append((kind, m.group(0)))
    # Inserted from the end, so that the positions still hold. At one
    # position an end is placed before a start.
    for pos, _, tag in sorted(inserts, reverse=True):
        body = body[:pos] + tag + body[pos:]
    return body, rendered


def unspan(page):
    """Make an element that is a span with no link left in it an <a>
    again, which is what it was before this script put a link inside it.
    """
    def element(m):
        if m.group(1) == SPAN and "<a " not in m.group(3):
            return f"<a{m.group(2)}>{m.group(3)}</a>"
        return m.group(0)

    return ELEMENT.sub(element, page)


def unmark(page):
    "Take the markdown off a page, giving back the page it was put on."
    return unspan(MARKDOWN_LINK.sub(r"\1", MARKDOWN_TAGS.sub("", page)))


def markdown(page, pages):
    "Put the markdown in every prose block and comment of a page."
    rendered = []

    def element(m):
        tag, attrs, body = m.group(1), m.group(2), m.group(3)
        found = CLASS.search(attrs)
        if "href" in attrs or not found or \
           found.group(1) not in LINKABLE_CLASSES:
            return m.group(0)
        new, done = mark(body, pages)
        if not done:
            return m.group(0)
        rendered.extend(done)
        if "<a " in new:
            tag = SPAN
        return f"<{tag}{attrs}>{new}</{tag}>"

    return ELEMENT.sub(element, page), rendered


# The space between the universe dot and a closing bracket, which the
# source needs because the dot is a postfix operator, and which the
# rendering has no use for now that a browser puts the dot where it
# belongs. It is wrapped in <dot-space>, which the stylesheet hides,
# rather than taken out, so that every character Agda wrote is still in
# the page, which is what the one check in rewrite below rests on, and so
# that showing the spaces again is a matter of taking the markup off.
# Agda emits no element of that name anywhere.
#
# Only ) and } are tightened. A comma keeps its space, because the source
# needs it there as well, a name being allowed to end in a comma, and
# because a space before a comma is the convention of the library
# throughout. The space sits between two elements, in the text of the
# <pre> itself, so none of this reaches inside an element. The dot is
# found by the module it links to rather than by its offset there, which
# moves whenever that module is edited.

DOT = "\u0307"

DOT_SPACE = re.compile(r'(<a\b[^>]*href="MLTT\.Universes\.html#\d+"'
                       r'[^>]*>_?' + DOT + r'</a>)'
                       r' (<a\b[^>]*>[)}])')

DOT_SPACE_TAGS = re.compile(r'</?dot-space>')

# The universe dot itself, with the space the source needs before it,
# which together make the page read (X : 𝓤) as the HoTT book writes it.
# A source with more than one space there has them all hidden.
# It is hidden in the same way as the space above, in <universe-dot>,
# which the stylesheet hides, so that the page still holds every
# character Agda wrote. Only a use of the dot is hidden, its body being
# the dot alone rather than _̇, and the page of MLTT.Universes keeps its
# dots, that being where the notation is explained.

UNIVERSE_DOT = re.compile(r'(?<=</a>)( +)'
                          r'(<a\b[^>]*href="MLTT\.Universes\.html#\d+"'
                          r'[^>]*>' + DOT + r'</a>)')

UNIVERSE_DOT_TAGS = re.compile(r'</?universe-dot>')

NOTATION_PAGE = "MLTT.Universes"


def tighten(page):
    """Hide the space between the universe dot and a closing bracket.

    Returns the new page and how many spaces were hidden in it. A space
    already hidden is left alone, so a page can be given again.
    """
    return DOT_SPACE.subn(r'\1<dot-space> </dot-space>\2', page)


def untighten(page):
    "Show those spaces again, giving back the page they were hidden on."
    return DOT_SPACE_TAGS.sub("", page)


def hide_dots(page):
    """Hide the universe dots, with the space before each of them.

    Returns the new page and how many dots were hidden in it. A dot
    already hidden is left alone, so a page can be given again.
    """
    return UNIVERSE_DOT.subn(r'<universe-dot>\1\2</universe-dot>', page)


def show_dots(page):
    "Show them again, giving back the page they were hidden on."
    return UNIVERSE_DOT_TAGS.sub("", page)


# The space between a universe and its successor, which the source needs
# because ⁺ is a postfix operator, hidden so that the page reads 𝓤⁺ and
# (𝓤 ⊔ 𝓥)⁺ as a paper writes them. It is hidden in the same way as the
# spaces above, in <plus-space>, which the stylesheet hides. The successor
# is found as the ⁺ or ⁺⁺ that links to MLTT.Universes, so that a name
# such as List⁺ is left alone. A line that defines a name ending in ⁺, as
# 𝓤⁺ = 𝓤 ⁺ does in Iterative.Sets, keeps its spaces, since it would
# otherwise read 𝓤⁺ = 𝓤⁺, and the page of MLTT.Universes keeps them all,
# that being where the notation is explained.

PLUS_SPACE = re.compile(r'(?<=</a>) '
                        r'(<a\b[^>]*href="MLTT\.Universes\.html#\d+"'
                        r'[^>]*>⁺⁺?</a>)')

PLUS_SPACE_TAGS = re.compile(r'</?plus-space>')

DEFINES_PLUS = re.compile(r'\s*\S*⁺\s*=(?:\s|$)')


def tighten_plus(page):
    """Hide the space between a universe and its successor.

    Returns the new page and how many spaces were hidden in it. A space
    already hidden is left alone, so a page can be given again.
    """
    lines, hidden = page.split("\n"), 0
    for i, line in enumerate(lines):
        if DEFINES_PLUS.match(html.unescape(TAG.sub("", line))):
            continue
        lines[i], n = PLUS_SPACE.subn(r'<plus-space> </plus-space>\1', line)
        hidden += n
    return "\n".join(lines), hidden


def untighten_plus(page):
    "Show those spaces again, giving back the page they were hidden on."
    return PLUS_SPACE_TAGS.sub("", page)


# The line that says who wrote a file and when, and the markers of a
# later addition, which open with Added and the date and close with End
# of addition, put in bold so that the seams of a file show at a glance.
# Each of them runs to the end of its first sentence, or of its line,
# and a -- that begins a comment line is left as it is. A marker that
# runs into a link is left alone rather than wrapped across it. Nothing
# is added to the text of the page, only the markup that the stylesheet
# makes bold.
#
# The header is the first line of the first prose block of a page, which
# Agda writes as the element with id 1, and it is taken as a header when
# it carries a year, or when it names contributors and nothing else. The
# names are read from the list in README.md, so a contributor who adds
# themselves there the first time they contribute, as that list asks,
# has the headers of their files emboldened with everyone else's. A
# first line that is a title keeps the ordinary weight.

# Added opens a marker on its own, that being how it is always used,
# while a word that also has an ordinary sense, such as Moved, is taken
# as a marker only when the line carries a year. TODO is a marker of its
# own, and the word alone is emboldened, so that what a file still owes
# its reader is easy to find.

SEAMS = ("Updated|Moved|Refactored|Modified|Completed|Revised|Edited|"
         "Removed|Renamed|Extended|Rewritten|Generali[sz]ed|Simplified|"
         "Split|Rephrased|Deprecated")

ADDITION = re.compile(r'(?m)^[ \t]*(?:--[ \t]*)?'
                      r'(?:(Added\b[^\n.]*\.?)'
                      r'|((?:' + SEAMS + r')\b[^\n.]*?'
                      r'(?:19|20)\d\d[^\n.]*\.?)'
                      r'|(End of (?:the )?addition[^\n]*?)[ \t]*$'
                      r'|(TODO)\b)')

BOLD_TAGS = re.compile(r'</?bold-mark>')

YEAR = re.compile(r'\b(?:19|20)\d\d\b')

# The contributors, as the list in README.md gives them, which is one
# item of the form * [Name](url) per line under its own heading. A name
# that the files write in a longer form than the list's, which ALIASES
# records, answers to the same person and the same url.

CONTRIBUTORS = re.compile(r'(?m)^[ \t]*\*[ \t]*\[([^\]\n]+)\]\(([^)\s]+)\)')

CONTRIBUTORS_HEADING = "Current TypeTopology contributors"

AND = re.compile(r'\s+and\s+|\s*,\s*|\s*&\s*')

ALIASES = {"Jonathan Sterling": "Jon Sterling",
           "Bruno da Rocha Paiva": "Bruno Paiva"}


def contributors(root):
    """The list of contributors in README.md, each name with the url of
    their page there, or none.

    A library without that file, which is what rewriting a rendering on
    its own gives, leaves a header of names alone and keeps a dated one.
    """
    try:
        readme = open(os.path.join(root, "README.md"), encoding="utf-8").read()
    except OSError:
        return {}
    below = readme.split(CONTRIBUTORS_HEADING, 1)
    if len(below) < 2:
        return {}
    section = below[1].split("\n##", 1)[0]
    names = dict(CONTRIBUTORS.findall(section))
    for written, listed in ALIASES.items():
        if listed in names:
            names[written] = names[listed]
    return names


def header(text, names):
    """The span of the header at the start of a prose block, or None.

    A dated header runs from the first character to the first full stop
    at or after the year, which keeps an abbreviated month out of it, or
    to the end of the line when there is none. A header of names runs to
    the end of the line, and every name in it has to be in the list of
    contributors, so that a title is left alone.
    """
    line = text.split("\n", 1)[0]
    if not line[:1].strip():
        return None
    found = YEAR.search(line)
    if found:
        stop = line.find(".", found.end())
        return 0, len(line) if stop < 0 else stop + 1
    said = [one for one in AND.split(line.rstrip(" .,")) if one]
    if said and said[-1] == "original date unknown":
        # The idiom of MLTT.Universes for a file whose history was
        # severed by a reorganization: names, then this phrase.
        said = said[:-1]
    if names and said and all(one in names for one in said):
        return 0, len(line.rstrip())
    return None


def bold(page, names):
    """Put the header of a file and the markers of an addition in bold.

    Returns the new page, how many headers and how many markers were
    found in it.
    """
    headers, found = 0, 0

    def element(m):
        nonlocal headers, found
        tag, attrs, body = m.group(1), m.group(2), m.group(3)
        kind = CLASS.search(attrs)
        if "href" in attrs or not kind or \
           kind.group(1) not in LINKABLE_CLASSES:
            return m.group(0)
        text, where, inside = positions(body)
        inserts, spans = [], []
        if 'id="1"' in attrs and kind.group(1) == "Background":
            where_header = header(text, names)
            if where_header:
                spans.append(where_header)
                headers += 1
        for one in ADDITION.finditer(text):
            which = next(i for i in (1, 2, 3, 4) if one.group(i))
            spans.append((one.start(which), one.end(which)))
            found += 1
        for s, e in spans:
            if e <= s or inside[s] or inside[e - 1]:
                continue
            inserts += [(where[s], 1, "<bold-mark>"),
                        (where[e - 1] + 1, 0, "</bold-mark>")]
        if not inserts:
            return m.group(0)
        for pos, _, mark_ in sorted(inserts, reverse=True):
            body = body[:pos] + mark_ + body[pos:]
        return f"<{tag}{attrs}>{body}</{tag}>"

    return ELEMENT.sub(element, page), headers, found


def unbold(page):
    "Take that markup off, giving back the page it was put on."
    return BOLD_TAGS.sub("", page)


# The name of a contributor in the header of a file, and in a marker of
# an addition, linked to the page that the list in README.md gives for
# them. Only those two places get links, so a name in a reference to a
# paper stays plain text. The names are matched with the accents taken
# off both sides, so that a header saying Martín Escardó is linked by
# the list's Martin Escardo, and ALIASES above carries the names the
# files write in a longer form than the list's. A name inside a link
# already, or one that the markup of another pass cuts in two, is left
# as it is.

AUTHOR_LINK = re.compile(r'<a class="Author" href="[^"]*">([^<]*)</a>')


def fold(text):
    """The text with the accents taken off its letters, one character
    for one character, so that a position in it is a position in the
    text.
    """
    folded = []
    for c in text:
        parts = unicodedata.normalize("NFD", c)
        folded.append(parts[0] if all(unicodedata.combining(x)
                                      for x in parts[1:]) else c)
    return "".join(folded)


def author_pattern(names):
    """A pattern for the names of the contributors as a page writes
    them, folded, with the url each matched form links to, or None when
    there are no names.

    An apostrophe in a name is matched in the escaped forms Agda writes
    as well, so that Keri D'Angelo is found in a page that says
    D&#39;Angelo.
    """
    if not names:
        return None
    urls = {}
    for name, url in names.items():
        base = fold(name)
        for form in {base, base.replace("'", "&#39;"),
                     base.replace("'", "&apos;")}:
            urls[form] = url
    ordered = sorted(urls, key=len, reverse=True)
    rx = re.compile(r'(?<!\w)(?:' + "|".join(map(re.escape, ordered))
                    + r')(?!\w)')
    return rx, urls


def link_authors(page, names, pattern):
    """Link the names in the header of a file and in the markers of an
    addition to the contributors' pages.

    Returns the new page and how many names were linked.
    """
    rx, urls = pattern
    linked = 0

    def element(m):
        nonlocal linked
        tag, attrs, body = m.group(1), m.group(2), m.group(3)
        kind = CLASS.search(attrs)
        if "href" in attrs or not kind or \
           kind.group(1) not in LINKABLE_CLASSES:
            return m.group(0)
        text, where, inside = positions(body)
        spans = []
        if 'id="1"' in attrs and kind.group(1) == "Background":
            where_header = header(text, names)
            if where_header:
                spans.append(where_header)
        for one in ADDITION.finditer(text):
            which = next(i for i in (1, 2, 3, 4) if one.group(i))
            if which != 4:
                spans.append((one.start(which), one.end(which)))
        if not spans:
            return m.group(0)
        folded = fold(text)
        inserts, taken = [], set()
        for s, e in spans:
            for one in rx.finditer(folded, s):
                a, b = one.start(), one.end()
                if a >= e:
                    break
                if b > e or (a, b) in taken or any(inside[a:b]) or \
                   "<" in body[where[a]:where[b - 1] + 1]:
                    continue
                taken.add((a, b))
                inserts += [(where[a], 1,
                             f'<a class="Author" '
                             f'href="{urls[one.group(0)]}">'),
                            (where[b - 1] + 1, 0, "</a>")]
                linked += 1
        if not inserts:
            return m.group(0)
        for pos, _, mark_ in sorted(inserts, reverse=True):
            body = body[:pos] + mark_ + body[pos:]
        # The element holds a link now, so it becomes a span, which
        # unspan undoes once the link is taken off.
        return f"<{SPAN}{attrs}>{body}</{SPAN}>"

    return ELEMENT.sub(element, page), linked


def unlink_authors(page):
    "Take those links off, giving back the page they were put on."
    return unspan(AUTHOR_LINK.sub(r"\1", page))


# A citation [1] in the prose or a comment, linked to the entry of the
# list of references on the same page that begins a line with [1] or
# [1]:, or with a markdown bullet - [1]:, and each number of [1, 2] linked to its own entry. A number is
# linked only when the page has exactly one entry for it, so that a page
# with two lists numbered from 1, or a citation of a list kept in another
# file, is left as it is and reported. A link in markdown, [text](url),
# is not a citation. Nothing is added to the text of the page, only the
# anchor around the [n] of an entry and the link around a citation.

ENTRY = re.compile(r'(?m)^[ \t]*(?:--[ \t]*)?(?:[-*][ \t]+)?'
                   r'(\[(\d+)\]):?(?=\s)')
CITATION = re.compile(r'\[(\d+(?:\s*,\s*\d+)*)\](?!\()')
NUMBER = re.compile(r'\d+')
CITATION_LINK = re.compile(r'<a class="(?:Citation|Reference)"'
                           r' (?:href|id)="[^"]*">([^<]*)</a>')


def linkable(m):
    """The kind of an element whose text this script may mark up, or
    None for an element Agda links or that is code."""
    kind = CLASS.search(m.group(2))
    if "href" in m.group(2) or not kind or \
       kind.group(1) not in LINKABLE_CLASSES:
        return None
    return kind.group(1)


def reference_id(n):
    return f"reference-{n}"


def link_citations(page):
    """Link the citations of a page to the entries of its references.

    Returns the new page, how many citations were linked, and the
    numbers cited that have no single entry to link to.
    """
    entries = collections.Counter()
    for m in ELEMENT.finditer(page):
        if linkable(m):
            text, _, _ = positions(m.group(3))
            entries.update(e.group(2) for e in ENTRY.finditer(text))
    taken = set(re.findall(r'\bid="([^"]*)"', page))
    single = {n for n, k in entries.items()
              if k == 1 and reference_id(n) not in taken}
    linked, missed = 0, []

    def element(m):
        nonlocal linked
        tag, attrs, body = m.group(1), m.group(2), m.group(3)
        if not linkable(m):
            return m.group(0)
        text, where, inside = positions(body)
        inserts, starts = [], set()

        def wrap(a, b, open_):
            if any(inside[a:b]) or "<" in body[where[a]:where[b - 1] + 1]:
                return False
            inserts.extend([(where[a], 1, open_),
                            (where[b - 1] + 1, 0, "</a>")])
            return True

        for e in ENTRY.finditer(text):
            starts.add(e.start(1))
            if e.group(2) in single:
                wrap(e.start(1), e.end(1), f'<a class="Reference" '
                     f'id="{reference_id(e.group(2))}">')
        for c in CITATION.finditer(text):
            if c.start() in starts:
                continue
            numbers = list(NUMBER.finditer(c.group(1)))
            for d in numbers:
                if d.group(0) not in single:
                    missed.append(d.group(0))
                    continue
                a, b = c.start(1) + d.start(), c.start(1) + d.end()
                if len(numbers) == 1:
                    a, b = c.start(), c.end()
                if wrap(a, b, f'<a class="Citation" '
                        f'href="#{reference_id(d.group(0))}">'):
                    linked += 1
        if not inserts:
            return m.group(0)
        for pos, _, mark_ in sorted(inserts, reverse=True):
            body = body[:pos] + mark_ + body[pos:]
        return f"<{SPAN}{attrs}>{body}</{SPAN}>"

    return ELEMENT.sub(element, page), linked, missed


def unlink_citations(page):
    "Take those links off, giving back the page they were put on."
    return unspan(CITATION_LINK.sub(r"\1", page))


def rewrite(htmldir, check, md, tight, dots, plus, embolden, authors,
            cite, names):
    """Rewrite every page in place.

    Returns the links in each page, the names that answer to no page, the
    links that rest on a reading rather than on a name that is exact, the
    markdown rendered, how many spaces after the universe dot are
    hidden, how many universe dots are hidden, how many spaces before
    the successor of a universe are hidden, how many names of authors
    are linked, how many citations are linked and the ones left
    unlinked, and how many pages had to be rewritten, which is none of
    them when the last run did it already. The links counted are the ones this
    script makes, an <a> with an href and nothing else, which is a shape
    Agda itself never emits.
    """
    paths = sorted(glob.glob(os.path.join(htmldir, "*.html")))
    pages = {os.path.basename(p)[:-len(".html")] for p in paths}
    tails = collections.defaultdict(set)
    for name in pages:
        tails[name.rsplit(".", 1)[-1]].add(name)

    defined = definitions(htmldir)
    found, unresolved, rewritten = {}, collections.defaultdict(list), 0
    read, rendered, tightened, hidden_dots, plussed = [], [], 0, 0, 0
    headers, marked, authored = 0, 0, 0
    cited, uncited = 0, []
    pattern = author_pattern(names)
    for path in paths:
        here = os.path.basename(path)[:-len(".html")]
        original = open(path, encoding="utf-8").read()
        page = unbold(untighten_plus(show_dots(untighten(
            unmark(unlink_authors(unlink_citations(original)))))))
        own = {name for target, name in OWN_MODULE.findall(page)
               if target in ("", os.path.basename(path))}
        new, links, missing = transform(page, pages, tails, here, own, defined)
        for name in missing:
            unresolved[name].append(here)
        if links:
            # Only markup was added, so every character the reader sees
            # must have survived untouched. This is the one check that
            # would catch a match running past the end of an element, or a
            # url losing a character to the trimming, anywhere in the
            # library at once.
            if visible(new) != visible(page):
                raise SystemExit(f"{path}: the text of the page changed; "
                                 f"nothing has been written")
            if check:
                again, more, _ = transform(new, pages, tails, here, own, defined)
                if more or again != new:
                    raise SystemExit(f"{path}: rewriting it again would "
                                     f"change it further; nothing has "
                                     f"been written")
        if md:
            linked = new
            new, done = markdown(linked, pages)
            rendered += [(here, kind, text) for kind, text in done]
            if visible(new) != visible(linked) or unmark(new) != linked:
                raise SystemExit(f"{path}: the markdown cannot be taken off "
                                 f"again exactly; nothing has been written")
        if embolden:
            plain = new
            new, one, n = bold(new, names)
            if unbold(new) != plain or visible(new) != visible(plain):
                raise SystemExit(f"{path}: the markup of the header and "
                                 f"the markers cannot be taken off again "
                                 f"exactly; nothing has been written")
            headers += one
            marked += n
        if authors and pattern:
            plain = new
            new, n = link_authors(new, names, pattern)
            if unlink_authors(new) != plain or visible(new) != visible(plain):
                raise SystemExit(f"{path}: the links on the names of the "
                                 f"authors cannot be taken off again "
                                 f"exactly; nothing has been written")
            authored += n
        if cite:
            plain = new
            new, n, missed = link_citations(new)
            if unlink_citations(new) != plain or \
               visible(new) != visible(plain):
                raise SystemExit(f"{path}: the links on the citations "
                                 f"cannot be taken off again exactly; "
                                 f"nothing has been written")
            cited += n
            uncited += [(here, k) for k in missed]
        if tight:
            # The spaces are only hidden, so the text of the page is
            # untouched here as well, and taking the markup off gives
            # back the page it was put on.
            shown = new
            new, hidden = tighten(new)
            if untighten(new) != shown or visible(new) != visible(shown):
                raise SystemExit(f"{path}: the spaces after the universe "
                                 f"dot cannot be shown again exactly; "
                                 f"nothing has been written")
            tightened += hidden
        if dots and here != NOTATION_PAGE:
            shown = new
            new, gone = hide_dots(new)
            if show_dots(new) != shown or visible(new) != visible(shown):
                raise SystemExit(f"{path}: the universe dots cannot be "
                                 f"shown again exactly; nothing has been "
                                 f"written")
            hidden_dots += gone
        if plus and here != NOTATION_PAGE:
            shown = new
            new, n = tighten_plus(new)
            if untighten_plus(new) != shown or visible(new) != visible(shown):
                raise SystemExit(f"{path}: the spaces before the successor "
                                 f"of a universe cannot be shown again "
                                 f"exactly; nothing has been written")
            plussed += n
        if new != original:
            open(path, "w", encoding="utf-8").write(new)
            rewritten += 1
        here_links = OURS.findall(new)
        if here_links:
            found[os.path.basename(path)] = here_links
        # Read back from the page itself, so that the report is the same
        # whether or not this run had anything to rewrite.
        # A link to a definition shows the identifier after its module,
        # which is taken off before the module is compared.
        read += [(here, module, shown)
                 for module, anchor, shown in TO_A_PAGE.findall(new)
                 if module in pages
                 and (shown.rsplit(".", 1)[0] if anchor
                      else SUFFIX.sub("", shown)) != module]
    return (found, unresolved, read, rendered, tightened, hidden_dots,
            plussed, cited, uncited, headers, marked, authored, rewritten)


def index_above(here, pages):
    """The index of the nearest directory above the module HERE, or the
    index of the library, or None on that index itself.

    A directory need not have an index module of its own, while seventeen
    subdirectories do have one, so the name is walked up a component at a
    time rather than guessed at in one step: there is no
    DomainTheory.Basics.index above DomainTheory.Basics.Curry, which
    therefore lands on DomainTheory.index.
    """
    parts = here.split(".")
    if parts[-1] == MAIN_INDEX:
        parts.pop()
    while len(parts) > 1:
        parts.pop()
        above = ".".join(parts) + "." + MAIN_INDEX
        if above in pages:
            return above
    return None if here == MAIN_INDEX else MAIN_INDEX


def corner_buttons(htmldir, url):
    """Put the buttons in the corner of every page, taking off whatever an
    earlier run left there.

    Returns how many pages had to be changed, which is none of them when
    the last run put the same buttons on every one.
    """
    paths = sorted(glob.glob(os.path.join(htmldir, "*.html")))
    pages = {os.path.basename(p)[:-len(".html")] for p in paths}
    href = url.replace("&", "&amp;").replace('"', "&quot;") if url else ""
    changed = 0
    for path in paths:
        here = os.path.basename(path)[:-len(".html")]
        above = index_above(here, pages)
        buttons = []
        if here != MAIN_INDEX and above != MAIN_INDEX and MAIN_INDEX in pages:
            buttons.append(BUTTON.format(href=MAIN_INDEX + ".html",
                                         title="The index of the library",
                                         glyph=GLYPH.format(shape=HOUSE)))
        if above in pages:
            buttons.append(BUTTON.format(
                href=above + ".html",
                title=("Up to the index of the library"
                       if above == MAIN_INDEX else "Up to " + above),
                glyph=GLYPH.format(shape=ARROW)))
        if href:
            buttons.append(BUTTON.format(href=href,
                                         title="Search TypeTopology",
                                         glyph=GLYPH.format(shape=GLASS)))
        corner = CORNER.format(buttons="".join(buttons)) if buttons else ""
        page = open(path, encoding="utf-8").read()
        new = CORNERS.sub("", page).replace("<body>", "<body>" + corner, 1)
        if new != page:
            open(path, "w", encoding="utf-8").write(new)
            changed += 1
    return changed


def render(agda, source, entry, htmldir, force):
    "Run agda --html, unless the rendering is there and up to date already."
    # Ask git, which knows what belongs to the library, and walk the tree
    # where there is no git, as in the container the github action runs in.
    sources = []
    try:
        listed = subprocess.run(["git", "ls-files", "*.lagda", "*.agda"],
                                cwd=source, capture_output=True, text=True)
        sources = [os.path.join(source, f) for f in listed.stdout.split()]
    except OSError:
        pass
    if not sources:
        sources = [os.path.join(root, f)
                   for root, _, here in os.walk(source)
                   for f in here if f.endswith((".lagda", ".agda"))]
    newest = max((os.path.getmtime(f) for f in sources if os.path.exists(f)),
                 default=0)
    pages = glob.glob(os.path.join(htmldir, "*.html"))
    if pages and not force and min(os.path.getmtime(p) for p in pages) > newest:
        print(f"{len(pages)} pages in {htmldir} are up to date")
        return
    print(f"{agda} --html --html-dir={htmldir} {entry}   (this takes a while)")
    try:
        proc = subprocess.Popen([agda, "--html", f"--html-dir={htmldir}", entry],
                                cwd=source, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
    except FileNotFoundError:
        raise SystemExit(f"{agda} not found; install it, or pass an existing "
                         f"rendering with --html <dir>")
    for line in proc.stdout:
        print(line, end="")
    proc.wait()
    if proc.returncode != 0:
        # A hole in a proof and a type error are equally fatal to the whole
        # rendering, and this cannot tell them apart from the exit status.
        raise SystemExit("agda did not finish: the library has holes or type "
                         "errors. Whatever was in the output directory "
                         "before has been left as it is.")


def default_css():
    """The stylesheet to use when none is given.

    This script has a copy in two places, and the stylesheet is beside it
    in TypeTopologyHTML while in the library itself it is assets/Agda.css,
    so whichever of the two is there is the one taken.
    """
    beside = os.path.join(HERE, "Agda.css")
    assets = os.path.join(os.path.dirname(HERE), "assets", "Agda.css")
    return beside if os.path.exists(beside) else assets


def stylesheet(css, htmldir):
    """Put the given stylesheet in place of the one Agda writes.

    Agda writes its own Agda.css into the output directory on every run,
    so a stylesheet of one's own has to be put back afterwards rather than
    once and for all.
    """
    if not os.path.isfile(css):
        raise SystemExit(f"{css} is not there")
    target = os.path.join(htmldir, "Agda.css")
    if os.path.isfile(target) and open(target, encoding="utf-8").read() == \
       open(css, encoding="utf-8").read():
        return
    shutil.copyfile(css, target)
    print(f"{target} replaced by {css}")


def copy(src, dst):
    "Take a rendering somewhere else as the input, without touching it."
    if os.path.abspath(src) == os.path.abspath(dst):
        # --html and --out the same directory is how a workflow that has
        # run Agda already asks for that rendering to be rewritten where
        # it stands, with nothing copied anywhere.
        print(f"rewriting {dst} in place")
        return
    pages = glob.glob(os.path.join(src, "*.html"))
    if not pages:
        raise SystemExit(f"no html pages in {src}")
    print(f"copying {len(pages)} pages from {src}")
    shutil.copytree(src, dst, dirs_exist_ok=True)


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--typetopology", default=os.path.join(os.path.dirname(HERE),
                                                          "TypeTopology"),
                   help="the TypeTopology development to render")
    p.add_argument("--source", default=None,
                   help="its source directory, if not <typetopology>/source")
    p.add_argument("--entry", default="AllModulesIndex.lagda",
                   help="the module to render, which imports all the others")
    p.add_argument("--out", default=os.path.join(HERE, "html"),
                   help="where the rendered pages go")
    p.add_argument("--html", default=None, metavar="DIR",
                   help="rewrite a copy of this existing rendering, and do "
                        "not run agda at all")
    p.add_argument("--agda", default="agda", help="the agda to run")
    p.add_argument("--css", default=default_css(),
                   help="the stylesheet to put in the rendering, replacing "
                        "the one agda writes; by default Agda.css beside "
                        "this script, or the library's assets/Agda.css, "
                        "whichever is there, and 'none' keeps Agda's own")
    p.add_argument("--search-url", default=SEARCH_URL, metavar="URL",
                   help="the search page that the magnifying glass in "
                        "the corner of every page leads to, by default the "
                        "published one, and 'none' leaves that button out")
    p.add_argument("--no-markdown", action="store_true",
                   help="leave the markdown in the prose and the comments "
                        "as plain text, taking it off pages that have it")
    p.add_argument("--list-markdown", action="store_true",
                   help="list the markdown rendered, page by page")
    p.add_argument("--no-tighten", action="store_true",
                   help="leave the space between the universe dot and a "
                        "closing bracket showing, taking the markup off "
                        "pages that have it")
    p.add_argument("--no-bold", action="store_true",
                   help="leave the header of a file and the markers of an "
                        "addition in the ordinary weight, taking the "
                        "markup off pages that have it")
    p.add_argument("--no-hide-dots", action="store_true",
                   help="leave the universe dots showing, taking the "
                        "markup off pages that have it")
    p.add_argument("--no-tighten-plus", action="store_true",
                   help="leave the space between a universe and its "
                        "successor showing, taking the markup off pages "
                        "that have it")
    p.add_argument("--no-author-links", action="store_true",
                   help="leave the name of an author in a header or a "
                        "marker as plain text, taking the links off "
                        "pages that have them")
    p.add_argument("--no-citations", action="store_true",
                   help="leave the citations [1] unlinked, taking the "
                        "links off pages that have them")
    p.add_argument("--citations", action="store_true",
                   help="list the citations left unlinked, page by page")
    p.add_argument("--force", action="store_true",
                   help="run agda even when the rendering looks up to date")
    p.add_argument("--check", action="store_true",
                   help="also check that a second run would change nothing")
    p.add_argument("--list", action="store_true",
                   help="list the links made, with how often each occurs")
    p.add_argument("--unresolved", action="store_true",
                   help="list the module references that point at no page")
    p.add_argument("--overflow", action="store_true",
                   help="list the lines that render wider than the limit, "
                        "and the lines that hidden markup leaves short in "
                        "the middle of a paragraph")
    p.add_argument("--width", type=int, default=80, metavar="N",
                   help="the limit on the width of a rendered line, "
                        "80 by default")
    p.add_argument("--guessed", action="store_true",
                   help="list the links that rest on a reading of the name, "
                        "namely a bare name, or a qualified one whose module "
                        "has moved, resolved by its last component")
    args = p.parse_args()

    source = args.source or os.path.join(args.typetopology, "source")
    root = (args.typetopology
            if os.path.isfile(os.path.join(args.typetopology, "README.md"))
            else os.path.dirname(HERE))
    out = os.path.abspath(args.out)
    os.makedirs(out, exist_ok=True)

    if args.html:
        copy(args.html, out)
    else:
        if not os.path.isdir(source):
            raise SystemExit(f"{source} is not there; say where the library "
                             f"is with --typetopology")
        render(args.agda, source, args.entry, out, args.force)

    if args.css != "none":
        stylesheet(args.css, out)

    (found, unresolved, read, rendered, tightened, hidden_dots, plussed,
     cited, uncited, headers, marked, linked, rewritten) = rewrite(
        out, args.check, not args.no_markdown, not args.no_tighten,
        not args.no_hide_dots, not args.no_tighten_plus, not args.no_bold,
        not args.no_author_links, not args.no_citations, contributors(root))
    links = [href for page in found.values() for href in page]
    pages = len(glob.glob(os.path.join(out, "*.html")))
    print(f"{len(links)} links in {len(found)} of the {pages} pages in {out}"
          + (f", {rewritten} page{'s' if rewritten != 1 else ''} rewritten"
             if rewritten else ", all of them there already"))
    if rendered:
        kinds = collections.Counter(kind for _, kind, _ in rendered)
        print(f"{len(rendered)} pieces of markdown rendered: "
              + ", ".join(f"{n} {k}" for k, n in sorted(kinds.items()))
              + ("" if args.list_markdown else "; --list-markdown lists them"))
    if tightened:
        print(f"{tightened} spaces between the universe dot and a closing "
              f"bracket hidden by the stylesheet")
    if headers or marked:
        print(f"{headers} headers and {marked} markers of an addition "
              f"put in bold")
    if linked:
        print(f"{linked} names of authors linked to their pages "
              f"in README.md")
    if hidden_dots:
        print(f"{hidden_dots} universe dots hidden by the stylesheet, "
              f"and {NOTATION_PAGE} keeps its own")
    if plussed:
        print(f"{plussed} spaces between a universe and its successor "
              f"hidden by the stylesheet")
    if cited or uncited:
        print(f"{cited} citations linked to their references, "
              f"{len(uncited)} left unlinked for want of a single entry"
              + ("" if args.citations or not uncited
                 else "; --citations lists them"))
    if args.citations:
        by_page = collections.defaultdict(list)
        for here, n in uncited:
            by_page[here].append(n)
        for here, ns in sorted(by_page.items()):
            print(f"  {here}: " + " ".join(f"[{n}]" for n in ns))
    url = None if args.search_url == "none" else args.search_url
    changed = corner_buttons(out, url)
    if changed:
        print(f"corner buttons rewritten on {changed} "
              f"page{'s' if changed != 1 else ''}")
    if read:
        print(f"{len(read)} of them are links whose text is not the module it "
              f"points to"
              + ("" if args.guessed else "; --guessed lists them"))
    if unresolved:
        n = sum(len(v) for v in unresolved.values())
        print(f"{n} names in {len(unresolved)} shapes look like module "
              f"references but point at no page"
              + ("" if args.unresolved else "; --unresolved lists them"))
    wide, short = overflow(out, args.width)
    if wide or short:
        print(f"{len(wide)} lines render wider than {args.width} characters "
              f"in {len({w[0] for w in wide})} pages, and {len(short)} are "
              f"left short by hidden markup before a continuation"
              + ("" if args.overflow else "; --overflow lists them"))

    if args.list:
        counts = collections.Counter(links)
        for href, n in sorted(counts.items()):
            print(f"{n:4}  {href}")

    if args.list_markdown:
        for here, kind, text in rendered:
            shown = (text.replace("\n", "\n" + " " * 64) if kind == "block"
                     else " ".join(text.split()))
            print(f"{kind:6}  {here:55} {shown}")

    if args.guessed:
        for page, module, shown in sorted(read):
            print(f"{shown:44} -> {module:44} in {page}")

    if args.overflow:
        for kind, rows in (("wide", wide), ("short", short)):
            for here, n, seen, source, text in rows:
                print(f"{kind:5} {here}:{n} {seen} shown, {source} in the "
                      f"source  {text.strip()[:60]}")

    if args.unresolved:
        for name in sorted(unresolved, key=lambda k: (-len(unresolved[k]), k)):
            where = collections.Counter(unresolved[name])
            pages = ", ".join(f"{p}" for p, _ in where.most_common(3))
            more = "" if len(where) <= 3 else f", and {len(where) - 3} more"
            print(f"{len(unresolved[name]):4}  {name:52} {pages}{more}")


if __name__ == "__main__":
    sys.exit(main())
