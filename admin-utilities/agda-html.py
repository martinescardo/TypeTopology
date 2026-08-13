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

A module reference is linked only when a page of that name is there to
link to, so a name that points at nothing is left as it is, and reported
by --unresolved. Those are worth reading: most are references that went
stale when a module was renamed. Email addresses are deliberately left
alone.

The pages look exactly as they did. Agda's own stylesheet already gives
every link no underline and a green background under the cursor, which is
what an identifier in the code does, so the stylesheet is left alone too.
"""

import argparse, collections, glob, os, re, shutil, subprocess, sys

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

TO_A_PAGE = re.compile(r'<a href="([^"]*)\.html">([^<]*)</a>')

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
    """
    candidates = tails.get(name.rsplit(".", 1)[-1], set())
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
    part is linked and the rest of the name left outside the link. Failing
    both, its last component is tried, which is what lets a reference
    survive its module moving to another directory, and what resolves a
    file name written without its directory.

    Returns the href, the length of the text to link, and how it was
    resolved, or None when no page of the library answers to the name.
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
    return None


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


def linkify(text, pages, tails, here, own):
    """Link everything linkable in one stretch of escaped text.

    Returns the text, the links made, each with how it was resolved, and
    the names that look like references and answer to nothing.
    """
    out, pos, links, unresolved = [], 0, [], []
    for m in LINKABLE.finditer(text):
        name, start = m.group(0), m.start()
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


def transform(page, pages, tails, here, own):
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
            done, made, missing = linkify(gap, pages, tails, here, own)
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


def rewrite(htmldir, check):
    """Rewrite every page in place.

    Returns the links in each page, the names that answer to no page, the
    links that rest on a reading rather than on a name that is exact, and
    how many pages had to be rewritten, which is none of them when the
    last run did it already. The links counted are the ones this script
    makes, an <a> with an href and nothing else, which is a shape Agda
    itself never emits.
    """
    paths = sorted(glob.glob(os.path.join(htmldir, "*.html")))
    pages = {os.path.basename(p)[:-len(".html")] for p in paths}
    tails = collections.defaultdict(set)
    for name in pages:
        tails[name.rsplit(".", 1)[-1]].add(name)

    found, unresolved, rewritten = {}, collections.defaultdict(list), 0
    read = []
    for path in paths:
        here = os.path.basename(path)[:-len(".html")]
        page = open(path, encoding="utf-8").read()
        own = {name for target, name in OWN_MODULE.findall(page)
               if target in ("", os.path.basename(path))}
        new, links, missing = transform(page, pages, tails, here, own)
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
                again, more, _ = transform(new, pages, tails, here, own)
                if more or again != new:
                    raise SystemExit(f"{path}: rewriting it again would "
                                     f"change it further; nothing has "
                                     f"been written")
            open(path, "w", encoding="utf-8").write(new)
            rewritten += 1
        here_links = OURS.findall(new)
        if here_links:
            found[os.path.basename(path)] = here_links
        # Read back from the page itself, so that the report is the same
        # whether or not this run had anything to rewrite.
        read += [(here, module, shown)
                 for module, shown in TO_A_PAGE.findall(new)
                 if module in pages and SUFFIX.sub("", shown) != module]
    return found, unresolved, read, rewritten


def render(agda, source, entry, htmldir, force):
    "Run agda --html, unless the rendering is there and up to date already."
    sources = subprocess.run(["git", "ls-files", "*.lagda", "*.agda"],
                             cwd=source, capture_output=True,
                             text=True).stdout.split()
    newest = max((os.path.getmtime(os.path.join(source, f)) for f in sources),
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
    p.add_argument("--css", default=os.path.join(HERE, "Agda.css"),
                   help="the stylesheet to put in the rendering, replacing "
                        "the one agda writes; by default Agda.css beside "
                        "this script, and 'none' keeps Agda's own")
    p.add_argument("--force", action="store_true",
                   help="run agda even when the rendering looks up to date")
    p.add_argument("--check", action="store_true",
                   help="also check that a second run would change nothing")
    p.add_argument("--list", action="store_true",
                   help="list the links made, with how often each occurs")
    p.add_argument("--unresolved", action="store_true",
                   help="list the module references that point at no page")
    p.add_argument("--guessed", action="store_true",
                   help="list the links that rest on a reading of the name, "
                        "namely a bare name, or a qualified one whose module "
                        "has moved, resolved by its last component")
    args = p.parse_args()

    source = args.source or os.path.join(args.typetopology, "source")
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

    found, unresolved, read, rewritten = rewrite(out, args.check)
    links = [href for page in found.values() for href in page]
    pages = len(glob.glob(os.path.join(out, "*.html")))
    print(f"{len(links)} links in {len(found)} of the {pages} pages in {out}"
          + (f", {rewritten} page{'s' if rewritten != 1 else ''} rewritten"
             if rewritten else ", all of them there already"))
    if read:
        print(f"{len(read)} of them are links whose text is not the module it "
              f"points to"
              + ("" if args.guessed else "; --guessed lists them"))
    if unresolved:
        n = sum(len(v) for v in unresolved.values())
        print(f"{n} names in {len(unresolved)} shapes look like module "
              f"references but point at no page"
              + ("" if args.unresolved else "; --unresolved lists them"))

    if args.list:
        counts = collections.Counter(links)
        for href, n in sorted(counts.items()):
            print(f"{n:4}  {href}")

    if args.guessed:
        for page, module, shown in sorted(read):
            print(f"{shown:44} -> {module:44} in {page}")

    if args.unresolved:
        for name in sorted(unresolved, key=lambda k: (-len(unresolved[k]), k)):
            where = collections.Counter(unresolved[name])
            pages = ", ".join(f"{p}" for p, _ in where.most_common(3))
            more = "" if len(where) <= 3 else f", and {len(where) - 3} more"
            print(f"{len(unresolved[name]):4}  {name:52} {pages}{more}")


if __name__ == "__main__":
    sys.exit(main())
