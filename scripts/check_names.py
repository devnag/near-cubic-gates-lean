#!/usr/bin/env python3
r"""check_names.py -- whole-token scan of a directory tree for banned names.

  python3 scripts/check_names.py PATH ...            # exit 1 and list every hit
  python3 scripts/check_names.py --add WORD          # add a word to scripts/banned-names.sha256

The list stores SHA-256 digests of lower-case words (multi-word entries joined by '-'), one per line, so the
list itself names nothing. Every text and every file/directory name is cut into maximal ASCII alphanumeric
runs; a run is checked whole and after splitting at camelCase and letter/digit boundaries, and runs of two or
three consecutive tokens are checked for multi-word entries. Matching is case-insensitive and whole-token:
a banned word inside a longer ordinary word is not a hit. Every hit is reviewed by a person; nothing is
replaced automatically.

One section is exempt: the AI methodology statement of the paper's source, paper/paper.tex, which names the
tools used, as the disclosure requires. It runs from the line `\section*{AI methodology statement}` to the line
before the next `\section`, `\appendix`, `\begin{thebibliography}`, `\bibliography{` or `\end{document}`. Hits
inside it are not reported; the rest of the file, and every other file, is scanned in full.
"""
import hashlib, re, sys
from pathlib import Path

RUN = re.compile(r'[A-Za-z0-9]+')
CAMEL = re.compile(r'[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|[0-9]+')


EXEMPT_SECTION = ('paper/paper.tex', '\\section*{AI methodology statement}')
SECTION_END = re.compile(r'^\\(section|appendix|begin\{thebibliography\}|bibliography\{|end\{document\})', re.M)


def exempt_span(f, root, text):
    """The (start, end) character span of the exempt section if f is paper/paper.tex, else None."""
    if not f.resolve().as_posix().endswith('/' + EXEMPT_SECTION[0]):
        return None
    a = text.find('\n' + EXEMPT_SECTION[1])
    if a < 0:
        return None
    a += 1
    m = SECTION_END.search(text, a + len(EXEMPT_SECTION[1]))
    return (a, m.start() if m else len(text))


def H(w):
    return hashlib.sha256(w.lower().encode()).hexdigest()


def load_ban(path):
    path = Path(path) if path else Path(__file__).with_name('banned-names.sha256')
    return {l.split()[0] for l in path.read_text().splitlines() if l.strip() and not l.startswith('#')}


def hits_in(text, hashes):
    runs = [(m.start(), m.group(0)) for m in RUN.finditer(text)]
    for off, run in runs:
        cand = {run.lower()} | {t.lower() for t in CAMEL.findall(run)}
        for w in cand:
            if H(w) in hashes:
                yield off, w, run
    low = [(o, r.lower()) for o, r in runs]
    for k in (2, 3):                        # multi-word entries, e.g. two consecutive tokens
        for i in range(len(low) - k + 1):
            w = '-'.join(t for _, t in low[i:i + k])
            if H(w) in hashes:
                yield low[i][0], w, text[low[i][0]:low[i + k - 1][0] + len(low[i + k - 1][1])]


def scan_file(p, hashes, out, root=Path('.')):
    n = 0
    for _, w, run in hits_in(str(p), hashes):
        out.append(f'{p}:0:0: banned token {w!r} in path component {run!r}'); n += 1
    try:
        text = p.read_text(errors='replace')
    except (IsADirectoryError, OSError):
        return n
    starts = [0] + [i + 1 for i, c in enumerate(text) if c == '\n']
    import bisect
    span = exempt_span(p, root, text)
    for off, w, run in hits_in(text, hashes):
        if span and span[0] <= off < span[1]:
            continue
        ln = bisect.bisect_right(starts, off)
        col = off - starts[ln - 1]
        line = text[starts[ln - 1]:text.find('\n', off) if text.find('\n', off) >= 0 else len(text)]
        out.append(f'{p}:{ln}:{col}: banned token {w!r} in {run!r} | {line.strip()[:120]}'); n += 1
    return n


def main(argv):
    ban = None
    if '--banlist' in argv:
        i = argv.index('--banlist'); ban = argv[i + 1]; del argv[i:i + 2]
    if '--add' in argv:
        i = argv.index('--add'); w = argv[i + 1]
        p = Path(ban) if ban else Path(__file__).with_name('banned-names.sha256')
        with open(p, 'a') as f:
            f.write(H(w) + '\n')
        print(f'added one entry to {p}')
        return 0
    files = []                              # (file, root it was found under)
    if '--list-of-files' in argv:
        i = argv.index('--list-of-files')
        files = [(Path(l), Path('.')) for l in Path(argv[i + 1]).read_text().split('\n') if l]
        del argv[i:i + 2]
    for a in argv:
        p = Path(a)
        if p.is_dir():
            files += [(q, p) for q in p.rglob('*') if not ({'.lake', '.git', '.comparator', 'pdfs'} & set(q.parts))
                      and (q.is_file() or q.is_dir())]
        else:
            files.append((p, Path('.')))
    hashes = load_ban(ban)
    out = []
    for f, root in files:
        if f.name == 'banned-names.sha256':
            continue
        if f.is_dir():                      # directory names are scanned too
            for _, w, run in hits_in(str(f.relative_to(root)) if root in f.parents else str(f), hashes):
                out.append(f'{f}:0:0: banned token {w!r} in directory name {run!r}')
            continue
        scan_file(f, hashes, out, root)
    print('\n'.join(out))
    print(f'check_names: {len(files)} files, {len(out)} hits', file=sys.stderr)
    return 1 if out else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
