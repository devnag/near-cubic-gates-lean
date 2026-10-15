#!/usr/bin/env python3
"""Identity checks for this source mapping; they do not certify mathematics.

Run from the repository root:  python3 SourceMapping/check.py

Always checked:
  * the pinned files (Statement.lean, paper/paper.tex) by SHA-256;
  * every Lean and paper excerpt equals the current file lines (SHA-256) and is printed verbatim on its page;
  * every declaration of a page's closure list (manifest.json) is printed on that page;
  * every quotation of a published source is printed on its page;
  * every local link resolves, as written, to a file of this repository; line anchors lie inside the file, and a
    link to a proof declaration lands on the line that declares it;
  * no page contains a forbidden proof token.
Checked when the published sources are present in SourceMapping/pdfs/ (scripts/fetch_sources.sh downloads them and
extracts their text; they are not distributed with the repository):
  * each source file's SHA-256;
  * every quoted line occurs on the pinned page of the source's extracted text, except the lines declared as
    transcriptions of displayed formulas, which are counted separately and not verified.
"""
import hashlib
import html
import json
import re
import sys
import unicodedata
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FORBIDDEN = re.compile("|".join(["so" + "rry", "adm" + "it", "native" + "_decide", "axi" + "om", "ext" + "ern",
                                 "implemented" + "_by", "un" + "safe"]), re.I)


def fail(msg):
    print(f"FAIL {msg}")
    sys.exit(1)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def esc(text):
    return html.escape(text, quote=False)


# Some PDFs' text layers spell symbols as TeX commands (the Murray-Williams PDF writes `\geq` for ≥ and `\{ 0, 1\}`
# for {0, 1}); they are read as the symbols they print.
TEX_SYMBOLS = {"geq": "≥", "leq": "≤", "in": "∈", "ell": "ℓ", "cdot": "·", "bullet": "•", "rightarrow": "→"}


def norm(text):
    text = re.sub(r"\\(geq|leq|in|ell|cdot|bullet|rightarrow)(?![A-Za-z])|\\([{}])",
                  lambda m: TEX_SYMBOLS[m.group(1)] if m.group(1) else m.group(2), text)
    text = unicodedata.normalize("NFKC", text)
    for a, b in (("−", "-"), ("–", "-"), ("—", "-"), ("’", "'"), ("‘", "'"), ("“", '"'), ("”", '"'),
                 ("≠", "/="), ("⁄", "/"), ("…", "...")):
        text = text.replace(a, b)
    return re.sub(r"[\s^{}_]", "", text)


def pdf_page(text, number):
    pages, cur = {}, None
    for line in text.split("\n"):
        m = re.match(r"===== PDF PAGE (\d+) / \d+ =====", line)
        if m:
            cur = int(m.group(1))
            pages[cur] = []
        elif cur is not None:
            pages[cur].append(line)
    return "\n".join(pages.get(number, []))


def html_text(text):
    text = re.sub(r"<script.*?</script>|<style.*?</style>", "", text, flags=re.S)
    return html.unescape(re.sub(r"<[^>]+>", " ", text))


def inside(path):
    return path.resolve().is_relative_to(ROOT.resolve())


def main():
    manifest = json.loads((HERE / "manifest.json").read_text(encoding="utf-8"))
    for name, expected in manifest["sources"].items():
        path = ROOT / name
        if not path.is_file() or not inside(path):
            fail(f"pinned file missing: {name}")
        if sha(path.read_bytes()) != expected:
            fail(f"pinned file changed: {name}")
    pages = {p["file"]: (HERE / p["file"]).read_text(encoding="utf-8") for p in manifest["pages"]}
    readme = (HERE / "README.md").read_text(encoding="utf-8")
    for name in pages:
        if f"]({name})" not in readme:
            fail(f"README does not link {name}")
    printed = {}
    for e in manifest["excerpts"]:
        lines = (ROOT / e["source"]).read_text(encoding="utf-8").splitlines()
        body = "\n".join(lines[e["start"] - 1:e["end"]]) + "\n"
        if sha(body.encode()) != e["sha256"]:
            fail(f"stale excerpt: {e['page']}: {e['source']} {e['start']}-{e['end']}")
        if "<pre>\n" + esc(body) + "</pre>" not in pages[e["page"]]:
            fail(f"excerpt not printed: {e['page']}: {e['source']} {e['start']}-{e['end']}")
        if e["kind"] == "lean":
            printed.setdefault(e["page"], set()).add(e["declaration"])
    for p in manifest["pages"]:
        missing = [d for d in p["declarations"] if d not in printed.get(p["file"], set())]
        if missing:
            fail(f"{p['file']}: closure declarations not printed: {missing}")

    # published sources: present only after scripts/fetch_sources.sh
    sources, notes, present = manifest["published_sources"], [], {}
    for key, meta in sources.items():
        f = HERE / meta["file"]
        if not f.is_file():
            continue
        if sha(f.read_bytes()) == meta["sha256"]:
            present[key] = True
        elif meta["kind"] == "html":
            present[key] = True
            notes.append(f"{meta['file']}: a saved copy of a web page, not byte-identical to the pinned copy (such "
                         f"pages change on every request); its quotation is checked against its text")
        else:
            fail(f"source file hash: {meta['file']} is not the pinned file (SHA-256 {meta['sha256']})")
    verified = transcribed = unchecked = 0
    texts = {}
    for q in manifest["quotes"]:
        if sha(q["text"].encode()) != q["sha256"] or "<pre>\n" + esc(q["text"]) + "\n</pre>" not in pages[q["page"]]:
            fail(f"quotation not printed: {q['page']}: {q['source']} p.{q['pdf_page']}")
        meta = sources[q["source"]]
        if q["source"] not in present:
            unchecked += 1
            continue
        if q["source"] not in texts:
            t = HERE / meta["text"]
            if not t.is_file():
                fail(f"{meta['file']} is present but its extracted text {meta['text']} is not: "
                     f"run scripts/fetch_sources.sh")
            texts[q["source"]] = t.read_text(encoding="utf-8", errors="replace")
        raw = texts[q["source"]]
        hay = pdf_page(raw, q["pdf_page"]) if meta["kind"] == "pdf" else html_text(raw)
        variants = [norm(hay), norm(re.sub(r"-\s*\n\s*", "", hay))]
        for i, line in enumerate(q["text"].split("\n")):
            if line.strip() in ("", "…", "..."):
                continue
            if i in q["transcribed"]:
                transcribed += 1
                continue
            if not any(norm(line) in v for v in variants):
                fail(f"quoted line not on {meta['short']} page {q['pdf_page']}: {line!r}")
            verified += 1

    decl_links = {(d["page"], d["path"], d["line"]): d["declaration"] for d in manifest["proof_links"]}
    links, found = 0, set()
    for page in sorted(HERE.glob("*.md")):
        text = page.read_text(encoding="utf-8")
        if FORBIDDEN.search(text):
            fail(f"forbidden token in {page.name}")
        outside = re.sub(r"<pre>.*?</pre>", "", text, flags=re.S)
        for target in re.findall(r"\[[^\]]*\]\(([^)\s]+)\)", outside):
            if target.startswith(("http://", "https://")):
                continue
            rel, _, frag = target.partition("#")
            path = page if not rel else (page.parent / rel)
            if not path.is_file() or not inside(path):
                fail(f"missing or outside link: {page.name}: {target}")
            if frag:
                m = re.fullmatch(r"L(\d+)(?:-L(\d+))?", frag)
                if not m:
                    fail(f"bad anchor: {page.name}: {target}")
                lines = path.read_text(encoding="utf-8").splitlines()
                last = int(m.group(2) or m.group(1))
                if not 1 <= int(m.group(1)) <= last <= len(lines):
                    fail(f"anchor outside file: {page.name}: {target}")
                key = (page.name, str(path.resolve().relative_to(ROOT.resolve())), int(m.group(1)))
                if key in decl_links:
                    decl = decl_links[key]
                    if not re.search(rf"\b{re.escape(decl)}\b", lines[key[2] - 1]):
                        fail(f"link does not land on `{decl}`: {page.name}: {target}")
                    found.add(key)
            links += 1
    if found != set(decl_links):
        fail(f"proof declaration links in manifest.json not found on their pages: {sorted(set(decl_links) - found)}")
    print(json.dumps({
        "pages": len(pages),
        "pinned_files": len(manifest["sources"]),
        "lean_excerpts": sum(e["kind"] == "lean" for e in manifest["excerpts"]),
        "paper_excerpts": sum(e["kind"] == "paper" for e in manifest["excerpts"]),
        "local_links": links,
        "proof_declaration_links": len(found),
        "quotations": len(manifest["quotes"]),
        "published_sources_present": f"{len(present)} of {len(sources)}",
        "quoted_lines_verified_on_source_page": verified,
        "quoted_lines_transcribed_not_verified": transcribed,
        "quotations_without_their_source": unchecked,
        "notes": notes + ([] if not unchecked else
                          ["run scripts/fetch_sources.sh to check the quotations against the published sources"]),
        "status": "PASS",
        "scope": "Identity checks only; not a review of the mathematics.",
    }, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
