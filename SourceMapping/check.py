#!/usr/bin/env python3
"""Check release documentation identity and correspondence inventories, not mathematics.

No network access, Lean execution, pin refresh, or writes. Default mode requires a
manifest sealed against a final fold. --allow-draft is for private fixtures only.
"""
import argparse
import hashlib
import html
import json
import re
import sys
import unicodedata
from pathlib import Path

SCHEMA = "near-cubic-gates/source-map/2"
PAPER_SHA = "3bfede57ee87cb531f0623dcd29529c25d8be2c19251670f1cf7e5e5d849be88"
# Canonical JSON of all eight reviewed source entries, including exact PDF/text
# pins and release-relative paths. Removing sources must not turn INCOMPLETE into COMPLETE.
SOURCE_CATALOG_SHA = "086f2bc29ba586fd09df6282d767d6dfc053a40511ad642c2c7f5c59de1665a1"
PREFIX = "NearCubicGates.Published."
LEAVES = {
    PREFIX + x for x in (
        "Apostol.primeNumberTheorem", "Williams.RectangularProductLeaf",
        "BCGT13.BCGT13_Theorem11_1", "Shoup.FindIrrPolyAlgorithm17",
        "STV.Theorem29", "CW19Proximity.Lemma22Half", "CW19Code.Lemma26")
}
# Exact consumer producers and dependencies. Order is not mathematically relevant.
EXPECTED = {
    "normalization": ("Normalization.IntegerThreshold", "Normalization.threshold_normalization", ()),
    "restriction": ("Restriction.CentralBinomial", "Restriction.centralBinomialRestriction", ()),
    "bernstein": ("Probability.BernsteinFinite", "Probability.finiteBernstein", ()),
    "primes": ("Base.Primes", "Base.primes_of_primeNumberTheorem", ("Apostol.primeNumberTheorem",)),
    "rectangularProduct": ("Williams.Final", "Williams.Final.williams14_of_leaf", ("Williams.RectangularProductLeaf",)),
    "shortPCP": ("Assembly.Field6Ordinary", "Assembly.field6Ordinary", ("BCGT13.BCGT13_Theorem11_1", "Shoup.FindIrrPolyAlgorithm17")),
    "refuter": ("Assembly.Field7", "Assembly.field7", ()),
    "amplification": ("Amplification.Field8", "Amplification.field8", ("STV.Theorem29",)),
    "threeQueryPCPP": ("Assembly.Field9Encoder", "Assembly.field9Encoder", ("CW19Proximity.Lemma22Half", "CW19Code.Lemma26")),
}
EXPECTED_TYPES = {
    "normalization": "NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2",
    "restriction": "NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction",
    "bernstein": "NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0}",
    "primes": "NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem",
    "rectangularProduct": "NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4",
    "shortPCP": "NearCubicGates.Adapters.Assembly.OrdinaryOracleCircuitPCP",
    "refuter": "NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13",
    "amplification": "NearCubicGates.Close.CLW20_Lemma3_9_Multitape",
    "threeQueryPCPP": "NearCubicGates.PublishedSources.PCPP.PerfectThreeQueryProximityLiteral ∧ NearCubicGates.Adapters.Assembly.EfficientLinearEncoder",
}
PAGES = ["README.md", "paper/README.md", "SourceMapping/README.md", "SourceMapping/main-theorem.md"] + [
    "SourceMapping/" + x for x in (
        "1-threshold-normalization.md", "2-live-restriction.md", "3-bernstein.md",
        "4-prime-number-theorem.md", "5-rectangular-product.md", "6-short-pcp.md",
        "7-refuter.md", "8-amplification.md", "9-three-query-pcpp.md")]
CORE = {"Statement.lean", "NineInputs.lean", "MainTheorem.lean", "SourceAdapters/Assembly.lean",
        "Check.lean", "Challenge.lean", "Solution.lean", "paper/paper.tex", "CITATION.cff",
        "SourceMapping/check.py"}
LABEL = re.compile(r"`((?:lem|imp|thm|def|app|rem|sec):[^`]+)`")
LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+)\)")


class CheckError(Exception):
    pass


def need(condition, message):
    if not condition:
        raise CheckError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def within(root, name):
    p = (root / name).resolve()
    need(p.is_relative_to(root.resolve()), f"path outside release: {name}")
    return p


def unique(items, label):
    need(len(items) == len(set(items)), f"duplicate {label}")


def inventory(leaves, fields):
    unique(leaves, "leaf")
    need(set(leaves) == LEAVES, "trusted leaf inventory differs from the exact seven leaves")
    names = [r["field"] for r in fields]
    unique(names, "derived field")
    need(set(names) == set(EXPECTED), "derived field inventory differs from the exact nine fields")
    for row in fields:
        mod, decl, deps = EXPECTED[row["field"]]
        need(row["module"] == "SourceAdapters." + mod, f"producer module: {row['field']}")
        need(row["decl"] == "NearCubicGates.Adapters." + decl, f"producer declaration: {row['field']}")
        unique(row["leaves"], "producer dependency")
        need(set(row["leaves"]) == {PREFIX + s for s in deps}, f"producer dependencies: {row['field']}")
        need(row.get("joins") == [], f"open producer joins: {row['field']}")
        need(row.get("type") == EXPECTED_TYPES[row["field"]], f"canonical producer conclusion type: {row['field']}")


def links(root, pages):
    files, count = set(), 0
    for name in pages:
        text = within(root, name).read_text()
        for target in LINK.findall(text):
            if target.startswith(("https://", "http://", "mailto:")):
                continue
            rel, _, frag = target.partition("#")
            p = within(root, str(Path(name).parent / rel)) if rel else within(root, name)
            need(p.exists(), f"missing local link: {name}: {target}")
            if p.is_file():
                files.add(str(p.relative_to(root.resolve())))
            if frag:
                # Current pages deliberately use file links and named labels in prose.
                m = re.fullmatch(r"L([0-9]+)(?:-L([0-9]+))?", frag)
                need(m is not None and p.is_file(), f"unsupported local anchor: {name}: {target}")
                lo, hi = int(m[1]), int(m[2] or m[1])
                need(1 <= lo <= hi <= len(p.read_text().splitlines()), f"line anchor: {name}: {target}")
            count += 1
    return files, count


def normalize(text):
    text = unicodedata.normalize("NFKC", html.unescape(text))
    for a, b in (("−", "-"), ("–", "-"), ("’", "'"), ("“", '"'), ("”", '"')):
        text = text.replace(a, b)
    return re.sub(r"\s+", "", text)


def source_checks(root, sources, quotes, pages):
    ids = [s["id"] for s in sources]
    unique(ids, "source id")
    catalog = {s["id"]: s for s in sources}
    present, absent = [], []
    for s in sources:
        p = within(root, s["file"])
        if not p.is_file():
            absent.append(s["id"])
        else:
            need(sha(p.read_bytes()) == s["sha256"], f"source PDF identity: {s['id']}")
            present.append(s["id"])
    verified, transcription, unchecked = [], [], []
    for i, q in enumerate(quotes):
        need(q["source"] in catalog, f"unknown quoted source: {i}")
        need(q["page"] in pages, f"unlisted quote page: {i}")
        need(q["text"] in html.unescape(within(root, q["page"]).read_text()), f"quote not printed: {i}")
        need(sha(q["text"].encode()) == q["sha256"], f"quote identity: {i}")
        s = catalog[q["source"]]
        if q.get("transcribed", False):
            transcription.append(i)
            continue
        if q["source"] not in present or not s.get("text"):
            unchecked.append(i)
            continue
        p = within(root, s["text"])
        if not p.is_file():
            unchecked.append(i)
            continue
        need(sha(p.read_bytes()) == s["text_sha256"], f"source text identity: {s['id']}")
        body = p.read_text()
        # pdftotext form feeds delimit physical PDF pages. No whole-document fallback.
        chunks = body.split("\f")
        n = q["pdf_page"]
        need(isinstance(n, int) and 1 <= n <= len(chunks), f"quote PDF page: {i}")
        need(normalize(q["text"]) in normalize(chunks[n - 1]), f"quote absent from pinned page: {i}")
        verified.append(i)
    return {"source_files_verified": present, "source_files_unavailable": absent,
            "quote_indices_verified": verified, "quote_indices_transcribed_not_verified": transcription,
            "quote_indices_unchecked": unchecked,
            "source_quote_status": "COMPLETE" if not absent and not unchecked and not transcription else "INCOMPLETE"}


def check(root, manifest, allow_draft=False):
    root = root.resolve()
    m = json.loads(manifest.read_text())
    need(m["schema"] == SCHEMA, "unsupported manifest schema")
    final = m["status"] == "final-sealed"
    need(final or allow_draft, "manifest is not final-sealed")
    need(m["status"] in ("final-sealed", "private-fixture"), "invalid manifest status")
    inventory(m["trusted_leaves"], m["derived_fields"])
    catalog_bytes = json.dumps(m["published_sources"], sort_keys=True, ensure_ascii=False,
                               separators=(",", ":")).encode()
    need(sha(catalog_bytes) == SOURCE_CATALOG_SHA, "reviewed source catalog differs (IDs, PDF/text pins or paths)")
    need(set(m["pages"]) == set(PAGES) and len(m["pages"]) == len(PAGES), "page inventory")
    pins = m["pins"]
    need(str(manifest.resolve().relative_to(root)) not in pins, "manifest must not pin itself")
    required = CORE | set(PAGES) | {r["module"].replace(".", "/") + ".lean" for r in m["derived_fields"]}
    need(required <= set(pins), f"missing required pins: {sorted(required - set(pins))}")
    for name, digest in pins.items():
        p = within(root, name)
        need(p.is_file() and re.fullmatch("[0-9a-f]{64}", digest), f"missing/invalid pinned artifact: {name}")
        need(sha(p.read_bytes()) == digest, f"changed pinned artifact: {name}")
    need(pins["paper/paper.tex"] == PAPER_SHA, "paper is not the current version-3 source")
    provenance = m["provenance"]
    if final:
        need(provenance["fold_mode"] == "final", "not a final fold")
        need(provenance["open_fields"] == [], "fold has open fields")
        need(provenance["statement_sha256"] == pins["Statement.lean"], "stale final Statement pin")
        need(provenance["obligations_sha256"] == provenance["canonical_obligations_sha256"], "stale canonical obligations")
        need(provenance["registry_sha256"] == provenance["read_registry_sha256"], "stale fold registry")
    statement = within(root, "Statement.lean").read_text()
    found = re.search(r"structure PublishedInputs : Prop where\n(.*?)(?=\n(?:/--|def FinalStatement))", statement, re.S)
    need(found is not None, "PublishedInputs declaration missing")
    actual = re.findall(r"^\s+\w+\s*:\s*(NearCubicGates\.Published\.[\w.]+)\s*$", found[1], re.M)
    rows = [line.strip() for line in found[1].splitlines() if line.strip()]
    need(len(rows) == len(actual) == 7 and set(actual) == LEAVES, "actual PublishedInputs differs from manifest")
    need(re.search(r"def FinalStatement\s*:\s*Prop\s*:=\s*PublishedInputs\s*→\s*NearCubicGates.Target.MainStatement", statement), "final implication declaration missing")
    for r in m["derived_fields"]:
        p = within(root, r["module"].replace(".", "/") + ".lean")
        short = r["decl"].split(".")[-1]
        need(re.search(r"^theorem\s+" + re.escape(short) + r"\b", p.read_text(), re.M), f"producer theorem absent: {r['decl']}")
    linked, nlinks = links(root, PAGES)
    need(linked <= set(pins), f"linked files lack pins: {sorted(linked - set(pins))}")
    paper = within(root, "paper/paper.tex").read_text()
    actual_labels = {p: sorted(set(LABEL.findall(within(root, p).read_text()))) for p in PAGES}
    need(m["paper_labels"] == actual_labels, "paper label inventory differs from pages")
    labels = set(re.findall(r"\\label\{([^}]+)\}", paper))
    for page, names in actual_labels.items():
        need(set(names) <= labels, f"missing paper label: {page}: {set(names) - labels}")
    source = source_checks(root, m["published_sources"], m["quotes"], PAGES)
    return {"status": "IDENTITY_PASS" if final else "PRIVATE_FIXTURE_PASS_NOT_RELEASE",
            "scope": "Documentation identity/inventory/links only; no mathematical or kernel certification.",
            "trusted_leaves": 7, "derived_fields": 9, "pinned_artifacts": len(pins),
            "pages": len(PAGES), "local_links": nlinks, "paper_labels": sum(map(len, actual_labels.values())), **source}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--manifest", type=Path)
    ap.add_argument("--allow-draft", action="store_true")
    args = ap.parse_args()
    try:
        print(json.dumps(check(args.root, args.manifest or args.root / "SourceMapping/manifest.json", args.allow_draft), indent=2))
    except (CheckError, KeyError, ValueError, OSError, TypeError) as e:
        print(f"FAIL {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
