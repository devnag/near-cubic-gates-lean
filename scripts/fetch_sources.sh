#!/usr/bin/env bash
# Optional acquisition of the current manifest's pinned source PDFs.
# Default: local inventory only. --download enables the verified direct URLs.
# Missing/manual sources return INCOMPLETE (exit 2); wrong bytes return FAIL (exit 1).
# No text extraction, dependency installation, deletion or overwriting of existing files.
set -euo pipefail
source_script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec python3 - "$source_script_dir/.." "$@" <<'PY'
import argparse
import hashlib
import json
import sys
import urllib.request
from pathlib import Path

CATALOG_SHA = "086f2bc29ba586fd09df6282d767d6dfc053a40511ad642c2c7f5c59de1665a1"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser(description="Inspect or optionally fetch the current pinned source PDFs.")
    ap.add_argument("--root", type=Path, default=Path(sys.argv[1]))
    ap.add_argument("--download", action="store_true", help="fetch entries with verified direct URLs; manual entries remain instructions")
    args = ap.parse_args(sys.argv[2:])
    root = args.root.resolve()
    try:
        manifest = json.loads((root / "SourceMapping/manifest.json").read_text())
        if manifest["schema"] != "near-cubic-gates/source-map/2":
            raise ValueError("unsupported source-map schema")
        sources = manifest["published_sources"]
        encoded = json.dumps(sources, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode()
        if sha(encoded) != CATALOG_SHA:
            raise ValueError("source catalog differs from the reviewed eight-entry acquisition catalog")
        results, bad, missing = [], 0, 0
        for source in sources:
            rel = Path(source["file"])
            dest = (root / rel).resolve()
            if not dest.is_relative_to(root / "SourceMapping/pdfs"):
                raise ValueError("source path outside SourceMapping/pdfs")
            acquisition = source["acquisition"]
            item = {"source": source["id"], "path": str(rel), "sha256": source["sha256"],
                    "locator": acquisition["locator"]}
            if dest.exists():
                if dest.is_file() and sha(dest.read_bytes()) == source["sha256"]:
                    item["status"] = "VERIFIED"
                else:
                    item.update(status="FAIL", reason="existing bytes differ; preserved without overwrite")
                    bad += 1
            elif args.download and acquisition["method"] == "download":
                url = acquisition["url"]
                if not url.startswith("https://"):
                    raise ValueError("direct source URL must use HTTPS")
                try:
                    with urllib.request.urlopen(url, timeout=60) as response:
                        data = response.read()
                    if sha(data) != source["sha256"]:
                        raise ValueError("download does not match the pinned PDF; nothing written")
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    with dest.open("xb") as output:
                        output.write(data)
                    item.update(status="VERIFIED", url=url)
                except (OSError, ValueError) as error:
                    item.update(status="FAIL", reason=str(error))
                    bad += 1
            else:
                item.update(status="INCOMPLETE", instruction="Save the exact cited PDF at the stated path with the stated SHA-256.")
                if acquisition.get("url"):
                    item["url"] = acquisition["url"]
                if acquisition["method"] == "download":
                    item["instruction"] += " Alternatively rerun with --download."
                missing += 1
            results.append(item)
        status = "FAIL" if bad else "INCOMPLETE" if missing else "ALL_PDFS_VERIFIED"
        print(json.dumps({"status": status, "download_enabled": args.download,
                          "scope": "Pinned PDF identity only; no text extraction or quotation/mathematical certification.",
                          "verified": len(sources)-bad-missing, "unavailable": missing, "failed": bad,
                          "sources": results}, indent=2, ensure_ascii=False))
        return 1 if bad else 2 if missing else 0
    except (OSError, KeyError, ValueError, TypeError) as error:
        print(json.dumps({"status":"FAIL", "reason":str(error)}))
        return 1


sys.exit(main())
PY
