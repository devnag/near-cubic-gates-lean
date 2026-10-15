#!/usr/bin/env bash
# Download the published sources quoted by SourceMapping/, check their SHA-256, and extract the text of each PDF
# page, so that `python3 SourceMapping/check.py` also checks every quotation against its source.
# Usage, from the repository root:  scripts/fetch_sources.sh
# Writes only SourceMapping/pdfs/ (git-ignored; the sources are not redistributed). Needs curl and Python 3.
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
DIR="$ROOT/SourceMapping/pdfs"
mkdir -p "$DIR/text"
printf '*\n' > "$DIR/.gitignore"

sha256() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi; }

# file|kind|sha256|url|how
SOURCES="
apostol76-chapter4-abstract.html|html|d869deff87446022e1d30e28d3c5b065e9c814d33b303ae7a1c16274aac6c052|https://link.springer.com/chapter/10.1007/978-1-4757-5579-4_5|manual
bv14.pdf|pdf|5e2dba9087704b01e238477b815d9871dc9462f319fc9ddd4f463c5590386d71|https://eccc.weizmann.ac.il/report/2014/017/download/|auto
clw20.pdf|pdf|d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c|https://eccc.weizmann.ac.il/report/2020/150/download/|auto
ctw26.pdf|pdf|b461919916161705a41f43866538d954bd100ca1d4c89451ba734d1caff9987d|https://eccc.weizmann.ac.il/report/2026/039/download/|auto
cw19.pdf|pdf|c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533|https://drops.dagstuhl.de/storage/00lipics/lipics-vol137-ccc2019/LIPIcs.CCC.2019.19/LIPIcs.CCC.2019.19.pdf|auto
mw20-sicomp.pdf|pdf|b633f81dc40dc20ca011cdedf29bb43b290fa2ed678bd6628d84646267ca2fec|https://dspace.mit.edu/server/api/core/bitstreams/fd66c806-f889-483b-ba4c-9ee9e99e2228/content|auto
vershynin-first-edition.pdf|pdf|681b6f3d947f71c023f3d1090e7aa33fd7e302647a6dfb6e69bd272363b6f462|https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf|auto
wilacc14-jacm.pdf|pdf|78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c|https://dl.acm.org/doi/pdf/10.1145/2559903|manual
"
PYPDF_WHL=pypdf-6.19.0-py3-none-any.whl
PYPDF_SHA=7e5d6e730e7dae87d560a2cee218b852f6498c8be61966f3cd02ead971e48d14
PYPDF_URL=https://files.pythonhosted.org/packages/3c/2c/c43c03eaf630435f023f1dc61ec4a4a78951ad5530a62c71cc89bde307b7/pypdf-6.19.0-py3-none-any.whl

manual_note() {
  case "$1" in
  apostol76-chapter4-abstract.html) echo "        the publisher's page answers scripted requests with a JavaScript check; open it in a browser and save the page (HTML) under this name. Web pages change on every request, so check.py does not require the pinned bytes here; it checks the quotation on the saved page's text." ;;
  wilacc14-jacm.pdf) echo "        the publisher's site (ACM Digital Library) refuses scripted downloads; open the link in a browser (access may require a subscription) and save the PDF under this name." ;;
  esac
}

failed=0; missing=0
while IFS='|' read -r file kind want url how; do
  [ -n "$file" ] || continue
  if [ -f "$DIR/$file" ] && { [ "$(sha256 "$DIR/$file")" = "$want" ] || [ "$kind" = html ]; }; then
    echo "ok      $file (present)"; continue
  fi
  if curl -fsSL --retry 2 -o "$DIR/$file.part" "$url" 2>/dev/null && [ "$(sha256 "$DIR/$file.part")" = "$want" ]; then
    mv "$DIR/$file.part" "$DIR/$file"; echo "ok      $file"
  else
    rm -f "$DIR/$file.part"
    if [ "$how" = manual ]; then
      echo "MANUAL  $file: save $url as SourceMapping/pdfs/$file (SHA-256 $want)"
      manual_note "$file"; missing=$((missing + 1))
    else
      echo "FAIL    $file: $url did not serve the pinned file (SHA-256 $want)"; failed=$((failed + 1))
    fi
  fi
done <<< "$SOURCES"

# pypdf 6.19.0 from PyPI (pinned), unpacked locally; it is used only to extract the PDF text.
if [ ! -d "$DIR/pypdf-lib/pypdf" ]; then
  if curl -fsSL --retry 2 -o "$DIR/$PYPDF_WHL" "$PYPDF_URL" && [ "$(sha256 "$DIR/$PYPDF_WHL")" = "$PYPDF_SHA" ]; then
    python3 -I -m zipfile -e "$DIR/$PYPDF_WHL" "$DIR/pypdf-lib"
  else
    echo "FAIL    pypdf 6.19.0: $PYPDF_URL did not serve the pinned wheel"; exit 1
  fi
fi
while IFS='|' read -r file kind want url how; do
  [ "$kind" = pdf ] && [ -f "$DIR/$file" ] || continue
  out="$DIR/text/${file%.pdf}.txt"
  [ -s "$out" ] && continue
  python3 -I - "$DIR/pypdf-lib" "$DIR/$file" "$out" <<'PY' || { echo "FAIL    text of $file"; failed=$((failed + 1)); }
import logging, sys
sys.path.insert(0, sys.argv[1])
import pypdf
logging.getLogger("pypdf").setLevel(logging.ERROR)
reader = pypdf.PdfReader(sys.argv[2])
n = len(reader.pages)
with open(sys.argv[3], "w", encoding="utf-8") as out:
    for i, page in enumerate(reader.pages, 1):
        try:
            text = page.extract_text() or ""
        except Exception as error:
            text = f"<<EXTRACT ERROR {error}>>"
        out.write(f"\n\n===== PDF PAGE {i} / {n} =====\n")
        out.write(text)
PY
  [ -s "$out" ] && echo "text    ${out#$ROOT/}"
done <<< "$SOURCES"

echo "$failed failed, $missing to save by hand; now run: python3 SourceMapping/check.py"
[ "$failed" -eq 0 ]
