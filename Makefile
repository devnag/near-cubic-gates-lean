# `make` downloads the prebuilt Mathlib, builds the proof, and checks it (a few hours).
.PHONY: all build check comparator names sourcemap kernel-replay clean
all: check

build:
	lake exe cache get
	lake build

check: build
	lake env lean Check.lean

# ---- optional ---------------------------------------------------------------------------------------------
comparator:            ## comparator check, tools included (README); run it in a fresh clone, so the proof is built only in its sandbox
	bash scripts/comparator.sh

names:                 ## the naming check used by CI
	python3 scripts/check_names.py .

sourcemap:             ## download the cited papers (not shipped here) and run the SourceMapping check
	bash scripts/fetch_sources.sh && python3 SourceMapping/check.py

kernel-replay: build   ## re-check every module's declarations with leanchecker (slow)
	find StatementChecks Proof Bindings -name '*.lean' | sed 's|/|.|g; s|\.lean$$||' | \
	  xargs -P $$(nproc) -I{} lake env leanchecker {}
	lake env leanchecker Statement
	lake env leanchecker StatementSupport
	lake env leanchecker MainTheorem

clean:                 ## remove the build (the downloaded Mathlib and the comparator tools in .comparator/ stay)
	rm -rf .lake/build
