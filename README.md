# Near-cubic gate lower bounds for SYM∘THR circuits: a Lean proof of the main theorem

This repository contains a complete Lean 4 proof of the main theorem of "Almost-Everywhere Near-Cubic Gate Lower
Bounds for SYM∘THR Circuits" (Dev Nag), from nine published results that it assumes as hypotheses (listed below). [`paper/paper.tex`](paper/paper.tex) is version 2 (October 15, 2026), the
version this proof was checked against. The main theorem (`thm:main`, Theorem 1.2 of the typeset paper;
paper/paper.tex, lines 220–233) reads:

> There is a rational constant 0 < γ < 1 such that, for every fixed 0 < d < γ/5, there are a positive integer K_d
> and a language F_d ∈ E^NP with the following property. For every sufficiently large n and every C ∈ 𝒲,
> W(C) ≤ ⌊n³/(K_d λ_n^{21/4} μ_n^7)⌋ ⟹ agr(C, F_d) < 1 − d.

Here 𝒲 is the paper's class of weighted symmetric threshold circuits (lines 184–197): C(x) = f(Σ_i w_i g_i(x)),
where each g_i is a threshold gate with arbitrary real weights and threshold, each w_i is a nonzero integer, and
f : ℤ → {0, 1} is an arbitrary lookup. W(C) = Σ_i |w_i| is the top weight; when every |w_i| = 1 it is the number of
bottom gates. λ_n = ⌈log₂ n⌉, μ_n = ⌈log₂ λ_n⌉, and agr(C, F) is the fraction of inputs x ∈ {0, 1}^n on which
C(x) = F_n(x). In words: below a near-cubic budget, every such circuit, whatever its symmetric output lookup, is
wrong on more than a d fraction of the inputs, at every large input length. As the paper says (lines 241–245), γ is
a rational lower bound on the rejection gap of a published PCP of proximity (input 9 below), small and not optimized.

The proof assumes nine published inputs. Each is written in Lean as a transcription of the published statement, and
Lean checks: those nine inputs ⇒ the main theorem, using only Lean's three standard axioms.

## Verify it

1. Install Lean (Linux or macOS, one line):

   ```
   curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none && . ~/.elan/env
   ```

2. In this directory run `make`. It downloads prebuilt Mathlib, builds the proof (7,651 Lean modules,
   about 1.3 million lines) and runs `Check.lean`. On a 90-core machine it took 2 h 41 min to 2 h 48 min. It needs
   about 60 GB of disk; the measured memory peak was 67 GB to 93 GB, page cache included.
3. For the strongest check, run `make comparator` (Linux only) in a fresh clone of this repository. This one command
   installs the pinned comparator tools in user space (no administrator rights; the versions are set in
   `scripts/comparator.sh`) and runs [comparator](https://github.com/leanprover/comparator): it builds the proof
   inside a sandbox, checks that `Solution.lean` proves exactly the statement of `Challenge.lean`, which depends on
   `Statement.lean` and Mathlib alone, checks the axioms, and replays the proof through Lean's kernel. In a fresh
   clone it took 4 h 31 min on a 90-core machine, with a measured memory peak of 66 GB (page cache included). Use a
   fresh clone: if `make` has already built the proof in the same directory, `make comparator` refuses to run,
   because the proof must be built only inside the sandbox (the script refuses whenever compiled proof files are
   already present). Comparator's sandbox (landrun) confines the build's file system access and, on Linux 6.7 or
   later, its TCP network access; the script also runs it under `systemd-run --user` with
   `RestrictAddressFamilies=~AF_UNIX`, which blocks Unix-domain sockets. Without a user D-Bus session it uses a
   detached systemd user unit, and without systemd it runs comparator directly and says so.
4. While it runs, check the pages in [`SourceMapping/`](SourceMapping/): one page for each of the nine inputs and one
   for the main theorem. Each puts the published statement beside the Lean definition that must say the same thing,
   with a short list of what to check.

## Reading the output

`make` ends with the output of `Check.lean`: (a) the statement written out in Lean: `FinalStatement`,
`NearCubicGates.Target.MainStatement` and the definitions of its conclusion, (b) `NineInputs`, whose nine fields are
the hypotheses, (c) the type of the main theorem `NearCubicGates.Close.main_from_inputs`, which is `FinalStatement`:
the nine inputs imply `MainStatement`, (d) its axioms, which must be exactly `[propext, Classical.choice, Quot.sound]`
(an unfinished proof would show `sorryAx`), and (e) one `assumes ...` line per input, then `PASS` or `FAIL`. `PASS`
means the theorem has exactly this type, the inputs are exactly the nine listed below in this order, and it depends
on no other axioms. `Check.lean` reads the compiled files that `make` built; it does not replay the proof through
the kernel. Comparator does, as does `make kernel-replay`.

`make comparator` reports `VERDICT: PASS (…). comparator: Your solution is okay!` (the parentheses say how
comparator was launched) and exits with status 0. The theorem in `Solution.lean` then

1. proves the same statement as in `Challenge.lean`;
2. uses no axioms beyond `propext`, `Quot.sound` and `Classical.choice`;
3. is accepted by the Lean kernel.

## What is assumed

`FinalStatement`, the last definition of `Statement.lean`, is `NineInputs → MainStatement`. `NineInputs` has one
field per published input (the table gives the last component of each Lean name; the full names are in the last
section of `Statement.lean`):

| # | Field of `NineInputs` | Lean statement | Published result | In the paper (paper/paper.tex) | Page |
|---|---|---|---|---|---|
| 1 | `normalization` | `CTW26_Lemma3_2` | Chen, Tal, Wang (ECCC TR26-039) Lemma 3.2, after Muroga, Toda, Takasu (1961): integer weights for threshold gates | `lem:integer`, lines 1069–1077 | [1](SourceMapping/1-threshold-normalization.md) |
| 2 | `restriction` | `CTW26_AppendixA3_CentralBinomialRestriction` | Chen, Tal, Wang Lemma 4.1, the counting bound of its proof in Appendix A.3: live gates under random restrictions | `lem:live`, lines 1087–1103 | [2](SourceMapping/2-live-restriction.md) |
| 3 | `bernstein` | `Vershynin18_Theorem2_8_4_FiniteBernstein` | Vershynin, *High-Dimensional Probability* (2018) Theorem 2.8.4 with K = 1: Bernstein's inequality | `lem:bernstein`, lines 1105–1115 | [3](SourceMapping/3-bernstein.md) |
| 4 | `primes` | `ApostolPrimeNumberTheorem` | Apostol, *Introduction to Analytic Number Theory* (1976) Chapters 4 and 13: the prime number theorem | `lem:primes`, lines 1281–1295 | [4](SourceMapping/4-prime-number-theorem.md) |
| 5 | `rectangularProduct` | `Williams14_Corollary4_4` | Williams (J. ACM 2014) Corollary 4.4 = C.2: rectangular matrix product on one multitape machine | `imp:batch`, lines 1530–1539 | [5](SourceMapping/5-rectangular-product.md) |
| 6 | `shortPCP` | `MW20_OracleCircuitPCP_TM2` | Murray, Williams (SIAM J. Comput. 2020) Section 5, in the proof of Theorem 1.4, after Ben-Sasson, Viola: short PCP as an oracle circuit | `imp:short-pcp`, lines 2185–2229 | [6](SourceMapping/6-short-pcp.md) |
| 7 | `refuter` | `CLW20_Theorem1_13` | Chen, Lyu, Williams (ECCC TR20-150) Theorem 1.13: refuter with an NP oracle, read for multitape machines | `imp:ae-refuter`, lines 2304–2329; multitape reading, `lem:multitape-refuter`, lines 4835–4841 | [7](SourceMapping/7-refuter.md) |
| 8 | `amplification` | `CLW20_Lemma3_9_Multitape` | Chen, Lyu, Williams Lemma 3.9, after Sudan, Trevisan, Vadhan Theorem 24: hardness amplification | `imp:ae-amplification`, lines 2331–2349 | [8](SourceMapping/8-amplification.md) |
| 9 | `threeQueryPCPP` | `ThreeQuerySourceGroup` | Chen, Williams (CCC 2019) Lemma 24 (perfectly complete three-query PCP of proximity) and Lemma 27 (linear code) | `imp:three-pcpp`, lines 2381–2415 | [9](SourceMapping/9-three-query-pcpp.md) |

Input 9 is one field with two published constituents: `ThreeQuerySourceGroup` is the conjunction of CW19 Lemma 24 and
CW19 Lemma 27. The nine inputs are therefore ten published assertions. The pointwise form the paper uses
(lines 2398–2415) is proved in Lean from the two.

Each input is defined in `Statement.lean`. Its page in `SourceMapping/` puts the published statement, pinned to its
PDF page, beside the Lean text and lists every reading (quantifier order, rounding, machine model) and any documented
deviation. The conclusion `MainStatement` is compared with the paper on
[`SourceMapping/main-theorem.md`](SourceMapping/main-theorem.md). The paper's own table of published inputs
(`app:sources`, lines 4721–4810) lists further results it cites. The Lean theorem assumes none of them: every result
it needs beyond the nine inputs is proved in Lean. For example the two-query PCPP of `imp:pcpp` (CLW20 Lemma 3.11) is
used only for the paper's periodic theorem and is not an input here.

## What to read

Read `Statement.lean`, `Challenge.lean` and `SourceMapping/`.

- `Statement.lean` (1,592 lines) is the whole trusted statement and imports Mathlib only. Part I
  (sections 1 to 23) is the machine model, the codecs, inputs 1, 5 and 7, and the amplifier of input 8; Part II
  (sections 24 to 30) is the main theorem's statement (section 25, `NearCubicGates.Target.MainStatement`), inputs 2,
  3, 4, 6 and 9, the definition of input 8, and `NineInputs` and `FinalStatement` (section 30).
- `Challenge.lean` states `FinalStatement` from `Statement.lean` and Mathlib alone. Its proof is a deliberate
  `sorry`, the only one in the repository: it is the statement comparator checks the proof against. `Solution.lean`
  proves the same statement with the main theorem, and `comparator.json` names that theorem and the permitted axioms.
- `MainTheorem.lean` holds the main theorem, `NearCubicGates.Close.main_from_inputs : NearCubicGates.Close.FinalStatement`.
- `StatementChecks/` proves facts about the trusted statement itself, for a skeptical reader: the integer budget is
  exactly the paper's floor bound for n ≥ 4 (`MainBudget.lean`); every ordinary SYM∘THR circuit with G gates is in the
  class with W = G (`CircuitClass.lean`); the statement is neither trivially true nor trivially false
  (`Nontrivial.lean`); and an E^NP certificate determines its language (`ENPDeterminism.lean`).
- `Bindings/` and `Proof/` are checked by Lean; you need not read them. `StatementSupport.lean` holds
  declarations that the proof needs and the statement does not; it imports `Statement.lean` and is not trusted.

Comparator's trusted import closure is `Statement` plus Mathlib. You also trust `lakefile.toml`, the sandbox and the
kernel.

## Caveats

- The comparator certifies exactly the main theorem, as an implication from the nine inputs (`FinalStatement`). The
  paper's other results, including the periodic-top theorem (`thm:periodic`, lines 306–324) and its refinements, are
  not formalized here.
- The published inputs are assumed, not proved here. Each is a transcription of a published statement under the
  encoding and machine-model readings documented on its `SourceMapping/` page; Lean cannot check that a transcription
  is faithful, and the pages are there so that a reader can. If an input as transcribed were false, `FinalStatement`
  would hold vacuously, and neither `Check.lean` nor comparator could detect it. The main interpretive step is the
  machine model. Inputs 5 and 7 are read for multitape Turing machines: Williams states input 5 for them, and the
  paper's Appendix C (`lem:multitape-refuter`) derives the refuter's multitape reading from its published proof.
  Input 6 is applied only to multitape verifiers, which restricts its hypothesis. The clocks of inputs 7 and 8 use
  the standard multitape notion of time-constructibility. Each page of [`SourceMapping/`](SourceMapping/) shows the
  published statement next to its Lean form, and "For skeptics" below lists every such reading.
- Docstrings say "Tier 1" for the proof's own multitape machine model (section 7 of `Statement.lean`, with the
  programs, word functions and verifiers of section 9) and "Tier 2" for Mathlib's `Turing.TM2` model. Constructions
  that inputs 6, 8 and 9 promise are stated in Tier 2; Williams's multiplication and the refuter (inputs 5 and 7)
  are stated in Tier 1, the multitape reading of the previous item.
- Input 4, the prime number theorem, is cited from Apostol's book. Its page quotes the publisher's abstract of
  Chapter 4, which states the limit; the book's own text was not checked.
- E^NP is deterministic 2^O(n) time with an NP oracle, stated as an explicit execution certificate (`InENP`). The
  budget is stated without real division, as (K·W·μ_n^7)^4·λ_n^21 ≤ n^12, which for n ≥ 4 is the paper's
  W ≤ ⌊n³/(K λ_n^{21/4} μ_n^7)⌋ (`MainBudget`; see [`SourceMapping/main-theorem.md`](SourceMapping/main-theorem.md)).
- Names such as the `NearCubicWires`, `RepairSource`, `RepairOrdinary` and `RepairRepresentation` namespaces, the
  `Proof/Wire_3_5` directory and module names such as `...Dock`, `...Handoff` or `...Closeout` come from code shared
  with the author's earlier Lean proofs; all of that code is included here, and the names carry no meaning beyond
  being names. So does `NearCubicGates.Close.Release.main_theorem`, the name comparator checks.
- Comments in that shared code refer to the earlier papers: a citation such as `paper.tex:400`, "Paper A.8" or
  "Appendix C.10" in `Proof/` outside `Proof/Gates/` is to the paper of the near-cubic wires proof
  ([github.com/devnag/near-cubic-wires](https://github.com/devnag/near-cubic-wires)), and in `Proof/Wire_3_5/` to the
  paper of [github.com/devnag/wire_three_five](https://github.com/devnag/wire_three_five); they are not line numbers
  of `paper/paper.tex`.
- One module, `Proof/Gates/GateRecovery/Aliases.lean`, uses a metaprogram (`run_cmd`) to add declaration aliases; it
  adds no axioms and no new statements.
- `make` uses prebuilt Mathlib binaries. To avoid them, remove `lake exe cache get` from the Makefile; Mathlib then
  builds from source, adding several hours.
- The one-command comparator check is Linux only. On macOS, `make` still builds the proof and runs `Check.lean`.

## For skeptics

This section is for a reader who expects the result to be wrong. It lists what you must take on trust, the quickest
order in which to check everything else, and every step at which a published statement enters Lean in a form other
than the printed one.

### What you must trust

Lean proves `FinalStatement`: the nine inputs imply `MainStatement`. For that claim, the trusted surface is:

1. **`Statement.lean`**, the whole statement; it imports Mathlib only. What matters most:
   - section 25, `NearCubicGates.Target.MainStatement`, and the definitions it uses (the threshold gate of section 4;
     the machine model, oracle programs and NP verifiers behind `InENP`, sections 7, 9, 10 and 14). This is the claim.
   - section 30: `NineInputs`, whose nine fields are the only hypotheses, and
     `FinalStatement := NineInputs → MainStatement`.
   - the definition of each input: 1 in section 18; 2 and 3 in section 27 (with `mean`, section 24); 4 in section 26;
     5 in section 23; 6 in section 29; 7 in section 22; 8 in sections 19, 21 and 30; 9 in sections 20 and 28. The
     machines of inputs 5 and 7, the verifier in the hypothesis of input 6, the clocks of inputs 7 and 8 (one
     definition, `TimeConstructible`, in section 22) and the machines of `InENP` are multitape machines of section 7.
     The algorithms that inputs 6, 8 and 9 promise are machines of Mathlib's `Turing.TM2` model.

   Each page of [`SourceMapping/`](SourceMapping/) prints every declaration of this file that its statement depends
   on.
2. **`Challenge.lean`**, which states
   `NearCubicGates.Close.Release.main_theorem : NearCubicGates.Close.FinalStatement`, imports only `Statement`, and
   has the deliberate `sorry` as its proof. Comparator checks the proof against it.
3. **`comparator.json`**, which names the two modules, the theorem, and the permitted axioms `propext`, `Quot.sound`
   and `Classical.choice`.
4. **`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`**, which pin Lean `v4.32.0` and Mathlib `v4.32.0`
   (commit `81a5d257…`). Through them you trust the Mathlib definitions that the statement uses, among them
   `Nat.clog`, `Nat.log`, `Nat.choose`, `Nat.primeCounting`, `Real.log`, `Real.exp`, real powers, `Finset.card`,
   `Fintype.card`, `Encodable.decode`, `Turing.TM2ComputableInTime` and `Turing.TM2ComputableInPolyTime`. By default
   Mathlib comes as prebuilt binaries (see Caveats to build it from source).
5. **`scripts/comparator.sh` and the tool revisions it pins**: comparator `v4.32.0` (`07bc4ea4…`), lean4export
   `v4.32.0` (`4e791520…`) and the sandbox landrun (`5e9a0d15…`, built with Go 1.27.1, whose download is checked by
   SHA-256). The script checks every revision before it runs that tool.
6. **Lean's kernel**, through which comparator replays the proof. `comparator.json` sets `enable_nanoda` to false, so
   no second kernel is run.

Everything else is checked, not trusted: `Proof/`, `Bindings/`, `StatementSupport.lean`, `MainTheorem.lean` and
`Solution.lean`. Whatever they contain, comparator accepts only a proof of the statement in `Challenge.lean` that uses
at most the three axioms, replayed by the kernel. `Check.lean`, `StatementChecks/` and `SourceMapping/` help you read
the statement; comparator does not rely on them.

Going from `FinalStatement` to the paper's theorem needs two more things: the nine published results must be true,
and no Lean input may say more than its source. Lean can check neither. The table below lists every step at which the
second could fail.

### Fastest path

1. **Is the conclusion the paper's theorem?** (About 10 minutes.) Read section 25 of
   [`Statement.lean`](Statement.lean) beside `thm:main` ([paper/paper.tex, lines 220–233](paper/paper.tex#L220-L233)),
   using [`SourceMapping/main-theorem.md`](SourceMapping/main-theorem.md) and its "What to check": the quantifier
   order, the class 𝒲, λ_n and μ_n, the agreement, the integer budget and E^NP. Then read section 30 (`NineInputs`,
   `FinalStatement`). If `MainStatement` is weaker than `thm:main`, nothing below matters. `StatementChecks/` proves
   part of this comparison in Lean: the integer budget is the paper's floor budget for n ≥ 4 (`mainBudget_iff_floor`),
   every ordinary SYM∘THR circuit with G gates is in the class with W = G, an E^NP certificate determines its
   language, and the statement is neither trivially true nor trivially false. As in the paper, γ is existential, so
   `MainStatement` holds exactly when its conclusion holds for one constant error d > 0 (`mainStatement_iff_exists_d`,
   in `StatementChecks/Nontrivial.lean`).
2. **Is that what was proved?** (5 minutes of your time, then the unattended run of step 3 of "Verify it"; Linux
   only.) Check that `Challenge.lean` imports only `Statement` and states `FinalStatement`, and that `comparator.json`
   names that theorem and the three axioms. Then run `make comparator` in a fresh clone and leave it running. Success
   is the line `VERDICT: PASS (…). comparator: Your solution is okay!` (the parentheses say how comparator was
   launched), and the command exits with status 0. Without comparator, `make` builds the proof and runs `Check.lean`,
   which prints a line beginning
   `PASS: NearCubicGates.Close.main_from_inputs proves NearCubicGates.Close.FinalStatement`. `Check.lean` checks the
   statement, the nine inputs in order and the three axioms, but does not replay the proof through the kernel
   (`make kernel-replay` does).
3. **Are the inputs the published results?** (About an hour, while step 2 runs.) For each input, open its page in
   [`SourceMapping/`](SourceMapping/) and work through its "What to check" list. Each page puts the published text,
   pinned to a page of its source, beside every Lean declaration the input depends on. Pages 1–6 and 8 take a few
   minutes each; pages 7 and 9 take about ten.
4. **Attack the readings.** (Open-ended; 30 minutes is a good start.) In the table below, begin with the rows whose
   justification Lean does not check: **Paper proof**, **Proof step**, **Argument** and **Reading**. For input 7, read
   the paper's Appendix C (`lem:multitape-refuter`, [paper/paper.tex, lines 4835–4841](paper/paper.tex#L4835-L4841),
   and the proof after it). For input 6, read `imp:short-pcp` and the text after it up to `rem:bv14-printed`
   ([lines 2185–2263](paper/paper.tex#L2185-L2263)).
5. **Optional: the quotations.** `make sourcemap` downloads the cited sources and checks every quotation on the pages
   against its pinned source page (see "Optional extra checks").

### Every step where Lean's form differs from the printed one

Every reading and deviation documented on the pages has one row here. For an input, Lean must assume no more than the
source states. For the main theorem (rows marked "main"), Lean must claim no less than the paper. The "Justification"
column first names the kind of step:

- **Special case**: Lean claims less than the printed statement: an instance, a narrower hypothesis or a weaker
  conclusion.
- **Equivalent**: the same statement in another form.
- **Reading**: the source leaves a term undefined or informal, and Lean fixes the standard meaning.
- **Proved in Lean**: a theorem of this repository closes the gap.
- **Proof step**: Lean assumes an inequality displayed in the source's proof, which is stronger than the lemma's
  statement.
- **Paper proof**: the paper proves the Lean reading from the source's proof; Lean does not check that proof.
- **Argument**: an informal argument shows that the source implies the Lean text; Lean does not check it.
- **Provenance**: not a reading, but a limit on how the citation was checked.

Every justification below is stated on the page cited in the last column, in the mapping README's “Models” and
“Encodings” paragraphs, or in the paper lines or Lean file that the row cites.

| # | Published source says | Lean says | Justification | Page |
|---|---|---|---|---|
| main | `thm:main`: W(C) ≤ ⌊n³/(K_d λ_n^{21/4} μ_n^7)⌋, for every sufficiently large n | `MainBudget K n W`: (K·W·μ_n^7)^4·λ_n^21 ≤ n^12, for every n ≥ n₀, where n₀ ≥ 4 | **Equivalent**, and **Proved in Lean**: `mainBudget_iff_floor` (`StatementChecks/MainBudget.lean`) proves the two budgets equivalent for n ≥ 4 and K > 0. The paper defines λ_n and μ_n for n ≥ 4, and any onset can be raised to 4. | [main, items 1, 5](SourceMapping/main-theorem.md) |
| main | F_d ∈ E^NP, the standard class, which the paper does not restate | `InENP F`: an oracle with a multitape NP verifier (witness length and time polynomial in the query's bit length), and a deterministic multitape oracle program that computes F within 2^{e·max(1,n)} steps. A query costs its framed length plus one step, and the answer selects the next state. | **Reading.** This is deterministic 2^O(n) time with an NP oracle, written as an explicit machine. A proof of `InENP F` exhibits such a machine, so the Lean conclusion is no weaker than the paper's. | [main, item 6](SourceMapping/main-theorem.md) |
| main | 𝒲 (`def:class`, lines 184–197): C(x) = f(Σ_i w_i g_i(x)), where the g_i are threshold gates, the w_i are nonzero integers and f : ℤ → {0,1} is arbitrary; W(C) = Σ_i \|w_i\|; real bottom weights are unrestricted (line 208) | `WeightedSymmetricCircuit`; `RealThresholdGate` outputs 1 iff threshold ≤ Σ weight_i·x_i; `topWeight` | **Reading.** This is the standard threshold gate, and the class is the same. The gate's `support` field is determined by its weights (`mem_support_iff`), so it restricts nothing. | [main, items 2–3](SourceMapping/main-theorem.md) |
| 1 | CTW26 Lemma 3.2: "For any THR gate on m input bits, there is an equivalent THR gate where all parameters are integers in range ±m^m" (the paper states it for m ≥ 1) | Every m : ℕ, including m = 0, where Lean reads 0^0 as 1 | **Proved in Lean** at m = 0. The repository proves the m = 0 case (`ctw26_lemma3_2_at_zero`) and shows that it would fail if 0^0 were 0. For m ≥ 1, Lean states the source's sentence. | [1, items 5–6](SourceMapping/1-threshold-normalization.md) |
| 1 | "an equivalent THR gate" (not defined); "all parameters" | Same output on every input in {0,1}^m (`Equivalent`); every weight and the threshold is an integer k with −m^m ≤ k ≤ m^m | **Reading.** Definition 3.1 defines THR gates on {0,1}^m only, and its parameters are exactly the weights and the threshold. | [1, items 3–4](SourceMapping/1-threshold-normalization.md) |
| 2 | CTW26 Lemma A.3, the threshold case of Lemma A.3.1: f restricted by ρ is constant with probability ≥ 1 − O(k/√n). Its proof combines equations (14) and (15) (PDF pp. 27–28) and reaches k·C(n−k, ⌊(n−k)/2⌋)/2^{n−k} before the final O(·). | For every real threshold gate and 0 < k < n, the probability that the gate is live is at most k·C(n−k, ⌊(n−k)/2⌋)/2^{n−k} | **Proof step.** Lean assumes the exact bound displayed in the published proof, not just the lemma's O(·) form, so you trust that display. The paper's k/√(n−k+1) bound and its Markov step are proved in Lean. | [2, items 1, 4, 5](SourceMapping/2-live-restriction.md) |
| 2 | "a random restriction ρ ∈ {0, 1, ∗}^n which has exactly k many ∗-s", drawn from the set P of such ρ, with \|P\| = C(n,k)·2^{n−k}; "non-constant" | `FiniteRestriction n k`: pairs of a k-subset I and an assignment to the other n − k coordinates, averaged uniformly (`mean`). A gate is live (`gateLive`) when it differs on two inputs that agree with the assignment outside I. | **Equivalent.** The pairs are in bijection with P, so the uniform average over them is the probability over P. | [2, items 2–3](SourceMapping/2-live-restriction.md) |
| 3 | Vershynin Theorem 2.8.4: X_1, …, X_N are independent, have mean zero and \|X_i\| ≤ K; for every t ≥ 0, P{\|Σ X_i\| ≥ t} ≤ 2 exp(−(t²/2)/(σ² + Kt/3)), where σ² = Σ E X_i² | A finite nonempty sample set with the uniform measure, a finite nonempty index set, K = 1 and s > 0; the bound is 2 exp(−s²/(2(σ² + s/3))) | **Special case.** Finite uniform spaces, K = 1 and s > 0 are instances, and at K = 1 the two exponents are equal. | [3, items 1, 3, 4](SourceMapping/3-bernstein.md) |
| 3 | "independent" | `finiteIndependent`: for every finite subfamily S and all sets of reals A_i, P[Y_i ∈ A_i for all i ∈ S] = Π_{i∈S} P[Y_i ∈ A_i] | **Equivalent** to mutual independence. Each Y_i has a finite range, so any set of reals can be replaced by its intersection with that range, which is a Borel set with the same preimage. | [3, item 2](SourceMapping/3-bernstein.md) |
| 4 | Apostol: lim_{x→∞} π(x) log x / x = 1 | For every ε > 0 there is an onset ≥ 2 such that \|π(n) log n / n − 1\| < ε for every natural number n past it (Mathlib's `Nat.primeCounting` and `Real.log`) | **Special case.** The real limit implies the limit at natural arguments, and an onset can always be raised to 2. | [4, items 1–3](SourceMapping/4-prime-number-theorem.md) |
| 4 | Provenance: the quotation is the publisher's abstract of Apostol's Chapter 4, which states the limit. The proof, in Chapter 13, is identified from the publisher's page and was not read from a pinned copy. | Unchanged (row above) | **Provenance.** The Lean text is the classical prime number theorem. What is limited is how the citation was checked, not the claim. | [4, Source and item 5](SourceMapping/4-prime-number-theorem.md) |
| 5 | Williams Corollary 4.4 = C.2: two 0-1 matrices "can be multiplied over the integers in O(N² · poly(log N)) time" for all sufficiently large N; Appendix C (p. 26) says this can be implemented "(even on a multitape TM)" | One deterministic multitape machine over bits (at least three tapes, with the output on its own tape) that, for every N ≥ N₀, halts within C·N²·(log₂ N)^e steps with the product | **Reading stated by the source.** Williams states the multitape implementation, and N₀, C and e are the onset and the constants of O(N² poly(log N)). Bits: **Argument**, not checked by Lean. Williams fixes no tape alphabet (paper v2 reads its algorithms over a binary alphabet, lines 1036–1039), and a machine over a larger alphabet runs on bits with a constant-factor slowdown, each symbol coded as a block of cells. | [5, items 1, 4, Class](SourceMapping/5-rectangular-product.md) |
| 5 | Dimensions N × N^{.1} and N^{.1} × N (the paper writes ⌈N^{0.1}⌉) | Only N = k^10, with dimensions N × k and k × N | **Special case.** At N = k^10, N^{.1} = k under every rounding. | [5, item 2](SourceMapping/5-rectangular-product.md) |
| 5 | "multiplied over the integers" | Entries are computed in ℕ, each written in ⌊log₂ N⌋ + 1 binary digits | **Proved in Lean.** The product in ℕ equals the integer product (`product_cast`), and every entry is at most k ≤ N (`product_lt`), in `Bindings/Williams14_Corollary4_4.lean`. | [5, item 3](SourceMapping/5-rectangular-product.md) |
| 6 | Murray, Williams: "for every verifier algorithm V(x, y) running in time T(n) ≥ n" | V is any multitape verifier that halts within T(n) steps on every (x, y) with \|x\| = n (`RunsInTime`), and n ≤ T(n) | **Special case.** Such a machine is a verifier algorithm running in time T(n), so this only narrows the hypothesis. Paper v2 proves the statement for such verifiers when T(n) is computable (Appendix D, `thm:short-pcp-ours`, lines 5253–5261); Lean does not use that proof. | [6, item 1](SourceMapping/6-short-pcp.md) |
| 6 | "an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle circuit"; Murray and Williams leave the computability of T implicit, and paper v2 states it as a hypothesis | A polynomial-time machine of Mathlib's `Turing.TM2` model whose input is x and T(n) in binary, each framed; no hypothesis on T beyond n ≤ T(n) | **Reading.** The input has length O(n + log T(n)), so polynomial time in it is poly(n, log T(n)). An algorithm as Murray and Williams state it may ignore the extra input, and paper v2's proof uses the computability of T only to compute T(n) and quantities derived from it. That polynomial time is the same class for TM2, multitape and random-access machines is an **Argument** (standard simulations), not checked by Lean. | [6, item 9](SourceMapping/6-short-pcp.md); [mapping README, “Models”](SourceMapping/README.md) |
| 6 | "C^O_x has ℓ = log2(T(n)) + O(log log T(n)) inputs" | Constants K and e with 2^ℓ ≤ K·T(n)·L(T(n))^e, where L(m) = ⌈log₂(m + 2)⌉ (`logScale`) | **Special case.** Taking logarithms, this is ℓ ≤ log₂ T(n) + O(log log T(n)), the upper half of the printed equation; the lower half is not claimed. | [6, item 4](SourceMapping/6-short-pcp.md) |
| 6 | "poly(n, log T(n)) size", with oracle gates of ℓ inputs | Size, the number of nodes (inputs, constants and oracle gates included), at most K·(n + b + 1)^e, where b is the number of binary digits of T(n) | **Reading.** poly(·) is read with explicit constants, chosen after V and T, as are the constants of ℓ and the polynomial of A's running time. The size counts nodes, as for the circuits of inputs 8 and 9 (on node and gate counts, see page 8, item 4). | [6, items 3, 5, 8](SourceMapping/6-short-pcp.md) |
| 6 | "If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle O … such that C^O_x is unsatisfiable"; "If V(x, y) rejects on all y of length T(n), then for every oracle O …, C^O_x has at least 2^ℓ · (1 − 1/n) satisfying assignments" | As printed: V(x, y) accepts when some run halts in an accepting state (`Verifier.accepts`), and the satisfying assignments are counted (`satCount`) and compared in the reals; the properties are claimed for n ≥ 1 only | **Special case** at n ≥ 1: at n = 0 the bound 1 − 1/n has no meaning. Since V halts on every input, "rejects on all y" is the negation of "some y makes V accept". | [6, items 2, 6, 7](SourceMapping/6-short-pcp.md) |
| 7 | CLW20 Theorem 1.13. CLW20 writes its proof for random-access machines (p. 19: "For simplicity, we assume all machines are random-access machines in the following"). | Every machine is multitape: the promise machines M, the verifier of L ∈ NTIME[T(n)] (witness length and step bound c(T(n)+1), on every input and witness), and the oracle program R | **Paper proof**, not a special case. The paper's `lem:multitape-refuter` (Appendix C) derives the theorem for multitape machines: the diagonal language runs each enumerated machine through the nondeterministic linear-time universal two-tape simulation of Fortnow and Santhanam (paper v2, lines 2314–2322). Lean does not check this derivation. | [7, items 3, 6, Class](SourceMapping/7-refuter.md) |
| 7, 8 | "every time-constructible function T(n)" (input 7); "any time-constructible function S(n)" (input 8) | `TimeConstructible`, one definition for both inputs: a multitape program writes the binary digits of T(n) from 1^n within C·(T(n)+1) steps | **Reading.** This is the standard notion (T(n) is computed in binary from n in unary in O(T(n)) steps), and the definition states exactly that. It has no n ≤ T(n) clause: CLW20 writes that bound next to “time-constructible” where it needs it, and input 7 states it separately (`InClockRange`, next row). For input 8, which then also covers S with S(n) < n, see the circuit-size row. | [7, item 2](SourceMapping/7-refuter.md), [8, items 1, 4](SourceMapping/8-amplification.md) |
| 7 | "n ≤ T(n) ≤ 2^{poly(n)}" | `InClockRange`: n ≤ T(n), and T(n) ≤ 2^{C(n+1)^k} for some C and k | **Equivalent.** Every polynomial is at most some C(n+1)^k. | [7, item 2](SourceMapping/7-refuter.md) |
| 7 | The promise: M is "guessing at most n/10 bits" | Promise machines take a witness of exactly ⌊n/16⌋ bits (`OrdinaryWeakMachine`) | **Special case**, the page's documented deviation. The promise class is smaller, so the statement claims less (paper v2, lines 2323–2324). | [7, item 4, deviation](SourceMapping/7-refuter.md) |
| 7 | M is "running in o(T(n)) time"; M(x) = 1 iff some guess w makes V_M(x, T(n), w) = 1 (p. 19) | M halts within runtime(n) steps on every input and witness, and for every multiplier m, eventually m·runtime(n) ≤ T(n) (`OrdinaryLittleO`). M(x) means "some witness makes M accept" (`machineValue`). | **Equivalent.** Little-o has its usual meaning, and acceptance is the formula of p. 19. | [7, item 4](SourceMapping/7-refuter.md) |
| 7 | "R runs in poly(T(n)) time"; "for every fixed M and every sufficiently large n" | R and the degree d are chosen first. For each M there are a constant C and an onset past which R outputs x within C·(T(n)+1)^d counted steps. | **Special case.** Letting the constant and the onset depend on the fixed M only weakens the claim; the degree stays fixed with R. | [7, item 1](SourceMapping/7-refuter.md) |
| 7 | "adaptive access to an SAT oracle" | The oracle answers whether an encoded CNF formula with exactly three literals per clause is satisfiable. A query costs its framed length plus one step, and the answer selects the next state. | **Reading.** Access is adaptive as printed. Exactly three literals per clause: **Argument**, not checked by Lean. CLW20 does not say how queries are written; any SAT query, a CNF formula or a circuit, converts in polynomial time into an equisatisfiable CNF formula with exactly three literals per clause (Tseitin's construction; a shorter clause repeats a literal), within R's poly(T(n)) budget. | [7, item 5](SourceMapping/7-refuter.md) |
| 8 | f "does not have (general) circuits of size S(n)"; g cannot be approximated "by circuits of size S(n)^{1/c}". CLW20 defines neither circuits nor size and refers to textbooks (p. 15). | Fan-in-two AND and OR gates, NOT gates, constants and inputs, as a DAG; size = the number of nodes, input and constant nodes included | **Argument** (on the page; not checked by Lean). Node and gate counts differ by at most n + 2, and for large S the existential c absorbs that difference. Small S: Lean's `TimeConstructible` has no n ≤ S(n) clause, and neither has Lemma 3.9. At a length with S(n) < n, parity on n bits serves as g: a circuit of size at most S(n)^{1/c} < n misses an input bit and agrees with parity on exactly half of the inputs; at S(n) = 0 no circuit has size 0. At the other lengths the lemma applied to max(S(n), n) supplies g. The proof uses the lemma only at S(n) = n^{2^D}. | [8, item 4, documented reading](SourceMapping/8-amplification.md) |
| 8 | "given the 2^n-length truth table of f, the truth table of g can be constructed in 2^{O(n)} time" | A Mathlib `Turing.TM2` machine that maps the framed n and the truth table of f to the framed arity and the truth table of g, within 2^{e·n} steps from an onset on | **Reading.** 2^O(n) time is polynomial in the length of the 2^n-bit truth table. That polynomial time is the same class for TM2, multitape and random-access machines is an **Argument** (standard simulations), not checked by Lean. | [8, item 5](SourceMapping/8-amplification.md); [mapping README, “Models”](SourceMapping/README.md) |
| 8 | "There is a constant c ≥ 1 such that, for any time-constructible function S(n)…"; g : {0, 1}^{O(n)} → {0, 1}; "cannot be (1/2 + ε)-approximated" (defined on p. 3) | The real c ≥ 1 is chosen first, and everything else may depend on S. The arity is at most arityFactor·n from an onset on. "Circuits of size s" means size at most s, and approximation is as CLW20 defines it. | **Equivalent.** The quantifier order is the printed one, O(n) is read with its constant and onset, and "size s" means "at most s", as CLW20 glosses it in Lemma 3.6 (p. 17: “for all circuit C of size at most s”). | [8, items 1–3](SourceMapping/8-amplification.md) |
| 9 | CW19 Lemma 24, soundness for δ-far inputs, whose Hamming distance from every accepted input is "more than δn" (p. 11) | `ProximityFar δ`: relative distance at least δ (non-strict), for 0 < δ < 1 | **Special case** at δ/2 (documented deviation (a)). Apply Lemma 24 at δ/2: relative distance at least δ is more than δ/2, and s and the size constants may depend on δ. | [9, item 7, deviations](SourceMapping/9-three-query-pcpp.md) |
| 9 | Lemma 24 states no bound on the proof length | proofBits ≤ K(m+1)^e, where m is the node count of the circuit | **Argument** (documented deviation (b); on the page, not checked by Lean). The verifier reads at most 3·2^r proof positions. Dropping the unread ones and renumbering changes no acceptance probability, and the constructions stay polynomial-time. CW19's own proof of Theorem 5 assumes the same when it applies Lemma 24 (p. 21: “We can also assume \|π\| = ℓ = poly(n)”). | [9, item 9, deviations](SourceMapping/9-three-query-pcpp.md) |
| 9 | "random bits r = O(log n)", where n = \|x\| = \|C\| is the length of the explicit input (Definition 20: "V(x) tosses r(\|x\|) random coins") | 2^r ≤ K(m+1)^e | **Reading.** The code of C has length polynomial in its node count m, so r = O(log n) gives this bound. | [9, items 2, 9](SourceMapping/9-three-query-pcpp.md) |
| 9 | Definition 20, as quoted, gives no running time for the verifier. Property (2): the honest proof is constructed "in poly(\|C\| + \|w\|) time". | A polynomial-time Mathlib TM2 machine computes the whole verifier from the code of C: one clause of three literals per coin outcome, accepted iff their OR is true (property (1)). Another such machine computes the honest proof. | Honest proof: **Special case** of property (2). Verifier: **Reading** (the page's documented reading), not checked by Lean. Definition 20 states no running time; CW19's proof of Theorem 5 uses the verifier of Lemma 24 as “m = 2^{r(\|D\|)} = poly(n) many constraints on the oracle y ◦ π” (p. 21). Read as a polynomial-time algorithm, the verifier gives its 2^r = poly(\|C\|) clauses in polynomial time. For both machines, TM2 has the same polynomial time as the other models (an **Argument**). | [9, items 2, 4, 10](SourceMapping/9-three-query-pcpp.md); [mapping README, “Models”](SourceMapping/README.md) |
| 9 | CW19 Lemma 27: a constant-rate linear code "with minimum relative distance δ, an efficient encoder Enc and an efficient decoder Dec recovering error up to c1 · δ … each bit of the codeword depends on at most n/2 bits of the input" | Each codeword bit is the parity of a support set of at most ⌊n/2⌋ input bits; the length is at most K(n+1); distinct codewords are at relative distance at least `distance`; the decoder recovers every word within relative distance `radius`, with 0 < radius < distance < 1; encoder and decoder are polynomial-time TM2 machines; all of this for n ≥ 2 | **Special case.** Over {0,1}, "linear" means that each bit is a parity of input bits. `distance` and `radius` are existential and may be taken smaller than δ and c1·δ (for example min(δ, 1/2) and min(c1·δ, distance/2)), and n ≥ 2 only weakens the statement. "Efficient" is read as polynomial time; that TM2 has the same polynomial time is an **Argument**. | [9, item 5](SourceMapping/9-three-query-pcpp.md); [mapping README, “Models”](SourceMapping/README.md) |
| 9 | Circuit-Eval: "general fan-in-2 circuit[s]" C and inputs w; Lemma 24 holds "for any constant δ > 0" | Circuits with at least n nodes (`Circuit`), size = node count; 0 < δ < 1 | **Special case.** Restricting to circuits of size at least n and to δ < 1 only weakens the statement. | [9, item 6, deviations](SourceMapping/9-three-query-pcpp.md) |
| 5–9, main | Codes and tape layouts: the sources fix none | One code per object, printed on the pages: framed words. For 5: N in self-delimiting binary followed by the first matrix row by row on tape 0, the second matrix on tape 1, and the product row by row. For 6: x and T(n) in binary, and the oracle circuit as self-delimiting numbers (the node codes of the Boolean circuits, with tag 5 for oracle gates). For 7: machine descriptions (tape and state counts in unary, start state, flags, transition table) and CNF codes. For 8: the framed arity followed by the truth table. For 9: circuit and clause codes. | **Argument**, not checked by Lean. The usual codes of the same objects convert into one another in time polynomial in their length, and for the matrices of input 5 in quasi-linear time on a multitape machine (a transposition by sorting). Every bound absorbs that: N²·polylog N for 5; polynomial, or 2^O(n) on a truth table, for 6, 8 and 9; for 7, re-encoding the fixed M costs a constant that may depend on M. | [Mapping README, “Encodings”](SourceMapping/README.md); encoding rows on pages [5](SourceMapping/5-rectangular-product.md), [6](SourceMapping/6-short-pcp.md), [7](SourceMapping/7-refuter.md), [8](SourceMapping/8-amplification.md), [9](SourceMapping/9-three-query-pcpp.md), [main](SourceMapping/main-theorem.md) |

Some of the paper's adapted forms are missing from the table because Lean proves them from the inputs instead of
assuming them:

- input 1's bit lengths;
- input 2's square-root bound and Markov step;
- input 4's count of primes in (P/2, P];
- input 5's sizes below the onset;
- input 8's transfer to size (n+1)^{2^D} − 1;
- input 9's pointwise form.

The pages say which Lean theorems do this.

### What would break this

`FinalStatement` is an implication. If any field of `NineInputs` is false as stated in Lean, for example because a
reading in the table claims more than its source, then `NineInputs` has no proof and `FinalStatement` holds
vacuously. Neither `Check.lean` nor comparator can detect that. The inputs are closed propositions, so you can examine
them one at a time: if each is true, so is their conjunction. To attack, look for a reading under which a Lean input
is false although the published statement is true. Start with the rows whose justification Lean does not check:

- the multitape refuter (input 7, paper proof);
- the node-count circuit size (input 8, argument);
- the proof-length bound and the verifier's running time (input 9);
- the bound taken from a published proof (input 2);
- the model and encoding arguments (the mapping README's “Models” and “Encodings” paragraphs).

Input 6 deserves a separate look. Paper v2 shows (`rem:bv14-printed`,
[lines 2244–2263](paper/paper.tex#L2244-L2263)) that the printed form of Ben-Sasson and Viola's Theorem 1.1,
restated as CLW20 Lemma 3.10, cannot hold as printed (at a quadratic time bound it would compress SAT instances to polylogarithmic size); it is not among the nine inputs (page 6, "Why not
CLW20 Lemma 3.10"). Input 6 is the weaker statement of Murray and Williams. Paper v2 proves that statement for
deterministic multitape verifiers with computable time bounds in its Appendix D (`thm:short-pcp-ours`,
[lines 5253–5261](paper/paper.tex#L5253-L5261)), from the PCP construction of Ben-Sasson, Chiesa, Genkin and Tromer
with a randomness-efficient soundness amplification. Lean does not use that proof: input 6 is assumed, like the other
eight.

The other way to be wrong is for `MainStatement` to be weaker than `thm:main`; step 1 of the fastest path checks this.

Comparator certifies three things:

1. the theorem in `Solution.lean` has exactly the type stated in `Challenge.lean`, which is built from
   `Statement.lean` and Mathlib alone;
2. its proof uses no axioms beyond `propext`, `Quot.sound` and `Classical.choice`;
3. Lean's kernel accepts the proof, which is built only inside the sandbox in a fresh clone.

Comparator does not certify any of the following:

- that `Statement.lean` says what the paper and the sources say;
- that the nine inputs are true;
- that the Mathlib definitions the statement uses mean what you expect;
- any of the arguments in the table;
- any of the paper's other theorems.

The table and the pages exist for the parts comparator cannot certify.

## AI use

Generative-AI models were used substantively to write this formalization, as they were for the paper (see its "AI
methodology statement"). The result does not depend on trusting them: Lean's kernel checks the proof, and the
`SourceMapping/` pages let a reader check that the assumed statements match the published sources.

## Optional extra checks

- `make kernel-replay`: re-check every declaration with the standalone `leanchecker` (slow; parallel).
- `make names`: the naming check used by CI (`python3 scripts/check_names.py .`).
- `make sourcemap`: download the cited source PDFs from their publishers (`scripts/fetch_sources.sh`) and run
  `python3 SourceMapping/check.py`, which checks the quotations on the mapping pages against their pinned PDF pages
  and every excerpt against the files of this repository. Two of the sources cannot be downloaded by a script (the
  publishers require a browser); the script says how to save them. Displayed formulas that a PDF's extracted text does
  not reproduce are hand-reviewed readings rather than byte-for-byte matches (listed in `SourceMapping/README.md`).
  Without the downloads, `python3 SourceMapping/check.py` checks the excerpts and links only.
- Continuous integration runs the name check and builds the statement (`lake build Challenge`) on every push; the
  full build is a manually started job.

## License

Apache-2.0 ([LICENSE](LICENSE)), except `paper/`, which is CC BY 4.0 ([paper/README.md](paper/README.md)).
Quotations of other papers in `SourceMapping/` and in docstrings are short quotations for verification and remain
their authors'.

## Citation

Please cite the paper: Dev Nag, "Almost-Everywhere Near-Cubic Gate Lower Bounds for SYM∘THR Circuits", version 2,
October 15, 2026. The citation of this repository is in [CITATION.cff](CITATION.cff).
