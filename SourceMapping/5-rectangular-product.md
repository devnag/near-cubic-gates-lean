# 5. Rectangular matrix product: Williams (J. ACM 2014) Corollary 4.4 = C.2 (paper v2 `imp:batch`)

[Mapping index](README.md) · input 5 of 9 · field `rectangularProduct` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `rectangularProduct` of `NineInputs`). The other rows
show every definition that statement uses: all 31 declarations of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. The algorithm is one
multitape Turing machine with two input tapes, one for each matrix, as Williams' Appendix C states (“even on a
multitape TM”).

**Source.** R. Williams, “Nonuniform ACC Circuit Lower Bounds”, Journal of the ACM 61(1), Article 2 (2014), [https://doi.org/10.1145/2559903](https://doi.org/10.1145/2559903). Page numbers refer to that PDF, SHA-256 `78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c`.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>Williams, PDF p. 17</b>
<pre>
COROLLARY 4.4. For all sufficiently large N, two
0-1 matrices of dimensions N × N^{.1} and N^{.1} × N
can be multiplied over the integers in
O(N² · poly(log N)) time.
</pre>

<b>Williams, PDF p. 29</b>
<pre>
COROLLARY C.2. For all sufficiently large N, two
0-1 matrices of dimensions N × N^{.1} and N^{.1} × N
can be multiplied over the integers in
O(N² · poly(log N)) time.
</pre>

<b>Paper v2, lines 1530–1535</b> ([paper/paper.tex](../paper/paper.tex#L1530-L1535))

<pre>
\begin{import}[Williams]\label{imp:batch}
There is one deterministic multitape Turing machine that, for all
sufficiently large \(N\), multiplies over the integers any two
\(0\)-\(1\) matrices of dimensions \(N\times\ceil{N^{0.1}}\) and
\(\ceil{N^{0.1}}\times N\) in \(N^2\poly(\log N)\) steps.
\end{import}
</pre>

Paper v2, line 1537: “This is \cite[Corollary~4.4, restated as
Corollary~C.2]{WilACC14}.”

</td><td>

[Statement.lean, lines 1134–1142](../Statement.lean#L1134-L1142)

<pre>
/-- **Williams, JACM 2014, Corollary 4.4 (PDF p.17) = Corollary C.2 (PDF p.29), verbatim:**
"For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and N^{.1} × N can be
multiplied over the integers in O(N² · poly(log N)) time."

Read with an onset `N₀` and constants `C`, `e`, all
existential, and one multitape machine (Tier 1) that is correct and within `C · N² · (log₂ N)^e`
for every `N = k^10 ≥ N₀`. -/
def Williams14_Corollary4_4 : Prop :=
  ∃ N₀ C e : ℕ, Nonempty (MultitapeMultiplier N₀ C e)
</pre>

</td></tr>
<tr><td>

<b>Williams, PDF p. 26</b>
<pre>
Prima facie, it could be that Coppersmith’s
algorithm is nonuniform, making it difficult to
apply. For the sake of completeness, here we
verify using standard ideas that Coppersmith’s
algorithm can indeed be implemented to run (even
on a multitape TM) in O(N² · poly(log N)) time, on
matrices over any field of poly(N) elements.
</pre>

</td><td>

[Statement.lean, lines 1117–1132](../Statement.lean#L1117-L1132)

<pre>
/-- TIER 1 ALGORITHMIC CLAUSE (separable). One deterministic multitape machine (at least three
tapes; the output tape is neither input tape) that, for every `N = k^10 ≥ N₀` and every pair of
0-1 matrices of dimensions `N × N^{.1}` and `N^{.1} × N`, halts within `C · N² · (log₂ N)^e` steps
with their integer product on the output tape. -/
structure MultitapeMultiplier (N₀ C e : ℕ) where
  tapeCount : ℕ
  stateCount : ℕ
  threeTapes : 3 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFreshLeft : outputTape.val ≠ 0
  outputFreshRight : outputTape.val ≠ 1
  multiplies : ∀ (k : ℕ) (A : BitMatrix (k ^ 10) k) (B : BitMatrix k (k ^ 10)), N₀ ≤ k ^ 10 →
    ∃ receipt, run machine (C * (k ^ 10) ^ 2 * Nat.log 2 (k ^ 10) ^ e) (inputTapes (k ^ 10) A B) =
        some receipt ∧
      receipt.final.tapes outputTape = outputWord (k ^ 10) (product A B)
</pre>

</td></tr>
<tr><td>

<b>Williams, PDF p. 17</b>
<pre>
two 0-1 matrices of dimensions N × N^{.1} and
N^{.1} × N can be multiplied over the integers
</pre>

</td><td>

[Statement.lean, line 254](../Statement.lean#L254)

<pre>
abbrev BitMatrix (rows columns : ℕ) := Fin rows → Fin columns → Bool
</pre>

[Statement.lean, line 256](../Statement.lean#L256)

<pre>
abbrev NatMatrix (rows columns : ℕ) := Fin rows → Fin columns → ℕ
</pre>

[Statement.lean, lines 1099–1100](../Statement.lean#L1099-L1100)

<pre>
/-- A 0-1 matrix entry as the integer `0` or `1`. -/
def bit (b : Bool) : ℕ := if b then 1 else 0
</pre>

[Statement.lean, lines 1102–1104](../Statement.lean#L1102-L1104)

<pre>
/-- "multiplied over the integers": `(A · B)(i, j) = Σ_l A(i, l) · B(l, j)`. -/
def product {n m p : ℕ} (A : BitMatrix n m) (B : BitMatrix m p) : NatMatrix n p :=
  fun i j =&gt; ∑ l, bit (A i l) * bit (B l j)
</pre>

</td></tr>
<tr><td>

The layout of input and output on the tapes. The paper fixes none. Tape 0 holds N in
self-delimiting binary followed by the first matrix row by row, tape 1 holds the second matrix row by row, and the
product is written row by row on a separate output tape, each entry in ⌊log₂ N⌋ + 1 binary digits.

</td><td>

[Statement.lean, lines 1106–1110](../Statement.lean#L1106-L1110)

<pre>
/-- Tier 1 input tapes: tape 0 = `N` in self-delimiting binary, then `A` row by row;
tape 1 = `B` row by row; every other tape blank. -/
def inputTapes {t m : ℕ} (N : ℕ) (A : BitMatrix N m) (B : BitMatrix m N) : Fin t → List Bool :=
  fun tape =&gt; if tape.val = 0 then natWord N ++ rowMajorBitMatrix A
    else if tape.val = 1 then rowMajorBitMatrix B else []
</pre>

[Statement.lean, lines 1112–1115](../Statement.lean#L1112-L1115)

<pre>
/-- Tier 1 output: the `N × N` product row by row, each entry in `⌊log₂ N⌋ + 1` binary digits
(least significant first). -/
def outputWord (N : ℕ) (P : NatMatrix N N) : List Bool :=
  encodedNatCellTape (natBitLength N) (rowMajorNatMatrix P)
</pre>

[Statement.lean, lines 487–489](../Statement.lean#L487-L489)

<pre>
def rowMajorBitMatrix {rows columns : ℕ}
    (matrix : BitMatrix rows columns) : List Bool :=
  (List.ofFn fun row =&gt; List.ofFn fun column =&gt; matrix row column).flatten
</pre>

[Statement.lean, lines 491–492](../Statement.lean#L491-L492)

<pre>
def fixedWidthNatBits (width value : ℕ) : List Bool :=
  List.ofFn fun bit : Fin width =&gt; value.testBit bit.val
</pre>

[Statement.lean, lines 494–495](../Statement.lean#L494-L495)

<pre>
def encodedNatCellTape (width : ℕ) (cells : List ℕ) : List Bool :=
  cells.flatMap (fixedWidthNatBits width)
</pre>

[Statement.lean, lines 471–475](../Statement.lean#L471-L475)

<pre>
/-- A matrix as a sequential row-major cell tape.  This is a `List` in the
logic, not a balanced codec and not a single machine register. -/
def rowMajorNatMatrix {rows columns : ℕ}
    (matrix : NatMatrix rows columns) : List ℕ :=
  (List.ofFn fun row =&gt; List.ofFn fun column =&gt; matrix row column).flatten
</pre>

[Statement.lean, line 61](../Statement.lean#L61)

<pre>
def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1
</pre>

[Statement.lean, line 860](../Statement.lean#L860)

<pre>
def natWord (n : ℕ) : List Bool := framedNatBits n
</pre>

[Statement.lean, lines 511–515](../Statement.lean#L511-L515)

<pre>
/-- A self-delimiting binary word.  Its length prefix makes concatenation of
the variable-width fields unambiguous. -/
def framedNatBits (value : ℕ) : List Bool :=
  List.replicate (natBitLength value) true ++
    false :: fixedWidthNatBits (natBitLength value) value
</pre>

[Statement.lean, lines 508–509](../Statement.lean#L508-L509)

<pre>
def fixedWidthNatBits (width value : ℕ) : List Bool :=
  List.ofFn fun bit : Fin width =&gt; value.testBit bit.val
</pre>

</td></tr>
<tr><td>

<b>Williams, PDF p. 26</b>
<pre>
(even on a multitape TM)
</pre>

<b>Paper v2, lines 1036–1039</b> ([paper/paper.tex](../paper/paper.tex#L1036-L1039))

<pre>
\paragraph{Machine model.}
Algorithms are deterministic or nondeterministic multitape Turing
machines over a binary alphabet, and time counts machine steps. This is
the model of the imported algorithms (\cref{imp:batch,imp:ae-refuter}).
</pre>

The machine model. The paper's algorithms are multitape Turing machines over a binary alphabet, and time
counts steps (paper v2, lines 1037–1039). Lean's model: finitely many control states; each step reads the scanned bit
of every tape, may rewrite that cell and moves each head by at most one cell; `run` returns a result only if the
machine halts within the given number of steps, so a step budget is a time bound.

</td><td>

[Statement.lean, lines 324–328](../Statement.lean#L324-L328)

<pre>
inductive HeadMove where
  | left
  | stay
  | right
deriving DecidableEq
</pre>

[Statement.lean, lines 330–334](../Statement.lean#L330-L334)

<pre>
def HeadMove.apply (move : HeadMove) (head : ℕ) : ℕ :=
  match move with
  | .left =&gt; head - 1
  | .stay =&gt; head
  | .right =&gt; head + 1
</pre>

[Statement.lean, lines 336–337](../Statement.lean#L336-L337)

<pre>
def readTapeBit (tape : List Bool) (position : ℕ) : Bool :=
  tape.getD position false
</pre>

[Statement.lean, lines 339–346](../Statement.lean#L339-L346)

<pre>
/-- Write one cell, extending a one-sided tape with blank (`false`) cells when
the head is just beyond its currently materialized support. -/
def writeTapeBit : List Bool → ℕ → Bool → List Bool
  | [], 0, value =&gt; [value]
  | [], position + 1, value =&gt; false :: writeTapeBit [] position value
  | _old :: tail, 0, value =&gt; value :: tail
  | old :: tail, position + 1, value =&gt;
      old :: writeTapeBit tail position value
</pre>

[Statement.lean, lines 348–351](../Statement.lean#L348-L351)

<pre>
structure Configuration (tapeCount stateCount : ℕ) where
  control : Fin stateCount
  heads : Fin tapeCount → ℕ
  tapes : Fin tapeCount → List Bool
</pre>

[Statement.lean, lines 353–356](../Statement.lean#L353-L356)

<pre>
def Configuration.tapeCells
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount) : ℕ :=
  ∑ tape : Fin tapeCount, (configuration.tapes tape).length
</pre>

[Statement.lean, lines 358–363](../Statement.lean#L358-L363)

<pre>
def Configuration.scanned
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount) :
    Fin tapeCount → Bool :=
  fun tape =&gt; readTapeBit (configuration.tapes tape)
    (configuration.heads tape)
</pre>

[Statement.lean, lines 365–372](../Statement.lean#L365-L372)

<pre>
/-- A finite local action: one replacement bit and one unit head move per
tape, plus the next finite control state. -/
structure Action (tapeCount stateCount : ℕ) where
  nextControl : Fin stateCount
  /-- `none` leaves a tape unchanged; `some bit` writes exactly its scanned
  cell. -/
  write : Fin tapeCount → Option Bool
  move : Fin tapeCount → HeadMove
</pre>

[Statement.lean, lines 374–381](../Statement.lean#L374-L381)

<pre>
/-- The transition function has a finite domain (`Fin stateCount` and one bit
per tape), so it is extensionally a finite transition table. -/
structure Machine (tapeCount stateCount : ℕ) where
  descriptionBits : ℕ
  start : Fin stateCount
  halted : Fin stateCount → Bool
  rule : Fin stateCount → (Fin tapeCount → Bool) →
    Option (Action tapeCount stateCount)
</pre>

[Statement.lean, lines 383–394](../Statement.lean#L383-L394)

<pre>
def applyAction
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount)
    (action : Action tapeCount stateCount) :
    Configuration tapeCount stateCount where
  control := action.nextControl
  heads := fun tape =&gt; (action.move tape).apply (configuration.heads tape)
  tapes := fun tape =&gt;
    match action.write tape with
    | none =&gt; configuration.tapes tape
    | some value =&gt;
        writeTapeBit (configuration.tapes tape) (configuration.heads tape) value
</pre>

[Statement.lean, lines 396–402](../Statement.lean#L396-L402)

<pre>
def step
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (configuration : Configuration tapeCount stateCount) :
    Option (Configuration tapeCount stateCount) :=
  (machine.rule configuration.control configuration.scanned).map
    (applyAction configuration)
</pre>

[Statement.lean, lines 404–413](../Statement.lean#L404-L413)

<pre>
/-- Explicit tapes are the standard source input.  Any conversion from a
compact request to these tapes must be a separately executed loader. -/
def initialConfiguration
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (inputTapes : Fin tapeCount → List Bool) :
    Configuration tapeCount stateCount where
  control := machine.start
  heads := fun _tape =&gt; 0
  tapes := inputTapes
</pre>

[Statement.lean, lines 415–418](../Statement.lean#L415-L418)

<pre>
structure ExecutionReceipt (tapeCount stateCount : ℕ) where
  final : Configuration tapeCount stateCount
  steps : ℕ
  peakTapeCells : ℕ
</pre>

[Statement.lean, lines 420–449](../Statement.lean#L420-L449)

<pre>
def runFrom
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) :
    ℕ → Configuration tapeCount stateCount →
      Option (ExecutionReceipt tapeCount stateCount)
  | 0, configuration =&gt;
      if machine.halted configuration.control then
        some
          { final := configuration
            steps := 0
            peakTapeCells := configuration.tapeCells }
      else none
  | fuel + 1, configuration =&gt;
      if machine.halted configuration.control then
        some
          { final := configuration
            steps := 0
            peakTapeCells := configuration.tapeCells }
      else
        match step machine configuration with
        | none =&gt; none
        | some next =&gt;
            match runFrom machine fuel next with
            | none =&gt; none
            | some suffix =&gt;
                some
                  { final := suffix.final
                    steps := suffix.steps + 1
                    peakTapeCells := max configuration.tapeCells
                      suffix.peakTapeCells }
</pre>

[Statement.lean, lines 451–456](../Statement.lean#L451-L456)

<pre>
def run
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (fuel : ℕ) (inputTapes : Fin tapeCount → List Bool) :
    Option (ExecutionReceipt tapeCount stateCount) :=
  runFrom machine fuel (initialConfiguration machine inputTapes)
</pre>

</td></tr>
</table>

Superscripts are written with `^`: `N^{.1}` is N<sup>.1</sup> = N<sup>1/10</sup>.

**What to check** (a few minutes):

1. The quantifiers: an onset N₀ and constants C and e, chosen together with one machine, such that for every
   N ≥ N₀ of the form N = k<sup>10</sup> and every pair of 0-1 matrices of dimensions N × k and k × N, the machine
   halts within C · N² · (log₂ N)<sup>e</sup> steps with their product on the output tape. “For all sufficiently
   large N” is the onset; O(N² · poly(log N)) is C · N² · (log₂ N)<sup>e</sup>.
2. N<sup>.1</sup> is a whole number exactly when N = k<sup>10</sup>, and then it is k. The statement asks only for
   these N, where every rounding of N<sup>.1</sup> agrees (paper v2 writes ⌈N<sup>0.1</sup>⌉), so every reading of
   the printed corollary implies it.
3. “Multiplied over the integers”: entry (i, j) of the product is Σ<sub>l</sub> A(i, l) · B(l, j) with each 0-1
   entry read as the integer 0 or 1 (`bit`, `product`), stated in ℕ because every entry is nonnegative. This
   repository proves it equals the product over ℤ (`product_cast`) and that every entry is at most k ≤ N
   (`product_lt`), so the output width ⌊log₂ N⌋ + 1 loses nothing (in [`Bindings/Williams14_Corollary4_4.lean`](../Bindings/Williams14_Corollary4_4.lean)).
4. The machine is a deterministic multitape Turing machine over bits with at least three tapes; the output tape is
   neither input tape. `run` returns a result only if the machine halts within the step budget. Williams does not
   fix a tape alphabet; paper v2 reads its algorithms over a binary alphabet (lines 1036–1039). A multitape machine
   over a larger finite alphabet runs on bits with a constant-factor slowdown, each symbol coded as a block of a
   fixed number of cells; this standard simulation is an argument, not checked by Lean.
5. Below the onset the statement says nothing, as in the paper. The proof handles the finitely many smaller sizes
   itself, with a lookup table in front of the machine, proved correct in Lean (module
   `Bindings.Williams14_Corollary4_4`); it is not an assumption.

**Documented deviations:** none.

**Class:** literal, multitape reading. The machine model is the one interpretive step Lean does not check: Williams
states the multitape implementation in Appendix C (p. 26, quoted above).
