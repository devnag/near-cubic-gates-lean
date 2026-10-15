# Main theorem: near-cubic constant-error hardness (paper v2 `thm:main`)

[Mapping index](README.md) · the theorem the proof concludes

The first row is the main theorem of paper v2 and the Lean proposition `MainStatement` that the proof
concludes. The other rows show every definition `MainStatement` uses: all 51 declarations of its closure in the
trusted statement file, each printed exactly as it appears in that file. The closure stops at Lean's core library
and Mathlib, whose definitions are not printed. The last row is the theorem this repository proves: the nine
published inputs (pages 1–9) imply `MainStatement`.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>Paper v2, lines 220–233</b> ([paper/paper.tex](../paper/paper.tex#L220-L233))

<pre>
\begin{theorem}[Almost-everywhere near-cubic constant-error hardness]
\label{thm:main}\label{thm:gadget-fixed-error}
There is a rational constant \(0&lt;\gamma&lt;1\) such that, for every
fixed \(0&lt;d&lt;\gamma/5\), there are a positive integer \(K_d\)
and a language \(F_d\in\ENP\) with the following property.
For every sufficiently large \(n\) and every \(C\in\cW\),
\[
 \boxed{\quad
 W(C)\le\floor{\frac{n^3}{K_d\lambda_n^{21/4}\mu_n^7}}
 \quad\Longrightarrow\quad
 \operatorname{agr}(C,F_d)&lt;1-d .
 \quad}
\]
\end{theorem}
</pre>

</td><td>

[Statement.lean, lines 1221–1223](../Statement.lean#L1221-L1223)

<pre>
/-- The paper's main theorem (`thm:main`, also labelled `thm:gadget-fixed-error`). -/
def MainStatement : Prop :=
  ∃ gamma : ℚ, 0 &lt; gamma ∧ gamma &lt; 1 ∧ MainAt gamma
</pre>

[Statement.lean, lines 1213–1219](../Statement.lean#L1213-L1219)

<pre>
/-- The conclusion of `thm:main`, for its fixed rational soundness gap. -/
def MainAt (gamma : ℚ) : Prop :=
  ∀ d : ℝ, 0 &lt; d → d &lt; (gamma : ℝ) / 5 →
    ∃ K : ℕ, 0 &lt; K ∧ ∃ F : Language, InENP F ∧
      ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
        ∀ C : WeightedSymmetricCircuit n,
          MainBudget K n C.topWeight → agreement C F &lt; 1 - d
</pre>

</td></tr>
<tr><td>

<b>Paper v2, lines 184–197</b> ([paper/paper.tex](../paper/paper.tex#L184-L197))

<pre>
\begin{definition}\label{def:class}
A weighted symmetric threshold circuit has the form
\[
 C(x)=f(X(x)),\qquad X(x)=\sum_{i=1}^G w_i g_i(x),
 \qquad w_i\in\Z\setminus\{0\},
\]
where each \(g_i\) is a threshold gate and \(f:\Z\to\{0,1\}\)
is arbitrary. Its top weight is \(W(C)=\sum_i|w_i|\).
Write \(\cW\) for this class.
We say that \(C\) has period \(m\) if its lookup on the full frame
\([-W(C),W(C)]\cap\Z\) is the restriction of a Boolean function
on \(\Z/m\Z\). Both \(W(C)\) and the period refer to this one
representation.
\end{definition}
</pre>

<b>Paper v2, lines 200–208</b> ([paper/paper.tex](../paper/paper.tex#L200-L208))

<pre>
The resource \(W\) counts wires \emph{entering the output gate},
including multiplicity, not all wires in both layers. A negative
contribution \(-a g_i\) can be replaced by \(a(1-g_i)\), with a
constant shift absorbed into \(f\); complements of threshold gates
are threshold gates. Thus this is the ordinary symmetric-top model
with repeated connections counted, as in Chen--Tal--Wang
\cite[Section~5.3]{CTW26}. With one top wire per bottom gate, \(W\)
is the bottom-gate count; counting the single output gate adds one.
Bottom fan-in and real bottom weights remain unrestricted.
</pre>

</td><td>

[Statement.lean, lines 1171–1178](../Statement.lean#L1171-L1178)

<pre>
/-- A representation in the paper's class `𝒲`. Bottom weights are arbitrary
real numbers; signed integral top weights are charged by absolute value. -/
structure WeightedSymmetricCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  coefficient : Fin bottomCount → ℤ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  lookup : ℤ → Bool
</pre>

[Statement.lean, lines 1180–1182](../Statement.lean#L1180-L1182)

<pre>
def WeightedSymmetricCircuit.topWeight {n : ℕ}
    (C : WeightedSymmetricCircuit n) : ℕ :=
  ∑ i, (C.coefficient i).natAbs
</pre>

[Statement.lean, lines 1184–1186](../Statement.lean#L1184-L1186)

<pre>
noncomputable def WeightedSymmetricCircuit.score {n : ℕ}
    (C : WeightedSymmetricCircuit n) (x : BitInput n) : ℤ :=
  ∑ i, C.coefficient i * (if (C.bottom i).eval x then 1 else 0)
</pre>

[Statement.lean, lines 1188–1190](../Statement.lean#L1188-L1190)

<pre>
noncomputable def WeightedSymmetricCircuit.eval {n : ℕ}
    (C : WeightedSymmetricCircuit n) (x : BitInput n) : Bool :=
  C.lookup (C.score x)
</pre>

</td></tr>
<tr><td>

A threshold gate on n inputs, in the standard sense the paper uses (line 190; line 208:
“Bottom fan-in and real bottom weights remain unrestricted”): real weights w<sub>i</sub> and a real threshold θ;
the gate outputs 1 exactly when Σ<sub>i</sub> w<sub>i</sub>x<sub>i</sub> ≥ θ.

</td><td>

[Statement.lean, line 163](../Statement.lean#L163)

<pre>
abbrev BitInput (n : ℕ) := Fin n → Bool
</pre>

[Statement.lean, line 169](../Statement.lean#L169)

<pre>
def bitAsReal (bit : Bool) : ℝ := if bit then 1 else 0
</pre>

[Statement.lean, lines 171–176](../Statement.lean#L171-L176)

<pre>
/-- A semantic threshold gate together with its exact retained support. -/
structure RealThresholdGate (n : ℕ) where
  weight : Fin n → ℝ
  threshold : ℝ
  support : Finset (Fin n)
  mem_support_iff : ∀ i, i ∈ support ↔ weight i ≠ 0
</pre>

[Statement.lean, lines 178–180](../Statement.lean#L178-L180)

<pre>
noncomputable def RealThresholdGate.eval {n : ℕ} (gate : RealThresholdGate n)
    (input : BitInput n) : Bool :=
  decide (gate.threshold ≤ ∑ i, gate.weight i * bitAsReal (input i))
</pre>

</td></tr>
<tr><td>

<b>Paper v2, lines 210–218</b> ([paper/paper.tex](../paper/paper.tex#L210-L218))

<pre>
For \(n\ge4\), write
\[
 \lambda_n=\ceil{\lgx n},\qquad
 \mu_n=\ceil{\lgx\lambda_n}.
\]
For an \(n\)-input circuit, \(\operatorname{agr}(C,F)\) means
\(\Pr_{x\sim\{0,1\}^n}[C(x)=F(x)]\).
\emph{Almost everywhere} means at every sufficiently large \(n\),
with the language fixed before choosing \(n\) or the candidate circuit.
</pre>

</td><td>

[Statement.lean, line 1204](../Statement.lean#L1204)

<pre>
def lambda (n : ℕ) : ℕ := Nat.clog 2 n
</pre>

[Statement.lean, line 1206](../Statement.lean#L1206)

<pre>
def mu (n : ℕ) : ℕ := Nat.clog 2 (lambda n)
</pre>

[Statement.lean, lines 1192–1195](../Statement.lean#L1192-L1195)

<pre>
noncomputable def agreement {n : ℕ} (C : WeightedSymmetricCircuit n)
    (F : Language) : ℝ :=
  ((Finset.univ.filter fun x : BitInput n =&gt; C.eval x = F n x).card : ℝ) /
    (Fintype.card (BitInput n) : ℝ)
</pre>

[Statement.lean, line 165](../Statement.lean#L165)

<pre>
abbrev BoolFunction (n : ℕ) := BitInput n → Bool
</pre>

[Statement.lean, line 167](../Statement.lean#L167)

<pre>
abbrev Language := (n : ℕ) → BoolFunction n
</pre>

</td></tr>
<tr><td>

<b>Paper v2, lines 226–231</b> ([paper/paper.tex](../paper/paper.tex#L226-L231))

<pre>
\[
 \boxed{\quad
 W(C)\le\floor{\frac{n^3}{K_d\lambda_n^{21/4}\mu_n^7}}
 \quad\Longrightarrow\quad
 \operatorname{agr}(C,F_d)&lt;1-d .
 \quad}
</pre>

</td><td>

[Statement.lean, lines 1208–1211](../Statement.lean#L1208-L1211)

<pre>
/-- The budget in integers, `(K·w·μ^7)^4·λ^21 ≤ n^12`. For `n ≥ 4` and `K &gt; 0` it is equivalent to the paper's
`w ≤ ⌊n^3 / (K λ^(21/4) μ^7)⌋` (SourceMapping/main-theorem.md). -/
def MainBudget (K n w : ℕ) : Prop :=
  (K * w * mu n ^ 7) ^ 4 * lambda n ^ 21 ≤ n ^ 12
</pre>

</td></tr>
<tr><td>

E<sup>NP</sup> (line 224), the standard class: languages decided in time
2<sup>O(n)</sup> by a deterministic machine with an oracle for a language in NP. The paper uses the class without
restating its definition.

</td><td>

[Statement.lean, lines 1197–1202](../Statement.lean#L1197-L1202)

<pre>
/-- Ordinary deterministic exponential time with an NP oracle. This is an
actual finite-control execution certificate, not an uninterpreted predicate. -/
def InENP (F : Language) : Prop :=
  ∃ oracle : ℕ → Bool,
    Nonempty (RepairSource.EncodedNPVerifier oracle) ∧
    Nonempty (RepairSource.OrdinaryENPCertificate oracle F)
</pre>

[Statement.lean, lines 779–790](../Statement.lean#L779-L790)

<pre>
/-- An NP verifier for the query predicate: an ordinary verifier whose time and witness length are
polynomial in the length of the binary query word `code.bits`, not in its numeric value. -/
structure EncodedNPVerifier (oracle : ℕ → Bool) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 1 ≤ coefficient
  degree : ℕ
  correct : ∀ code : ℕ, oracle code = true ↔
    ∃ witness : List Bool,
      witness.length ≤ coefficient * (natBitLength code + 1) ^ degree ∧
      verifier.acceptsAt (coefficient * (natBitLength code + 1) ^ degree)
        code.bits witness
</pre>

[Statement.lean, lines 792–798](../Statement.lean#L792-L798)

<pre>
structure OrdinaryENPCertificate (oracle : ℕ → Bool) (language : Language) where
  program : OrdinaryOracleProgram
  exponent : ℕ
  exponentPositive : 1 ≤ exponent
  computes : ∀ n (input : BitInput n),
    OrdinaryOracleRuns oracle program (List.ofFn input) (language n input).toNat.bits
      (2 ^ (exponent * max 1 n))
</pre>

</td></tr>
<tr><td>

The oracle machine of E<sup>NP</sup>: a deterministic multitape machine that writes a
query on a query tape and receives the oracle's answer, which selects its next state; a query costs its framed
length plus one step. Its input and output are framed words on separate tapes.

</td><td>

[Statement.lean, lines 727–729](../Statement.lean#L727-L729)

<pre>
structure OracleReturn (stateCount : ℕ) where
  onFalse : Fin stateCount
  onTrue : Fin stateCount
</pre>

[Statement.lean, lines 731–735](../Statement.lean#L731-L735)

<pre>
structure OrdinaryOracleProgram where
  base : OrdinaryProgram
  queryTape : Fin base.tapeCount
  queryFresh : queryTape.val ≠ 0
  query : Fin base.stateCount → Option (OracleReturn base.stateCount)
</pre>

[Statement.lean, lines 737–738](../Statement.lean#L737-L738)

<pre>
abbrev OrdinaryOracleProgram.Config (program : OrdinaryOracleProgram) :=
  Configuration program.base.tapeCount program.base.stateCount
</pre>

[Statement.lean, lines 740–757](../Statement.lean#L740-L757)

<pre>
/-- One step of an oracle program, with its cost: an ordinary machine step or an oracle query (see the
constructors). -/
inductive OrdinaryOracleStep (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | local (before after : program.Config)
      (notHalted : program.base.machine.halted before.control = false)
      (notQuery : program.query before.control = none)
      (transition : step program.base.machine before = some after) :
      OrdinaryOracleStep oracle program 1 before after
  | ask (before : program.Config) (bits padding : List Bool)
      (rule : OracleReturn program.base.stateCount)
      (notHalted : program.base.machine.halted before.control = false)
      (atQuery : program.query before.control = some rule)
      (rewound : before.heads program.queryTape = 0)
      (writtenQuery : before.tapes program.queryTape = frame bits ++ padding) :
      OrdinaryOracleStep oracle program ((frame bits).length + 1) before
        { before with control := if oracle (CanonicalBinary.bitsValue bits)
            then rule.onTrue else rule.onFalse }
</pre>

[Statement.lean, lines 759–766](../Statement.lean#L759-L766)

<pre>
inductive OrdinaryOracleTrace (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | refl (configuration : program.Config) :
      OrdinaryOracleTrace oracle program 0 configuration configuration
  | cons {cost rest : ℕ} {before middle after : program.Config}
      (step : OrdinaryOracleStep oracle program cost before middle)
      (tail : OrdinaryOracleTrace oracle program rest middle after) :
      OrdinaryOracleTrace oracle program (cost + rest) before after
</pre>

[Statement.lean, lines 768–777](../Statement.lean#L768-L777)

<pre>
/-- Inputs and outputs are framed, with a distinct initially blank output tape.
All data preparation, querying and final head movements inside the program
must be present in the counted trace. -/
def OrdinaryOracleRuns (oracle : ℕ → Bool) (program : OrdinaryOracleProgram)
    (input output : List Bool) (budget : ℕ) : Prop :=
  ∃ cost final, cost ≤ budget ∧
    OrdinaryOracleTrace oracle program cost
      (initialConfiguration program.base.machine (program.base.inputTapes input)) final ∧
    program.base.machine.halted final.control = true ∧
    final.tapes program.base.outputTape = frame output
</pre>

[Statement.lean, line 595](../Statement.lean#L595)

<pre>
abbrev OrdinaryProgram := RepairOrdinary.Program
</pre>

[Statement.lean, lines 534–540](../Statement.lean#L534-L540)

<pre>
structure Program where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFresh : outputTape.val ≠ 0
</pre>

[Statement.lean, lines 542–544](../Statement.lean#L542-L544)

<pre>
def Program.inputTapes (p : Program) (word : List Bool) :
    Fin p.tapeCount → List Bool :=
  fun i =&gt; if i.val = 0 then frame word else []
</pre>

</td></tr>
<tr><td>

The NP verifier: a deterministic multitape machine with an input tape and a witness tape
that accepts a query exactly when some witness of polynomial length makes it halt in an accepting state within
polynomially many steps.

</td><td>

[Statement.lean, line 599](../Statement.lean#L599)

<pre>
abbrev OrdinaryVerifier := RepairOrdinary.Verifier
</pre>

[Statement.lean, lines 553–558](../Statement.lean#L553-L558)

<pre>
structure Verifier where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  accepting : Fin stateCount → Bool
</pre>

[Statement.lean, lines 560–563](../Statement.lean#L560-L563)

<pre>
def Verifier.inputTapes (v : Verifier)
    (input witness : List Bool) : Fin v.tapeCount → List Bool :=
  fun i =&gt; if i.val = 0 then frame input
    else if i.val = 1 then frame witness else []
</pre>

[Statement.lean, lines 565–568](../Statement.lean#L565-L568)

<pre>
def Verifier.acceptsAt (v : Verifier) (fuel : ℕ)
    (input witness : List Bool) : Prop :=
  ∃ receipt, run v.machine fuel (v.inputTapes input witness) = some receipt ∧
    v.accepting receipt.final.control = true
</pre>

</td></tr>
<tr><td>

<b>Paper v2, lines 1036–1044</b> ([paper/paper.tex](../paper/paper.tex#L1036-L1044))

<pre>
\paragraph{Machine model.}
Algorithms are deterministic or nondeterministic multitape Turing
machines over a binary alphabet, and time counts machine steps. This is
the model of the imported algorithms (\cref{imp:batch,imp:ae-refuter}).
Arithmetic on polynomial-bit integers uses elementary multiword
algorithms. When an algorithm consults a large table inside a loop, it
first sorts the relevant records by key and then merges, which costs a
logarithmic factor over reading the records once. All such overheads
are fixed polynomial factors.
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
<tr><td>

<b>Paper v2, lines 4721–4727</b> ([paper/paper.tex](../paper/paper.tex#L4721-L4727))

<pre>
\section{Source mapping for the published inputs}\label{app:sources}

The principal published inputs are listed below with their source
locations and adaptations; supporting references appear at their points
of use. Each listed statement was checked against a copy of its source. \emph{Verbatim}
means the statement is used as the source states it; \emph{adapted}
records what changed.
</pre>

This repository proves the main theorem from the nine published
inputs of this mapping (pages 1–9), in the order of the fields of `NineInputs`; no other assumption enters. The
proof is [`main_from_inputs`](../MainTheorem.lean#L41) (in [`MainTheorem.lean`](../MainTheorem.lean)).

</td><td>

[Statement.lean, lines 1575–1585](../Statement.lean#L1575-L1585)

<pre>
/-- The nine published inputs of the main theorem. -/
structure NineInputs : Prop where
  normalization : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2
  restriction : NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction
  bernstein : NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0}
  primes : NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem
  rectangularProduct : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4
  shortPCP : NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2
  refuter : NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13
  amplification : CLW20_Lemma3_9_Multitape
  threeQueryPCPP : NearCubicGates.PublishedSources.PCPP.ThreeQuerySourceGroup
</pre>

[Statement.lean, lines 1587–1588](../Statement.lean#L1587-L1588)

<pre>
/-- The main theorem from the nine inputs. -/
def FinalStatement : Prop := NineInputs → NearCubicGates.Target.MainStatement
</pre>

</td></tr>
<tr><td>

Encodings. The paper fixes no tape layout or binary code for these objects. The remaining definitions the
statement uses are printed here, so that every definition it depends on appears on this page.

</td><td>

[Statement.lean, line 61](../Statement.lean#L61)

<pre>
def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1
</pre>

[Statement.lean, lines 143–145](../Statement.lean#L143-L145)

<pre>
def bitsValue : List Bool → ℕ
  | [] =&gt; 0
  | bit :: rest =&gt; bit.toNat + 2 * bitsValue rest
</pre>

[Statement.lean, lines 530–532](../Statement.lean#L530-L532)

<pre>
def frame : List Bool → List Bool
  | [] =&gt; [false]
  | b :: bs =&gt; true :: b :: frame bs
</pre>

[Statement.lean, line 593](../Statement.lean#L593)

<pre>
abbrev frame := RepairOrdinary.frame
</pre>

</td></tr>
</table>

Superscripts are written with `^` in Lean comments: `n^12` is n<sup>12</sup>.

**What to check** (about ten minutes):

1. The quantifiers are in the paper's order: there is a rational γ with 0 < γ < 1 such that for every real d with
   0 < d < γ/5 there are a positive integer K and a language F in E<sup>NP</sup>, and an n₀, such that for every
   n ≥ n₀ and every circuit C of the class on n inputs, the budget implies agr(C, F) < 1 − d (`MainStatement`,
   `MainAt`). “For every sufficiently large n” is n₀; n₀ ≥ 4 is required because λ<sub>n</sub> and μ<sub>n</sub>
   are defined for n ≥ 4.
2. The class 𝒲 (`WeightedSymmetricCircuit`): G bottom threshold gates g<sub>i</sub> with arbitrary real weights,
   nonzero integer coefficients w<sub>i</sub>, and an arbitrary lookup f : ℤ → {0, 1}; `score` is
   X(x) = Σ w<sub>i</sub>g<sub>i</sub>(x), `eval` is f(X(x)), and `topWeight` is W(C) = Σ |w<sub>i</sub>|.
3. A threshold gate (`RealThresholdGate.eval`) outputs 1 exactly when threshold ≤ Σ weight<sub>i</sub>·x<sub>i</sub>.
   Its `support` field is the set of nonzero weights (`mem_support_iff`), so it restricts nothing.
4. λ<sub>n</sub> = ⌈log₂ n⌉ is `Nat.clog 2 n`, μ<sub>n</sub> = ⌈log₂ λ<sub>n</sub>⌉, and `agreement` is the fraction
   of the 2<sup>n</sup> inputs on which C and F agree.
5. The budget. For n ≥ 4, λ<sub>n</sub> ≥ 2 and μ<sub>n</sub> ≥ 1. For a natural number W,
   W ≤ ⌊n³/(Kλ<sup>21/4</sup>μ<sup>7</sup>)⌋ holds exactly when KWμ<sup>7</sup>λ<sup>21/4</sup> ≤ n³, and,
   raising both nonnegative sides to the fourth power, exactly when (KWμ<sup>7</sup>)<sup>4</sup>λ<sup>21</sup> ≤
   n<sup>12</sup>. That is `MainBudget K n C.topWeight`.
6. E<sup>NP</sup> (`InENP`): an oracle O : ℕ → Bool together with (a) an NP verifier for O
   (`EncodedNPVerifier`: O(code) is true exactly when some witness of length at most c(|code|+1)<sup>d</sup> makes
   a multitape verifier accept the binary code within that many steps) and (b) a deterministic oracle program that
   computes F on every input of length n within 2<sup>e·max(1, n)</sup> counted steps (`OrdinaryENPCertificate`).
   Every oracle query is charged its framed length plus one step, and the answer selects the next state, so
   queries are adaptive. This is deterministic 2<sup>O(n)</sup> time with an NP oracle.
7. The theorem this repository proves is `FinalStatement`: the nine inputs (`NineInputs`) imply `MainStatement`. Each
   field of `NineInputs` is the first-row statement of one page of this mapping.

**Documented deviations:** none. The budget is stated without real division (item 5); the class, the gate and the
agreement are the paper's.
