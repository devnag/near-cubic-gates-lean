# 7. Fixed-machine refuter: CLW20 Theorem 1.13 (paper v2 `imp:ae-refuter`)

[Mapping index](README.md) · input 7 of 9 · field `refuter` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `refuter` of `NineInputs`). The other rows
show every definition that statement uses: all 69 declarations of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. Every machine in the statement is a
multitape machine; paper v2 derives this reading of the theorem in its Appendix C (`lem:multitape-refuter`).

**Source.** L. Chen, X. Lyu, R. R. Williams, “Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization”, ECCC report TR20-150 (2020), [https://eccc.weizmann.ac.il/report/2020/150/download/](https://eccc.weizmann.ac.il/report/2020/150/download/). Page numbers refer to that PDF, SHA-256 `d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c`.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>CLW20, PDF p. 6</b>
<pre>
Theorem 1.13 (Refuter with an NP Oracle, Informal).
For every time-constructible function T(n) such that
n ≤ T(n) ≤ 2^{poly(n)}, there is a language
L ∈ NTIME[T(n)] and an algorithm R such that:
1. Input. The input to R is a pair (M, 1^n), with the
promise that M describes a nondeterministic Turing
machine running in o(T(n)) time and guessing at most
n/10 bits.
2. Output. For every fixed M and every sufficiently
large n, R(M, 1^n) outputs a string x ∈ {0, 1}^n such
that M(x) ≠ L(x).
3. Complexity. R runs in poly(T(n)) time with adaptive
access to an SAT oracle.
</pre>

<b>Paper v2, lines 2304–2313</b> ([paper/paper.tex](../paper/paper.tex#L2304-L2313))

<pre>
\begin{import}[Fixed-machine refuter]\label{imp:ae-refuter}
For every time-constructible \(N\le \Tclk(N)\le2^{\poly(N)}\), there
are a fixed language \(L_{\Tclk}\in\NTIME[\Tclk(N)]\) and a deterministic
SAT-oracle procedure \(R_{\Tclk}\) with the following property. For each
fixed nondeterministic machine \(M\) running in \(o(\Tclk(N))\) time
and guessing at most \(N/10\) bits, the procedure
\(R_{\Tclk}(M,1^N)\) returns, for every sufficiently large \(N\), a word
\(z_N\in\{0,1\}^N\) on which \(M\) and \(L_{\Tclk}\) disagree.
Its running time is \(\poly(\Tclk(N))\).
\end{import}
</pre>

<b>Paper v2, lines 4750–4752</b> ([paper/paper.tex](../paper/paper.tex#L4750-L4752))

<pre>
\Cref{imp:ae-refuter}, fixed-machine refuter &amp;
\cite[Theorem~1.13 and Section~4.1]{CLW20}, formal version Theorem~4.6; \cite{FS16} &amp;
Adapted: read for multitape machines, derived in \cref{lem:multitape-refuter}; weak machines guess at most \(N/16\) bits; no guessed computation trace is added.\\
</pre>

</td><td>

[Statement.lean, lines 1069–1080](../Statement.lean#L1069-L1080)

<pre>
/-- **CLW20 Theorem 1.13, PDF page 6 (printed p.5), verbatim:**
"Theorem 1.13 (Refuter with an NP Oracle, Informal). For every time-constructible function T(n)
such that n ≤ T(n) ≤ 2^{poly(n)}, there is a language L ∈ NTIME[T(n)] and an algorithm R such that:
1. Input. The input to R is a pair (M, 1^n), with the promise that M describes a nondeterministic
Turing machine running in o(T(n)) time and guessing at most n/10 bits.
2. Output. For every fixed M and every sufficiently large n, R(M, 1^n) outputs a string
x ∈ {0,1}^n such that M(x) ≠ L(x).
3. Complexity. R runs in poly(T(n)) time with adaptive access to an SAT oracle."
Each reading, including the multitape machine model, is listed in
`SourceMapping/7-refuter.md`. -/
def CLW20_Theorem1_13 : Prop :=
  ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → Theorem1_13At T
</pre>

[Statement.lean, lines 1056–1067](../Statement.lean#L1056-L1067)

<pre>
/-- The conclusion of Theorem 1.13 at one clock `T`: "there is a language L ∈ NTIME[T(n)] and an
algorithm R such that" items 1–3 hold. The degree `d` of "poly(T(n))" belongs to `R`. The
coefficient `C` and the onset of "every sufficiently large n" may depend on the fixed `M`. -/
def Theorem1_13At (T : ℕ → ℕ) : Prop :=
  ∃ L : Language, InNTIME T L ∧
    ∃ (R : OrdinaryOracleProgram) (d : ℕ),
      ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T →
        ∃ C onset : ℕ, ∀ n, onset ≤ n →
          ∃ x : BitInput n,
            OrdinaryOracleRuns RecoveryOracle.sourceSAT R (pairInput M n) (List.ofFn x)
              (C * (T n + 1) ^ d) ∧
            machineValue M n x ≠ L n x
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 6</b>
<pre>
For every time-constructible function T(n) such that
n ≤ T(n) ≤ 2^{poly(n)}
</pre>

</td><td>

[Statement.lean, lines 1031–1035](../Statement.lean#L1031-L1035)

<pre>
/-- "time-constructible" (standard notion, Tier 1 multitape model): a program that, given the word
`1^n`, outputs the binary digits of `T(n)` within `C·(T(n)+1)` steps. -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 &lt; C ∧ Nonempty (OrdinaryWordFunction ℕ (fun n =&gt; List.replicate n true)
    (fun n =&gt; (T n).bits) (fun n =&gt; C * (T n + 1)))
</pre>

[Statement.lean, lines 1037–1039](../Statement.lean#L1037-L1039)

<pre>
/-- "n ≤ T(n) ≤ 2^{poly(n)}". -/
def InClockRange (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧ ∃ C k : ℕ, ∀ n, T n ≤ 2 ^ (C * (n + 1) ^ k)
</pre>

[Statement.lean, line 597](../Statement.lean#L597)

<pre>
abbrev OrdinaryWordFunction := RepairOrdinary.WordFunction
</pre>

[Statement.lean, lines 546–551](../Statement.lean#L546-L551)

<pre>
structure WordFunction (Request : Type)
    (input output : Request → List Bool) (budget : Request → ℕ) where
  program : Program
  realizes : ∀ r, ∃ receipt,
    run program.machine (budget r) (program.inputTapes (input r)) = some receipt ∧
      receipt.final.tapes program.outputTape = output r
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

<b>CLW20, PDF p. 6</b>
<pre>
Let NTIMEGUESS[t(n), g(n)] be the class of languages
decided by nondeterministic algorithms running in
O(t(n)) steps and guessing at most g(n) bits.
</pre>

<b>CLW20, PDF p. 6</b>
<pre>
there is a language L ∈ NTIME[T(n)]
</pre>

</td><td>

[Statement.lean, lines 1041–1045](../Statement.lean#L1041-L1045)

<pre>
/-- "L ∈ NTIME[T(n)]" (nondeterministic `O(T(n))` time, Tier 1 multitape model): `L` is the
language of a verifier that halts within `c·(T(n)+1)` steps on every witness of length
`c·(T(n)+1)`. -/
def InNTIME (T : ℕ → ℕ) (L : Language) : Prop :=
  ∃ H : OrdinaryHierarchy T, ∀ n (x : BitInput n), L n x = true ↔ H.verifier.language H.time n x
</pre>

[Statement.lean, lines 601–607](../Statement.lean#L601-L607)

<pre>
structure OrdinaryHierarchy (T : ℕ → ℕ) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 0 &lt; coefficient
  halts : ∀ n (x : BitInput n) (w : BitInput (coefficient*(T n+1))),
    ∃ receipt, run verifier.machine (coefficient*(T n+1))
      (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt
</pre>

[Statement.lean, lines 609–610](../Statement.lean#L609-L610)

<pre>
def OrdinaryHierarchy.time {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (n : ℕ) : ℕ :=
  H.coefficient*(T n+1)
</pre>

[Statement.lean, lines 573–578](../Statement.lean#L573-L578)

<pre>
/-- The language of `v` at witness length `witnessLength n`: the inputs for which some witness of that
    length is accepted. -/
def Verifier.language (v : Verifier) (witnessLength : ℕ → ℕ) :
    (n : ℕ) → BitInput n → Prop :=
  fun n x =&gt; ∃ w : BitInput (witnessLength n),
    v.accepts (List.ofFn x) (List.ofFn w)
</pre>

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

[Statement.lean, lines 570–571](../Statement.lean#L570-L571)

<pre>
def Verifier.accepts (v : Verifier) (input witness : List Bool) : Prop :=
  ∃ fuel, v.acceptsAt fuel input witness
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 6</b>
<pre>
M describes a nondeterministic Turing
machine running in o(T(n)) time and guessing at most
n/10 bits.
</pre>

<b>CLW20, PDF p. 19</b>
<pre>
For a nondeterministic Turing machine M, an input x,
and a witness z, let VM(x, T, z) denote the result of
running M on the input x for at most T steps with
witness z.
…
Note that for an M using o(T(n)) time and g(n)
guesses, we have
M(x) = 1 ⇔ ∨_{w ∈ {0,1}^{g(n)}} VM(x, T(n), w) = 1.
</pre>

The displayed equivalence is transcribed linearly.

</td><td>

[Statement.lean, lines 612–617](../Statement.lean#L612-L617)

<pre>
structure OrdinaryWeakMachine where
  verifier : OrdinaryVerifier
  runtime : ℕ → ℕ
  halts : ∀ n (x : BitInput n) (w : BitInput (n/16)),
    ∃ receipt, run verifier.machine (runtime n)
      (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt
</pre>

[Statement.lean, lines 619–621](../Statement.lean#L619-L621)

<pre>
def OrdinaryWeakMachine.accepts (M : OrdinaryWeakMachine)
    (n : ℕ) (x : BitInput n) : Prop :=
  M.verifier.language (fun n =&gt; n/16) n x
</pre>

[Statement.lean, lines 623–625](../Statement.lean#L623-L625)

<pre>
def OrdinaryLittleO (M : OrdinaryWeakMachine) (T : ℕ → ℕ) : Prop :=
  ∀ multiplier : ℕ, 0 &lt; multiplier →
    ∃ onset, ∀ n, onset ≤ n → multiplier*M.runtime n ≤ T n
</pre>

[Statement.lean, lines 1051–1054](../Statement.lean#L1051-L1054)

<pre>
/-- `M(x)`, the truth value of "some witness makes `M` accept `x`" (CLW20 p.19). -/
noncomputable def machineValue (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) : Bool := by
  classical
  exact decide (M.accepts n x)
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 6</b>
<pre>
The input to R is a pair (M, 1^n)
</pre>

The paper fixes no code for the machine description M. Lean's code lists the tape
count and the state count in unary, the start state, the halting and accepting flags, and the transition table
entry by entry.

</td><td>

[Statement.lean, lines 1047–1049](../Statement.lean#L1047-L1049)

<pre>
/-- "The input to R is a pair (M, 1^n)": the framed description of `M`, then the framed `1^n`. -/
def pairInput (M : OrdinaryWeakMachine) (n : ℕ) : List Bool :=
  frame (VerifierEncoding.code M.verifier) ++ frame (List.replicate n true)
</pre>

[Statement.lean, lines 687–695](../Statement.lean#L687-L695)

<pre>
def code (v : OrdinaryVerifier) : List Bool :=
  let width := natBitLength v.stateCount
  List.replicate v.tapeCount true ++ [false] ++
  List.replicate v.stateCount true ++ [false] ++
  fixedBits width v.machine.start.val ++
  (List.ofFn fun i : Fin v.stateCount =&gt; [v.machine.halted i, v.accepting i]).flatten ++
  (List.ofFn fun i : Fin v.stateCount =&gt;
    (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =&gt;
      actionCode width (v.machine.rule i (fun tape =&gt; mask.val.testBit tape.val))).flatten).flatten
</pre>

[Statement.lean, lines 669–670](../Statement.lean#L669-L670)

<pre>
def fixedBits (width value : ℕ) : List Bool :=
  List.ofFn fun i : Fin width =&gt; value.testBit i.val
</pre>

[Statement.lean, lines 672–675](../Statement.lean#L672-L675)

<pre>
def writeCode : Option Bool → List Bool
  | none =&gt; [false, false]
  | some false =&gt; [true, false]
  | some true =&gt; [true, true]
</pre>

[Statement.lean, lines 677–680](../Statement.lean#L677-L680)

<pre>
def moveCode : HeadMove → List Bool
  | .left =&gt; [false, false]
  | .stay =&gt; [true, false]
  | .right =&gt; [false, true]
</pre>

[Statement.lean, lines 682–685](../Statement.lean#L682-L685)

<pre>
def actionCode {t s : ℕ} (width : ℕ) : Option (Action t s) → List Bool
  | none =&gt; false :: List.replicate (width + 4*t) false
  | some action =&gt; true :: (fixedBits width action.nextControl.val ++
      (List.ofFn fun i : Fin t =&gt; writeCode (action.write i) ++ moveCode (action.move i)).flatten)
</pre>

[Statement.lean, line 593](../Statement.lean#L593)

<pre>
abbrev frame := RepairOrdinary.frame
</pre>

[Statement.lean, lines 530–532](../Statement.lean#L530-L532)

<pre>
def frame : List Bool → List Bool
  | [] =&gt; [false]
  | b :: bs =&gt; true :: b :: frame bs
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 6</b>
<pre>
R runs in poly(T(n)) time with adaptive
access to an SAT oracle.
</pre>

The SAT oracle answers whether a CNF formula with three literals per clause is
satisfiable. Each query is written in binary on a query tape and costs its framed length plus one step; the
answer selects the machine's next state, so queries are adaptive.

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

[Statement.lean, lines 818–821](../Statement.lean#L818-L821)

<pre>
noncomputable def sourceSAT (code : Nat) : Bool :=
  match decodeSourceSAT code with
  | some formula =&gt; formula.all (fun clause =&gt; clause.length = 3) &amp;&amp; mathSat formula
  | none =&gt; false
</pre>

[Statement.lean, lines 813–816](../Statement.lean#L813-L816)

<pre>
def decodeSourceSAT (code : Nat) : Option EncodedCNF :=
  (decodeBalancedList code).map fun clauses =&gt;
    clauses.map fun clauseCode =&gt;
      (Encodable.decode (α := List (Bool × Nat)) clauseCode).getD []
</pre>

[Statement.lean, lines 710–712](../Statement.lean#L710-L712)

<pre>
noncomputable def mathSat (formula : EncodedCNF) : Bool := by
  classical
  exact decide (∃ assignment : Nat → Bool, formulaEval assignment formula = true)
</pre>

[Statement.lean, lines 653–654](../Statement.lean#L653-L654)

<pre>
def formulaEval (assignment : ℕ → Bool) (formula : EncodedCNF) : Bool :=
  formula.all (clauseEval assignment)
</pre>

[Statement.lean, lines 650–651](../Statement.lean#L650-L651)

<pre>
def clauseEval (assignment : ℕ → Bool) (clause : EncodedClause) : Bool :=
  clause.any (literalEval assignment)
</pre>

[Statement.lean, lines 647–648](../Statement.lean#L647-L648)

<pre>
def literalEval (assignment : ℕ → Bool) (literal : EncodedLiteral) : Bool :=
  if literal.1 then assignment literal.2 else !(assignment literal.2)
</pre>

[Statement.lean, line 643](../Statement.lean#L643)

<pre>
abbrev EncodedLiteral := Bool × ℕ
</pre>

[Statement.lean, line 645](../Statement.lean#L645)

<pre>
abbrev EncodedClause := List EncodedLiteral
</pre>

[Statement.lean, line 238](../Statement.lean#L238)

<pre>
abbrev EncodedCNF := List (List (Bool × ℕ))
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 19</b>
<pre>
We fix a natural enumeration of all (multitape)
nondeterministic Turing machines. Note that the
specific model does not really matter, see the
discussion in [Wil13], Section 2.1. We use the integer
M to denote the M-th nondeterministic Turing machine
in the enumeration. For simplicity, we assume all
machines are random-access machines in the following.
</pre>

CLW20 writes its proof for random-access machines. Paper v2 derives the theorem
with every machine read as a multitape machine, the reading Lean states:

<b>Paper v2, lines 4835–4841</b> ([paper/paper.tex](../paper/paper.tex#L4835-L4841))

<pre>
\begin{lemma}[Multitape refuter]\label{lem:multitape-refuter}
\Cref{imp:ae-refuter} holds with every machine in it, the class
\(\NTIME\) and the procedure \(R_{\Tclk}\) read for multitape Turing
machines, with the same quantifier order. The language \(L_{\Tclk}\) has a
nondeterministic multitape verifier that halts within \(O(\Tclk(N))\)
steps on every input and every guess.
\end{lemma}
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

Encodings. The paper fixes no tape layout or binary code for these objects. The remaining definitions the
statement uses are printed here, so that every definition it depends on appears on this page.

</td><td>

[Statement.lean, line 61](../Statement.lean#L61)

<pre>
def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1
</pre>

[Statement.lean, lines 74–90](../Statement.lean#L74-L90)

<pre>
def encodeBalancedList : List ℕ → ℕ
  | [] =&gt; 0
  | [value] =&gt; Nat.pair 1 value
  | first :: second :: rest =&gt;
      let values := first :: second :: rest
      let leftLength := (values.length + 1) / 2
      let left := values.take leftLength
      let right := values.drop leftLength
      Nat.pair 2
        (Nat.pair (encodeBalancedList left) (encodeBalancedList right))
termination_by values =&gt; values.length
decreasing_by
  all_goals
    simp_wf
    have : ((rest.length + 2 + 1) / 2) ≤ rest.length + 1 := by omega
    simp
    omega
</pre>

[Statement.lean, lines 92–108](../Statement.lean#L92-L108)

<pre>
def decodeBalancedListAux : ℕ → ℕ → Option (List ℕ)
  | 0, code =&gt; if code = 0 then some [] else none
  | fuel + 1, code =&gt;
      if code = 0 then
        some []
      else
        let outer := Nat.unpair code
        if outer.1 = 1 then
          some [outer.2]
        else if outer.1 = 2 then
          let branches := Nat.unpair outer.2
          match decodeBalancedListAux fuel branches.1,
              decodeBalancedListAux fuel branches.2 with
          | some left, some right =&gt; some (left ++ right)
          | _, _ =&gt; none
        else
          none
</pre>

[Statement.lean, lines 110–111](../Statement.lean#L110-L111)

<pre>
def decodeBalancedListCandidate (code : ℕ) : Option (List ℕ) :=
  decodeBalancedListAux (code + 1) code
</pre>

[Statement.lean, lines 113–115](../Statement.lean#L113-L115)

<pre>
def decodeBalancedList (code : ℕ) : Option (List ℕ) := do
  let values ← decodeBalancedListCandidate code
  if encodeBalancedList values = code then some values else none
</pre>

[Statement.lean, lines 143–145](../Statement.lean#L143-L145)

<pre>
def bitsValue : List Bool → ℕ
  | [] =&gt; 0
  | bit :: rest =&gt; bit.toNat + 2 * bitsValue rest
</pre>

[Statement.lean, line 163](../Statement.lean#L163)

<pre>
abbrev BitInput (n : ℕ) := Fin n → Bool
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
</table>

Superscripts are written with `^`: `2^{poly(n)}` is 2<sup>poly(n)</sup>.

**What to check** (about ten minutes):

1. The quantifiers are in the theorem's order: for every time-constructible T with n ≤ T(n) ≤
   2<sup>poly(n)</sup>, there are a language L in NTIME[T(n)], an oracle program R and a degree d (the exponent of
   poly(T(n)), fixed with R), such that for every weak machine M running in o(T(n)) time there are a constant C and
   an onset (both may depend on the fixed M) such that for every n past the onset, R on input (M, 1<sup>n</sup>)
   outputs some x ∈ {0, 1}<sup>n</sup> within C(T(n)+1)<sup>d</sup> counted steps, and M(x) ≠ L(x).
2. Time-constructible (`TimeConstructible`): a multitape program computes the binary digits of T(n) from
   1<sup>n</sup> within C(T(n)+1) steps. `InClockRange` is n ≤ T(n) ≤ 2<sup>C(n+1)<sup>k</sup></sup>. Input 8
   ([page 8](8-amplification.md)) uses this same definition of time-constructibility.
3. NTIME[T(n)] (`InNTIME`): L is the language of a multitape verifier that reads a witness of length c(T(n)+1)
   and halts within c(T(n)+1) steps on every input and witness (`OrdinaryHierarchy`).
4. The promise machines (`OrdinaryWeakMachine`): a multitape verifier that reads a witness of ⌊n/16⌋ bits and
   halts within runtime(n) steps on every witness; o(T(n)) is `OrdinaryLittleO`: for every multiplier m,
   eventually m · runtime(n) ≤ T(n). M(x) is “some witness makes M accept x” (`machineValue`), as on PDF p. 19.
5. The SAT oracle (`sourceSAT`) answers true exactly on codes of satisfiable CNF formulas with exactly three
   literals per clause; the output is written framed on the output tape (`OrdinaryOracleRuns`). CLW20 does not say
   how SAT queries are written. Any SAT query, a CNF formula or a circuit, converts in polynomial time into an
   equisatisfiable CNF formula with exactly three literals per clause (Tseitin's construction; a shorter clause
   repeats a literal), so R can convert its queries within its poly(T(n)) budget. This is an argument, not checked
   by Lean.
6. The model: every machine above is a multitape machine. This reading is the one step Lean does not check;
   paper v2 derives it in `lem:multitape-refuter` (lines 4835–4841 and its proof).

**Documented deviation:** the promise machines guess ⌊n/16⌋ bits, within the printed n/10. This is a smaller
promise class, so the statement claims less than the theorem (paper v2, lines 2323–2324).

**Class:** literal, multitape reading.
