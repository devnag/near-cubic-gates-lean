# 8. Hardness amplification: CLW20 Lemma 3.9 (paper v2 `imp:ae-amplification`)

[Mapping index](README.md) · input 8 of 9 · field `amplification` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `amplification` of `NineInputs`). The other rows
show every definition that statement uses: all 40 declarations of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. CLW20 attributes the lemma to
Sudan, Trevisan and Vadhan (2001). Time-constructibility is the multitape notion of input 7 (page 7), with the same
Lean definition; the truth-table construction is a machine of Mathlib's standard `Turing.TM2` model.

**Source.** L. Chen, X. Lyu, R. R. Williams, “Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization”, ECCC report TR20-150 (2020), [https://eccc.weizmann.ac.il/report/2020/150/download/](https://eccc.weizmann.ac.il/report/2020/150/download/). Page numbers refer to that PDF, SHA-256 `d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c`.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>CLW20, PDF p. 18</b>
<pre>
Lemma 3.9 ([STV01]). There is a constant c ≥ 1 such
that, for any time-constructible function S(n) and
every f : {0, 1}^n → {0, 1} that does not have
(general) circuits of size S(n). There is a function
g : {0, 1}^{O(n)} → {0, 1} that cannot be
(1/2 + S(n)^{−1/c})-approximated by circuits of size
S(n)^{1/c}. Furthermore, given the 2^n-length truth
table of f, the truth table of g can be constructed
in 2^{O(n)} time.
</pre>

<b>Paper v2, lines 2331–2349</b> ([paper/paper.tex](../paper/paper.tex#L2331-L2349))

<pre>
\begin{import}[General-circuit hardness amplification]
\label{imp:ae-amplification}
There is an absolute constant \(b_{\rm amp}\ge1\) with the following
property. For every fixed integer \(G\ge b_{\rm amp}\) there is a constant
\(a_G\ge1\) such that, if a \(q\)-input Boolean function has no general
Boolean circuit of size \(q^G\), its truth table determines, in
\(2^{O(q)}\) time, a function on at most \(a_Gq\) inputs having agreement
less than \(1/2+q^{-G/b_{\rm amp}}\) with every general circuit of size
\(q^{G/b_{\rm amp}}\).
\end{import}
We use \cite[Lemma~3.9]{CLW20} with \(S(q)=q^G\); it is attributed there to
the worst-case-to-average-case amplification of Sudan, Trevisan, and
Vadhan~\cite[Theorem~24]{STV01}. Its constant \(c=b_{\rm amp}\) is fixed
before the size function, while the \(O(q)\) arity and the \(2^{O(q)}\)
construction time may depend on \(S\), hence on \(G\). We state it only
for \(G\ge b_{\rm amp}\), so that \(S(q)=q^G\ge q^{b_{\rm amp}}\);
every use below has \(G&gt;b_{\rm amp}\). Every use below
fixes \(G\) first. We apply this input only in the branches where the
source input or an outer PCP oracle is hard for \emph{general} circuits.
</pre>

<b>Paper v2, lines 4753–4755</b> ([paper/paper.tex](../paper/paper.tex#L4753-L4755))

<pre>
\Cref{imp:ae-amplification}, amplification &amp;
\cite[Lemma~3.9]{CLW20}, from \cite[Theorem~24]{STV01} &amp;
Verbatim at \(S(q)=q^G\), stated only for \(G\ge b_{\rm amp}\): the exponent \(b_{\rm amp}\) is absolute and the arity factor \(a_G\) depends on \(G\). The Lean proof states it as printed, for every time-constructible \(S\) (see the text after \cref{imp:ae-amplification}).\\
</pre>

</td><td>

[Statement.lean, lines 1567–1573](../Statement.lean#L1567-L1573)

<pre>
/-- Input 8: CLW20 Lemma 3.9 with "time-constructible" in the standard multitape sense, the same
`TimeConstructible` as input 7 (`CLW20Theorem113.TimeConstructible`: a multitape machine computes the binary `S(n)`
from unary `n` within `C·(S(n)+1)` steps); the amplifier itself is `Lemma3_9AtTM2`. CLW20, PDF p. 18: "There is a
constant c ≥ 1 such that, for any time-constructible function S(n) and every f ..." -/
def CLW20_Lemma3_9_Multitape : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ S : ℕ → ℕ, NearCubicWires.Bindings.CLW20Theorem113.TimeConstructible S →
    Nonempty (NearCubicWires.Bindings.CLW20Lemma39TM2.Lemma3_9AtTM2 c S)
</pre>

[Statement.lean, lines 998–1016](../Statement.lean#L998-L1016)

<pre>
/-- What the sentence asserts for one constant `c` and one time-constructible `S` (Tier 2). The
construction is a Mathlib TM2 machine. -/
structure Lemma3_9AtTM2 (c : ℝ) (S : ℕ → ℕ) where
  /-- `g` for the input `f` on `n` bits. -/
  g : (n : ℕ) → BoolFunction n → AmplifierOutput
  /-- The hidden constant of `O(n)`. -/
  arityFactor : ℕ
  /-- The hidden onset of `O(n)`. -/
  arityOnset : ℕ
  /-- "every f ... that does not have (general) circuits of size S(n). There is a function
  g : {0,1}^{O(n)} → {0,1} that cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size
  S(n)^{1/c}." -/
  amplifies : ∀ (n : ℕ) (f : BoolFunction n), ¬ HasCircuitOfSize f (S n) →
    (arityOnset ≤ n → (g n f).arity ≤ arityFactor * n) ∧
    CannotBeApproximated (g n f).function
      ((S n : ℝ) ^ (-(1 : ℝ) / c)) ((S n : ℝ) ^ ((1 : ℝ) / c))
  /-- "Furthermore, given the 2^n-length truth table of f, the truth table of g can be
  constructed in 2^{O(n)} time." (Tier 2: Mathlib's TM2 model.) -/
  construction : TruthTableConstructionTM2 g
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 18</b>
<pre>
every f : {0, 1}^n → {0, 1} that does not have
(general) circuits of size S(n).
</pre>

<b>CLW20, PDF p. 15</b>
<pre>
We assume knowledge of basic complexity theory (see [AB09, Gol08] for excellent references).
</pre>

CLW20 defines neither circuits nor their size; it refers to these textbooks. Lean
reads size as the number of nodes, inputs and constants included (item 4 below).

</td><td>

[Statement.lean, lines 927–929](../Statement.lean#L927-L929)

<pre>
/-- "f ... has (general) circuits of size s": some circuit of size at most `s` computes `f`. -/
def HasCircuitOfSize {n : ℕ} (f : BoolFunction n) (s : ℕ) : Prop :=
  ∃ circuit : BooleanCircuit n, circuit.size ≤ s ∧ ∀ x, circuit.eval x = f x
</pre>

[Statement.lean, lines 211–220](../Statement.lean#L211-L220)

<pre>
/-- General Boolean circuits (fan-in-two AND and OR, NOT, constants and inputs): finite DAGs with a topological
node order. Their size counts DAG nodes, so a shared subcircuit counts once (it is not the size of the unfolded
formula); see `BooleanCircuit.size`. -/
structure BooleanCircuit (n : ℕ) where
  nodes : List (BooleanNode n)
  output : Fin nodes.length
  wellFormed :
    ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val
  deriving Repr
</pre>

[Statement.lean, lines 182–191](../Statement.lean#L182-L191)

<pre>
/-- One node in a topologically ordered fan-in-two Boolean DAG.  Child
references are natural-number node addresses; `BooleanCircuit.wellFormed`
requires every child to precede the node that uses it. -/
inductive BooleanNode (n : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  deriving Repr
</pre>

[Statement.lean, lines 193–199](../Statement.lean#L193-L199)

<pre>
def BooleanNode.WellFormedAt {n : ℕ} (index : ℕ) :
    BooleanNode n → Prop
  | .const _ =&gt; True
  | .input _ =&gt; True
  | .not child =&gt; child &lt; index
  | .and left right =&gt; left &lt; index ∧ right &lt; index
  | .or left right =&gt; left &lt; index ∧ right &lt; index
</pre>

[Statement.lean, lines 201–209](../Statement.lean#L201-L209)

<pre>
def BooleanNode.eval {n : ℕ} (input : BitInput n)
    (prior : Array Bool) : BooleanNode n → Bool
  | .const value =&gt; value
  | .input index =&gt; input index
  | .not child =&gt; !(prior[child]?.getD false)
  | .and left right =&gt;
      prior[left]?.getD false &amp;&amp; prior[right]?.getD false
  | .or left right =&gt;
      prior[left]?.getD false || prior[right]?.getD false
</pre>

[Statement.lean, lines 222–225](../Statement.lean#L222-L225)

<pre>
def BooleanCircuit.values {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Array Bool :=
  circuit.nodes.foldl
    (fun prior node =&gt; prior.push (node.eval input prior)) #[]
</pre>

[Statement.lean, lines 227–229](../Statement.lean#L227-L229)

<pre>
def BooleanCircuit.eval {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Bool :=
  (circuit.values input)[circuit.output.val]?.getD false
</pre>

[Statement.lean, lines 231–233](../Statement.lean#L231-L233)

<pre>
/-- The number of nodes, input and constant nodes included (the circuit's vertex count). -/
def BooleanCircuit.size {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  circuit.nodes.length
</pre>

[Statement.lean, line 165](../Statement.lean#L165)

<pre>
abbrev BoolFunction (n : ℕ) := BitInput n → Bool
</pre>

[Statement.lean, line 163](../Statement.lean#L163)

<pre>
abbrev BitInput (n : ℕ) := Fin n → Bool
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 3</b>
<pre>
We say that a function f : {0, 1}^n → {0, 1} cannot
be (1/2 + ε)-approximated by circuits of type C, if
every circuit from C computes f correctly on less than
(1/2 + ε)2^n of the n-bit inputs.
</pre>

<b>CLW20, PDF p. 17</b>
<pre>
(general) circuits of size s. That is, for all circuit C of size at most s, it holds:
</pre>

CLW20's gloss of “circuits of size s” in its Lemma 3.6: size at most s.

</td><td>

[Statement.lean, lines 931–936](../Statement.lean#L931-L936)

<pre>
/-- CLW20 PDF p.3: "cannot be (1/2 + ε)-approximated by circuits of type C, if every circuit from
C computes f correctly on less than (1/2 + ε)2^n of the n-bit inputs", with "circuits of size s"
read as size at most `s` (PDF p.17). -/
def CannotBeApproximated {m : ℕ} (g : BoolFunction m) (ε s : ℝ) : Prop :=
  ∀ circuit : BooleanCircuit m, (circuit.size : ℝ) ≤ s →
    ((Finset.univ.filter fun x =&gt; circuit.eval x = g x).card : ℝ) &lt; (1 / 2 + ε) * 2 ^ m
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 18</b>
<pre>
Furthermore, given the 2^n-length truth
table of f, the truth table of g can be constructed
in 2^{O(n)} time.
</pre>

The truth tables are written as words: the framed arity, then the
2<sup>arity</sup> values in the order of the inputs' binary codes.

</td><td>

[Statement.lean, lines 986–996](../Statement.lean#L986-L996)

<pre>
/-- TIER 2 ALGORITHMIC CLAUSE. "given the 2^n-length truth table of f, the truth table of g can
be constructed in 2^{O(n)} time": a Mathlib `TM2ComputableInTime` machine from the truth table of
`f` (with its framed arity) to the truth table of `g` (with its framed arity), whose step bound
is at most `2^(timeExponent · n)` from the onset `timeOnset` on. -/
structure TruthTableConstructionTM2 (g : (n : ℕ) → BoolFunction n → AmplifierOutput) where
  machine : Turing.TM2ComputableInTime amplifierInput amplifierOutputWord
    (fun request : AmplifierRequest =&gt; g request.inputArity request.function)
  timeExponent : ℕ
  timeOnset : ℕ
  exponentialTime : ∀ request : AmplifierRequest, timeOnset ≤ request.inputArity →
    machine.time (amplifierInput request).length ≤ 2 ^ (timeExponent * request.inputArity)
</pre>

[Statement.lean, lines 982–984](../Statement.lean#L982-L984)

<pre>
/-- The output word: the framed arity of `g`, then the full truth table of `g`. -/
def amplifierOutputWord (o : AmplifierOutput) : List Bool :=
  RepairOrdinary.frame o.arity.bits ++ boolFunctionTable o.function
</pre>

[Statement.lean, lines 840–842](../Statement.lean#L840-L842)

<pre>
/-- The outer ordinary carrier additionally frames this complete payload. -/
def amplifierInput (request : AmplifierRequest) : List Bool :=
  RepairOrdinary.frame request.inputArity.bits ++ boolFunctionTable request.function
</pre>

[Statement.lean, lines 836–838](../Statement.lean#L836-L838)

<pre>
structure AmplifierOutput where
  arity : ℕ
  function : BoolFunction arity
</pre>

[Statement.lean, lines 311–313](../Statement.lean#L311-L313)

<pre>
structure AmplifierRequest where
  inputArity : ℕ
  function : BoolFunction inputArity
</pre>

[Statement.lean, lines 288–290](../Statement.lean#L288-L290)

<pre>
def boolFunctionTable {n : ℕ} (function : BoolFunction n) : List Bool :=
  (List.range (2 ^ n)).map fun code =&gt;
    function fun index =&gt; code.testBit index.val
</pre>

[Statement.lean, lines 530–532](../Statement.lean#L530-L532)

<pre>
def frame : List Bool → List Bool
  | [] =&gt; [false]
  | b :: bs =&gt; true :: b :: frame bs
</pre>

</td></tr>
<tr><td>

<b>CLW20, PDF p. 18</b>
<pre>
for any time-constructible function S(n)
</pre>

Time-constructible, in the standard sense: a multitape machine computes S(n) in
binary from n in unary within O(S(n)) steps. Lean's `TimeConstructible` states exactly this: a multitape program
reads 1<sup>n</sup> and writes the binary digits of S(n) within C·(S(n)+1) steps. It is the definition of input 7
(page 7, row 2), the same Lean declaration; the machine model is in the next row.

</td><td>

[Statement.lean, lines 1031–1035](../Statement.lean#L1031-L1035)

<pre>
/-- "time-constructible" (standard notion, Tier 1 multitape model): a program that, given the word
`1^n`, outputs the binary digits of `T(n)` within `C·(T(n)+1)` steps. -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 &lt; C ∧ Nonempty (OrdinaryWordFunction ℕ (fun n =&gt; List.replicate n true)
    (fun n =&gt; (T n).bits) (fun n =&gt; C * (T n + 1)))
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

**Auxiliary constants.** Lean stores small generated proofs and pattern-matching helpers under the name of the first declaration that needed them, and later declarations reuse them. The statement uses the following ones, whose own declarations are not part of the statement; each is fully determined by its type shown here (a proof of a proposition, or the standard case-analysis principle of the type it matches on).

- `NearCubicWires.CanonicalBinary.bitsValue.match_1` : `(motive : List Bool → Sort u_1) → (x : List Bool) → (Unit → motive []) → ((bit : Bool) → (rest : List Bool) → motive (bit :: rest)) → motive x`, generated by Lean with the declaration at [Statement.lean, lines 143–145](../Statement.lean#L143-L145).

Superscripts are written with `^`: `S(n)^{−1/c}` is S(n)<sup>−1/c</sup>.

**What to check** (a few minutes):

1. The quantifiers: there is a real c ≥ 1 such that for every time-constructible S there is an amplifier
   (`Lemma3_9AtTM2 c S`): a map g from each f on n bits to a function on `arity` bits, a factor and an onset for
   O(n), and a construction machine. Everything but c may depend on S, as in the lemma. Time-constructible is the
   same clock notion as input 7: `TimeConstructible` is the very declaration page 7 prints (a multitape program
   computes the binary digits of S(n) from 1<sup>n</sup> within C·(S(n)+1) steps).
2. For every f on n bits with no circuit of size S(n) (`HasCircuitOfSize`): the arity of g is at most
   arityFactor · n from the onset on (g : {0, 1}<sup>O(n)</sup> → {0, 1}), and g cannot be
   (1/2 + S(n)<sup>−1/c</sup>)-approximated by circuits of size S(n)<sup>1/c</sup>.
3. General circuits (`BooleanCircuit`): fan-in-two AND and OR gates, NOT gates, constants and inputs, in
   topological order. “Cannot be (1/2 + ε)-approximated by circuits of size s” (`CannotBeApproximated`) is CLW20's
   definition on PDF p. 3: every circuit of size at most s agrees with g on fewer than (1/2 + ε)2<sup>m</sup>
   inputs. “Size s” means size at most s, as CLW20 glosses it in Lemma 3.6 (PDF p. 17, quoted above).
4. Circuit size, a documented reading. CLW20 defines neither circuits nor their size and refers to textbooks
   (PDF p. 15, quoted above). Lean's `size` is `nodes.length`: every node counts, the input nodes and the constant
   nodes included, which is the vertex count of the circuit as a graph (the doc comments of `BooleanCircuit` and
   `BooleanCircuit.size` say so). A convention that counts only the AND, OR and NOT gates gives sizes smaller by
   at most n + 2, because a circuit needs at most one node per input and two constants; for large S the
   existential constant c absorbs that difference. Small S need a separate look. CLW20 writes n ≤ T(n) next to
   “time-constructible” where it needs it (Theorem 1.13, page 7); Lemma 3.9 has no such clause, and neither has
   Lean's `TimeConstructible`. So input 8 also covers S with S(n) < n, and if the lemma is read as speaking only of
   S(n) ≥ n, the input still holds at those lengths: let g be parity on n bits. A circuit of size at most
   S(n)<sup>1/c</sup> ≤ S(n) < n has fewer than n nodes, so it does not read some input bit and agrees with parity on
   exactly half of the 2<sup>n</sup> inputs, fewer than (1/2 + S(n)<sup>−1/c</sup>)·2<sup>n</sup>. If S(n) = 0, the
   size bound is 0<sup>1/c</sup> = 0 and no circuit has size 0 (every circuit has an output node), so the condition
   holds vacuously. At the lengths with S(n) ≥ n, the lemma applied to max(S(n), n), which is time-constructible
   when S is, supplies g. This reading is an argument, not a theorem checked by Lean. The proof applies the lemma
   only at S(n) = n<sup>2<sup>D</sup></sup> (item 6), where n + 2 is of lower order.
5. The construction: a Mathlib TM2 machine that maps the framed n and the 2<sup>n</sup>-length truth table of f
   to the framed arity and the truth table of g, within 2<sup>timeExponent · n</sup> steps from an onset on.
   2<sup>O(n)</sup> time, which is polynomial in the length of the truth table, is the same class for TM2 machines
   as for multitape and random-access machines (see the mapping README, “Models”).
6. Paper v2 uses the lemma only at S(q) = q<sup>G</sup> for one fixed G ≥ b<sub>amp</sub> (lines 2341–2348). The proof applies the
   lemma at S(n) = n<sup>2<sup>D</sup></sup>, a q<sup>G</sup>, as paper v2 does, with D ≥ 1 fixed before n; it
   builds the multitape clock of n<sup>2<sup>D</sup></sup> ([`powClock`](../Proof/Gates/Main/Amplifier.lean#L162), in [`Proof/Gates/Main/Amplifier.lean`](../Proof/Gates/Main/Amplifier.lean)). It then moves
   the conclusion to the size (n+1)<sup>2<sup>D</sup></sup> − 1 that its consumer uses, with the constant doubled
   from c to 2c ([`transfer`](../Proof/Gates/Main/Amplifier.lean#L126), in [`Proof/Gates/Main/Amplifier.lean`](../Proof/Gates/Main/Amplifier.lean)): the hardness hypothesis carries over because
   n<sup>K</sup> ≤ (n+1)<sup>K</sup> − 1 (K = 2<sup>D</sup>), and the inapproximability because
   (n+1)<sup>K</sup> − 1 ≤ n<sup>2K</sup> for n ≥ 2; at n = 0 both sizes are 0, and n = 1 is vacuous because
   every one-bit function has a circuit of at most two nodes. This is a theorem proved in Lean, not an assumption;
   the statement itself quantifies over every time-constructible S, as the lemma does.

**Documented deviations:** none from the printed statement. **Documented reading:** circuit size is the node
count, inputs and constants included (item 4), a term CLW20 leaves to its textbooks.

**Class:** literal: CLW20's claim under the readings documented on this page (circuit size as the node count;
time-constructibility in the multitape model of input 7; the construction as a Mathlib TM2 machine).
