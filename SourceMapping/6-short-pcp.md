# 6. Short PCP as an oracle circuit: Murray–Williams (SIAM J. Comput. 2020), Section 5 (paper v2 `imp:short-pcp`)

[Mapping index](README.md) · input 6 of 9 · field `shortPCP` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `shortPCP` of `NineInputs`). The other rows
show every definition that statement uses: all 42 declarations of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. Murray and Williams state this form of the
short PCP of Ben-Sasson and Viola in the proof of their Theorem 1.4. The verifier V is a multitape machine; the
algorithm A that outputs the oracle circuit is a machine of Mathlib's standard `Turing.TM2` model, polynomial time
in the length of x and of T(n) in binary.

**Source.** C. D. Murray, R. R. Williams, “Circuit Lower Bounds for Nondeterministic Quasi-Polytime from a New Easy Witness Lemma”, SIAM Journal on Computing 49(5), STOC18-300–STOC18-322 (2020), DOI 10.1137/18M1195887; the published version, open-access copy in MIT's repository DSpace (https://hdl.handle.net/1721.1/134017), [https://dspace.mit.edu/server/api/core/bitstreams/fd66c806-f889-483b-ba4c-9ee9e99e2228/content](https://dspace.mit.edu/server/api/core/bitstreams/fd66c806-f889-483b-ba4c-9ee9e99e2228/content). Page numbers refer to that PDF, SHA-256 `b633f81dc40dc20ca011cdedf29bb43b290fa2ed678bd6628d84646267ca2fec`. The statement is in Section 5, in the proof of Theorem 1.4, on the journal's
pp. STOC18-316–STOC18-317, which are PDF pp. 18–19 (the PDF's first page is MIT's cover sheet). Murray
and Williams credit the construction to Ben-Sasson and Viola (footnote 5, quoted below; their reference [BSV14] is
the conference version): E. Ben-Sasson, E. Viola, “Short PCPs with projection queries”, ECCC report TR14-017 (2014), [https://eccc.weizmann.ac.il/report/2014/017/download/](https://eccc.weizmann.ac.il/report/2014/017/download/). Page numbers refer to that PDF, SHA-256 `5e2dba9087704b01e238477b815d9871dc9462f319fc9ddd4f463c5590386d71`. That paper's Theorem 1.1 as printed is not an input; see
**Why not CLW20 Lemma 3.10** below.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>MW20, PDF p. 18</b>
<pre>
In particular, for every verifier algorithm V(x, y) running in time T(n) ≥ n, they give
an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0, 1}^n, outputs
an oracle circuit C^O_x with the following properties:^5
• C^O_x has ℓ = log_2(T(n)) + O(log log T(n)) inputs, poly(n, log T(n)) size, and
each copy of the oracle gate O in C^O_x has ℓ inputs as well.
…
^5This is not formally stated in their article, but it is immediate from their Theorem 1.1.
</pre>

<b>MW20, PDF p. 19</b>
<pre>
• If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle
O : {0, 1}^ℓ → {0, 1} such that C^O_x is unsatisfiable.
• If V(x, y) rejects on all y of length T(n), then for every oracle O : {0, 1}^ℓ →
{0, 1}, C^O_x has at least 2^ℓ · (1 − 1/n) satisfying assignments.
</pre>

<b>Paper v2, lines 2185–2202</b> ([paper/paper.tex](../paper/paper.tex#L2185-L2202))

<pre>
\begin{import}[Short PCP, in the form of Murray--Williams]\label{imp:short-pcp}
In particular, for every verifier algorithm \(V(x,y)\) running in time
\(T(n)\ge n\), where \(T(n)\) is computable from \(n\) in
\(\poly(n,\log T(n))\) time, there is an algorithm \(A\) running in
\(\poly(n,\log T(n))\) time which, given \(x\in\{0,1\}^n\), outputs an
oracle circuit \(C^O_x\) with the following properties:
\begin{itemize}
\item \(C^O_x\) has \(\ell=\log_2(T(n))+O(\log\log T(n))\) inputs,
\(\poly(n,\log T(n))\) size, and each copy of the oracle gate \(O\) in
\(C^O_x\) has \(\ell\) inputs as well.
\item If there is a \(y\) of length \(T(n)\) such that \(V(x,y)\)
accepts, then there is an oracle \(O:\{0,1\}^\ell\to\{0,1\}\) such that
\(C^O_x\) is unsatisfiable.
\item If \(V(x,y)\) rejects on all \(y\) of length \(T(n)\), then for
every oracle \(O:\{0,1\}^\ell\to\{0,1\}\), \(C^O_x\) has at least
\(2^\ell\cdot(1-1/n)\) satisfying assignments.
\end{itemize}
\end{import}
</pre>

<b>Paper v2, lines 2203–2229</b> ([paper/paper.tex](../paper/paper.tex#L2203-L2229))

<pre>
This is the statement of Murray and Williams~\cite[Section~5, in the
proof of Theorem~1.4, pp.~STOC18-316--STOC18-317]{MW20}, quoted verbatim
except that ``they give an algorithm'' reads ``there is an algorithm'',
and that the computability of \(T\) is stated. Its opening ``In
particular'' refers to their preceding sentence, that the verifier of
Ben-Sasson and Viola ``yields proofs of \(\tilde O(T(n))\) length for all
running times \(T(n)\)''. Murray and Williams leave
the computability hypothesis implicit, but within its time bound the
algorithm \(A\) must output a circuit with
\(\ell=\log_2T(n)+O(\log\log T(n))\) inputs, and hence determine
\(\log T(n)\) to within \(O(\log\log T(n))\); the time
bound to which we apply the input satisfies the hypothesis
(\cref{lem:succinct-verifier}(i)). They credit the
construction to Ben-Sasson and Viola~\cite{BV14}, noting that it ``is
not formally stated in their article, but it is immediate from their
Theorem~1.1''~\cite[footnote~5]{MW20}. As printed, that theorem
fails at polynomial time bounds unless \(\mathrm{P}=\mathrm{NP}\) (\cref{rem:bv14-printed}).
The statement of Murray and Williams is
weaker. Section~4.4 of~\cite{BV14} obtains it from the verifier of
earlier work; we rely instead on our
proof of the case used here (\cref{thm:short-pcp-ours}). The convention is inverted:
\(C^O_x\) is unsatisfiable when the oracle is accepted on every random
string, and its satisfying assignments are the rejecting random strings.
The size bound keeps the dependence on the explicit input length \(n\).
We apply the input once, to one fixed verifier whose explicit inputs are
short descriptions of circuits (\cref{sec:gadget-transfer},
\cref{lem:succinct-verifier}).
</pre>

<b>Paper v2, lines 4741–4746</b> ([paper/paper.tex](../paper/paper.tex#L4741-L4746))

<pre>
\Cref{imp:short-pcp}, short PCP &amp;
\cite[Section~5, proof of Theorem~1.4, and footnote~5]{MW20}, credited there to \cite[Theorem~1.1]{BV14} &amp;
Verbatim, with ``they give'' read as ``there is'' and the implicit hypothesis that \(T(n)\) is computable in \(\poly(n,\log T(n))\) time stated; applied once, to the succinct verifier of \cref{lem:succinct-verifier}. Proved for multitape verifiers in \cref{thm:short-pcp-ours}. The printed \cite[Theorem~1.1]{BV14} and its restatement \cite[Lemma~3.10]{CLW20} are not used (\cref{rem:bv14-printed}).\\
\Cref{thm:short-pcp-ours}, the short PCP for multitape verifiers &amp;
\cite[Claim~5.1, Theorem~8.1 and its proof, Remarks~8.2 and~11.2, Theorem~11.1, Lemmas~12.23 and C.1--C.8]{BCGT13}; \cite[Theorem~2]{BSCGT13}; \cite[Lemma~4.7]{BV14} &amp;
Adapted: each proximity sub-verifier runs once on a shared random string, and soundness is amplified with a small-bias set (\cref{lem:small-bias,lem:patch-r}, proved here) instead of naive repetition; a Turing-machine-to-RAM simulation (\cref{lem:tm-ram}) is added.\\
</pre>

</td><td>

[Statement.lean, lines 1514–1553](../Statement.lean#L1514-L1553)

<pre>
/-- **Input 6: the short PCP as an oracle circuit (Murray–Williams 2020, Section 5, in the proof of Theorem 1.4,
pp. STOC18-316–STOC18-317, PDF pp. 18–19)**, verbatim:
"for every verifier algorithm V(x, y) running in time T(n) ≥ n, they give an algorithm A running in
poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle circuit C^O_x with the following
properties:
• C^O_x has ℓ = log2(T(n)) + O(log log T(n)) inputs, poly(n, log T(n)) size, and each copy of the oracle
  gate O in C^O_x has ℓ inputs as well.
• If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle O : {0,1}^ℓ → {0,1}
  such that C^O_x is unsatisfiable.
• If V(x, y) rejects on all y of length T(n), then for every oracle O : {0,1}^ℓ → {0,1}, C^O_x has at
  least 2^ℓ · (1 − 1/n) satisfying assignments."
Readings: the hidden constants are chosen after `V` and `T`; `T` is not assumed time-constructible, so `A`
receives `T(n)` in binary with `x`; `A` is a Mathlib polynomial-time TM2 machine (`Turing.TM2ComputableInPolyTime`);
the properties are claimed for `n ≥ 1` ("1/n"); `ℓ = log₂T + O(log log T)` is read as its upper half
`2^ℓ ≤ K·T·L(T)^e` with `L = logScale`. -/
def MW20_OracleCircuitPCP_TM2 : Prop :=
  ∀ (V : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → RunsInTime V T →
  ∃ out : InputRequest → OracleOutput,
    -- "an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle
    -- circuit C^O_x"
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun x : InputRequest =&gt; frame (List.ofFn x.2) ++ frame (T x.1).bits)
      (fun w : List Bool =&gt; w) (fun x =&gt; (out x).word)) ∧
    -- "ℓ = log2(T(n)) + O(log log T(n)) inputs"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      2 ^ (out x).ell ≤ K * T x.1 * logScale (T x.1) ^ e) ∧
    -- "poly(n, log T(n)) size"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      (out x).circuit.size ≤ K * (x.1 + natBitLength (T x.1) + 1) ^ e) ∧
    -- "If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle
    -- O : {0,1}^ℓ → {0,1} such that C^O_x is unsatisfiable."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∃ O : BitInput (out x).ell → Bool, ∀ z, (out x).circuit.eval O z = false) ∧
    -- "If V(x, y) rejects on all y of length T(n), then for every oracle O : {0,1}^ℓ → {0,1}, C^O_x has
    -- at least 2^ℓ · (1 − 1/n) satisfying assignments."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (¬ ∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∀ O : BitInput (out x).ell → Bool,
        (2 : ℝ) ^ (out x).ell * (1 - 1 / (x.1 : ℝ)) ≤ ((out x).satCount O : ℝ))
</pre>

</td></tr>
<tr><td>

<b>MW20, PDF p. 18</b>
<pre>
for every verifier algorithm V(x, y) running in time T(n) ≥ n
</pre>

<b>MW20, PDF p. 19</b>
<pre>
If there is a y of length T(n) such that V(x, y) accepts
</pre>

<b>MW20, PDF p. 19</b>
<pre>
If V(x, y) rejects on all y of length T(n)
</pre>

<b>Paper v2, lines 5253–5261</b> ([paper/paper.tex](../paper/paper.tex#L5253-L5261))

<pre>
\begin{theorem}[\Cref{imp:short-pcp} for multitape verifiers]
\label{thm:short-pcp-ours}
Let \(V(x,y)\) be a deterministic multitape machine and \(T:\N\to\N\) a
function with \(T(n)\ge n\), such that \(V\) halts within \(T(n)\) steps
on every \(x\in\{0,1\}^n\) and every \(y\), and \(T(n)\) is computable
from \(n\) in \(\poly(n,\log T(n))\) steps. Then the conclusion of
\cref{imp:short-pcp} holds for \(V\) and \(T\). In particular it holds
for \(\mathcal V_G\) and \(T_G\) of \cref{lem:succinct-verifier}.
\end{theorem}
</pre>

</td><td>

[Statement.lean, lines 1508–1512](../Statement.lean#L1508-L1512)

<pre>
/-- "every verifier algorithm V(x, y) running in time T(n)": on EVERY `(x, y)` with `|x| = n`, `V` halts within `T(n)`
steps. -/
def RunsInTime (V : OrdinaryVerifier) (T : ℕ → ℕ) : Prop :=
  ∀ n (x : BitInput n) (y : List Bool), ∃ receipt,
    run V.machine (T n) (V.inputTapes (List.ofFn x) y) = some receipt
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

<b>MW20, PDF p. 18</b>
<pre>
outputs
an oracle circuit C^O_x
</pre>

<b>MW20, PDF p. 18</b>
<pre>
each copy of the oracle gate O in C^O_x has ℓ inputs as well.
</pre>

An oracle circuit is a Boolean circuit that may also contain gates computing O. Its
nodes are those of the statement file's general Boolean circuits (constants, inputs, NOT, fan-in-two AND and OR, in
topological order, with a designated output node; `BooleanCircuit`) and oracle gates, each wired to ℓ earlier
nodes. An oracle gate outputs O applied to the values of its ℓ argument nodes.

</td><td>

[Statement.lean, lines 1429–1438](../Statement.lean#L1429-L1438)

<pre>
/-- One node of an oracle circuit on `n` inputs whose oracle gates have `arity` inputs: the nodes of
`BooleanCircuit` (constants, inputs, fan-in-two AND and OR, NOT) and one oracle gate, whose `arity` argument
wires are earlier nodes. -/
inductive OracleNode (n arity : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  | oracle (args : Fin arity → ℕ)
</pre>

[Statement.lean, lines 1440–1447](../Statement.lean#L1440-L1447)

<pre>
/-- Every child of the node at position `index` precedes it. -/
def OracleNode.WellFormedAt {n arity : ℕ} (index : ℕ) : OracleNode n arity → Prop
  | .const _ =&gt; True
  | .input _ =&gt; True
  | .not child =&gt; child &lt; index
  | .and left right =&gt; left &lt; index ∧ right &lt; index
  | .or left right =&gt; left &lt; index ∧ right &lt; index
  | .oracle args =&gt; ∀ j, args j &lt; index
</pre>

[Statement.lean, lines 1449–1458](../Statement.lean#L1449-L1458)

<pre>
/-- The value of a node, given the values `prior` of the earlier nodes; an oracle gate returns
`O` applied to the values of its argument wires. -/
def OracleNode.eval {n arity : ℕ} (O : BitInput arity → Bool) (input : BitInput n)
    (prior : Array Bool) : OracleNode n arity → Bool
  | .const value =&gt; value
  | .input index =&gt; input index
  | .not child =&gt; !(prior[child]?.getD false)
  | .and left right =&gt; prior[left]?.getD false &amp;&amp; prior[right]?.getD false
  | .or left right =&gt; prior[left]?.getD false || prior[right]?.getD false
  | .oracle args =&gt; O fun j =&gt; prior[args j]?.getD false
</pre>

[Statement.lean, lines 1460–1465](../Statement.lean#L1460-L1465)

<pre>
/-- "an oracle circuit C^O": a topologically ordered DAG of `OracleNode`s with a designated output node,
exactly like `BooleanCircuit`, plus oracle gates of arity `arity`. -/
structure OracleCircuit (n arity : ℕ) where
  nodes : List (OracleNode n arity)
  output : Fin nodes.length
  wellFormed : ∀ index : Fin nodes.length, (nodes.get index).WellFormedAt index.val
</pre>

[Statement.lean, lines 1467–1470](../Statement.lean#L1467-L1470)

<pre>
/-- The values of all nodes of `C^O` on `input`. -/
def OracleCircuit.values {n arity : ℕ} (C : OracleCircuit n arity) (O : BitInput arity → Bool)
    (input : BitInput n) : Array Bool :=
  C.nodes.foldl (fun prior node =&gt; prior.push (node.eval O input prior)) #[]
</pre>

[Statement.lean, lines 1472–1475](../Statement.lean#L1472-L1475)

<pre>
/-- `C^O(input)`. -/
def OracleCircuit.eval {n arity : ℕ} (C : OracleCircuit n arity) (O : BitInput arity → Bool)
    (input : BitInput n) : Bool :=
  (C.values O input)[C.output.val]?.getD false
</pre>

[Statement.lean, lines 1492–1496](../Statement.lean#L1492-L1496)

<pre>
/-- "an oracle circuit C^O_x" with "ℓ inputs", "each copy of the oracle gate O in C^O_x has ℓ inputs as
well": the number `ℓ` and the circuit. -/
structure OracleOutput where
  ell : ℕ
  circuit : OracleCircuit ell ell
</pre>

</td></tr>
<tr><td>

<b>MW20, PDF p. 18</b>
<pre>
C^O_x has ℓ = log_2(T(n)) + O(log log T(n)) inputs, poly(n, log T(n)) size
</pre>

</td><td>

[Statement.lean, lines 1477–1479](../Statement.lean#L1477-L1479)

<pre>
/-- The size: the number of nodes (input, constant and oracle nodes included), as `BooleanCircuit.size`. -/
def OracleCircuit.size {n arity : ℕ} (C : OracleCircuit n arity) : ℕ :=
  C.nodes.length
</pre>

[Statement.lean, lines 235–236](../Statement.lean#L235-L236)

<pre>
/-- `L(n) = ⌈log₂(n+2)⌉`, computed exactly on naturals. -/
def logScale (n : ℕ) : ℕ := Nat.clog 2 (n + 2)
</pre>

[Statement.lean, line 61](../Statement.lean#L61)

<pre>
def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1
</pre>

</td></tr>
<tr><td>

<b>MW20, PDF p. 19</b>
<pre>
C^O_x is unsatisfiable
</pre>

<b>MW20, PDF p. 19</b>
<pre>
C^O_x has at least 2^ℓ · (1 − 1/n) satisfying assignments.
</pre>

<b>MW20, PDF p. 19</b>
<pre>
Note the oracle O acts as a witness for the PCP verifier which runs the above trans-
formation on x, and checks whether C^O_x is unsatisfiable or not by guessing random
inputs to C^O_x.
</pre>

</td><td>

[Statement.lean, lines 1504–1506](../Statement.lean#L1504-L1506)

<pre>
/-- The number of satisfying assignments of `C^O`. -/
def OracleOutput.satCount (o : OracleOutput) (O : BitInput o.ell → Bool) : ℕ :=
  (Finset.univ.filter fun z : BitInput o.ell =&gt; o.circuit.eval O z = true).card
</pre>

</td></tr>
<tr><td>

<b>MW20, PDF p. 18</b>
<pre>
they give
an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0, 1}^n, outputs
an oracle circuit C^O_x
</pre>

The output format is not fixed by the paper. A writes ℓ, the number of nodes, the
code of each node in order, then the address of the output node, every number a self-delimiting binary word
(`natWord`). A node's code is a tag (0 constant, 1 input, 2 NOT, 3 AND, 4 OR) and two numbers, 0 when unused; an
oracle gate is tag 5 and the addresses of its ℓ argument nodes. A reads x and T(n) in binary, each framed, and is a
polynomial-time machine of Mathlib's `Turing.TM2ComputableInPolyTime`.

</td><td>

[Statement.lean, lines 1498–1502](../Statement.lean#L1498-L1502)

<pre>
/-- The output word: `ℓ` (the number of inputs and the oracle arity), the number of nodes, the node words in order,
then the output address. -/
def OracleOutput.word (o : OracleOutput) : List Bool :=
  natWord o.ell ++ natWord o.circuit.nodes.length ++ o.circuit.nodes.flatMap oracleNodeWord ++
    natWord o.circuit.output.val
</pre>

[Statement.lean, lines 1481–1490](../Statement.lean#L1481-L1490)

<pre>
/-- The word of a node, in the native three-field form of the Boolean nodes (tag, then two numbers, `0` when unused:
`0` constant, `1` input, `2` NOT, `3` AND, `4` OR); an oracle gate is tag `5` followed by its `arity` argument wires.
Every field is a self-delimiting `natWord`. -/
def oracleNodeWord {n arity : ℕ} : OracleNode n arity → List Bool
  | .const value =&gt; natWord 0 ++ natWord value.toNat ++ natWord 0
  | .input index =&gt; natWord 1 ++ natWord index.val ++ natWord 0
  | .not child =&gt; natWord 2 ++ natWord child ++ natWord 0
  | .and left right =&gt; natWord 3 ++ natWord left ++ natWord right
  | .or left right =&gt; natWord 4 ++ natWord left ++ natWord right
  | .oracle args =&gt; natWord 5 ++ (List.ofFn fun j =&gt; natWord (args j)).flatten
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

[Statement.lean, line 630](../Statement.lean#L630)

<pre>
abbrev InputRequest := Σ n : ℕ, BitInput n
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
<tr><td>

Encodings. The paper fixes no tape layout or binary code for these objects. The remaining definitions the
statement uses are printed here, so that every definition it depends on appears on this page.

</td><td>

[Statement.lean, line 163](../Statement.lean#L163)

<pre>
abbrev BitInput (n : ℕ) := Fin n → Bool
</pre>

</td></tr>
</table>

**Auxiliary constants.** Lean stores small generated proofs and pattern-matching helpers under the name of the first declaration that needed them, and later declarations reuse them. The statement uses the following ones, whose own declarations are not part of the statement; each is fully determined by its type shown here (a proof of a proposition, or the standard case-analysis principle of the type it matches on).

- `NearCubicWires.Bindings.CLW20Lemma39.CannotBeApproximated._proof_1` : `(1 + 1).AtLeastTwo`, generated by Lean with the declaration at [Statement.lean, lines 931–936](../Statement.lean#L931-L936).
- `NearCubicWires.CanonicalBinary.bitsValue.match_1` : `(motive : List Bool → Sort u_1) → (x : List Bool) → (Unit → motive []) → ((bit : Bool) → (rest : List Bool) → motive (bit :: rest)) → motive x`, generated by Lean with the declaration at [Statement.lean, lines 143–145](../Statement.lean#L143-L145).

Superscripts and subscripts are written with `^` and `_`: `C^O_x` is C<sub>x</sub><sup>O</sup>,
`log_2` is log₂, `2^ℓ` is 2<sup>ℓ</sup>, and `^5` marks footnote 5. The bullets on PDF p. 19 continue the list that
begins on PDF p. 18.

**What to check** (a few minutes):

1. The hypotheses: V is any multitape verifier that halts within T(n) steps on every input (x, y) with |x| = n
   (`RunsInTime`), and T(n) ≥ n. Paper v2 proves the statement for such verifiers (`thm:short-pcp-ours`, quoted in
   the second row), with T(n) computable; item 9 explains why the Lean statement needs no such hypothesis.
2. V(x, y) accepts: some run of the verifier on input x and witness y halts in an accepting state
   (`Verifier.accepts`); y ranges over the words of length T(n). Since V halts on every input, “V(x, y) rejects on
   all y of length T(n)” is the negation: no such y makes V accept.
3. The output: an oracle circuit with ℓ inputs whose oracle gates have ℓ inputs as well (`OracleOutput`, one ℓ for
   both). Its nodes are constants, inputs, NOT, fan-in-two AND and OR, and oracle gates, each wired to earlier nodes
   (`OracleNode`, `OracleNode.WellFormedAt`), with a designated output node; C<sup>O</sup><sub>x</sub>(z) is
   `OracleCircuit.eval`, and the size is the number of nodes (`OracleCircuit.size`), as for the Boolean circuits of
   inputs 8 and 9.
4. ℓ = log₂ T(n) + O(log log T(n)) is read as its upper half: constants K and e with
   2<sup>ℓ</sup> ≤ K · T(n) · L(T(n))<sup>e</sup>, where L(m) = ⌈log₂(m + 2)⌉ (`logScale`); taking logarithms,
   ℓ ≤ log₂ T(n) + O(log log T(n)). The lower half is not claimed.
5. The size poly(n, log T(n)) is at most K · (n + b + 1)<sup>e</sup>, where b is the number of binary digits of T(n)
   (`natBitLength`).
6. Completeness and soundness are as printed, in the printed convention: if some y of length T(n) makes V accept,
   some oracle O makes C<sup>O</sup><sub>x</sub> unsatisfiable (false at every z); if none does, then for every
   oracle O at least 2<sup>ℓ</sup> · (1 − 1/n) inputs z satisfy C<sup>O</sup><sub>x</sub>
   (`OracleOutput.satCount`, compared in the reals). As Murray and Williams note, the satisfying assignments are the
   random strings on which the PCP verifier rejects.
7. The properties are claimed for n ≥ 1: at n = 0 the bound 1 − 1/n has no meaning.
8. The quantifier order: the constants K and e of items 4 and 5, and the polynomial bounding A's running time, are
   chosen after V and T (for all V and T there are A, K and e), which is how Murray and Williams' O(·) and poly(·)
   read; paper v2 says so in the proof of `thm:short-pcp-ours` ([lines 5292–5293](../paper/paper.tex#L5292-L5293)).
9. The algorithm A: a polynomial-time Mathlib TM2 machine whose input is x and T(n) in binary, each framed, and
   whose output is the word of item 10. Murray and Williams leave the computability of T implicit; paper v2 states
   it as a hypothesis (T(n) computable from n in poly(n, log T(n)) time), and its proof of `thm:short-pcp-ours`
   uses it only to compute T(n) and quantities derived from it. Here A is given T(n), so the statement needs no
   such hypothesis. Wherever Murray and Williams' statement applies, it implies this one: an algorithm as they state
   it may ignore the extra input, whose length is O(log T(n)). For a T that is not computable within those bounds,
   their statement may fail as written, but this one still holds, because paper v2's proof uses T only through
   T(n), which A is given. So this is an adaptation of their statement, not a transcription. Polynomial time is the
   same class for TM2 machines as for
   multitape and random-access machines (see the mapping README, “Models”).
10. The output word is the statement file's native framed format (the row with A's quotation): self-delimiting
    numbers, and the node codes of the Boolean circuits with tag 5 added for oracle gates. The paper fixes no
    format; the usual codes of a circuit convert into this one in polynomial time.

**Why not CLW20 Lemma 3.10.** Earlier versions of the paper and of this statement took the short PCP in the form of
Ben-Sasson and Viola's Theorem 1.1, restated as CLW20 Lemma 3.10: projection query circuits, t = poly(r) queries
decided by a 3CNF, 2<sup>r</sup> ≤ T · polylog T, perfect completeness and soundness n<sup>−10</sup>. As printed,
that form cannot hold as stated: applied to a verifier for SAT that runs in time O(n<sup>2</sup>), it
would map SAT instances of size n to SAT instances of size polylog n in polynomial time, and iterating the map would
decide SAT in polynomial time (paper v2, `rem:bv14-printed`, [lines 2244–2263](../paper/paper.tex#L2244-L2263)). This statement uses the
weaker form of Murray and Williams instead, which their footnote 5 calls immediate from the same theorem (paper v2
discusses the derivation in the paragraph quoted in the first row). Paper v2 proves this form for deterministic
multitape verifiers with computable time bounds in its Appendix D (`app:short-pcp-proof`; the theorem
`thm:short-pcp-ours` is quoted in the second row), from the PCP of Ben-Sasson, Chiesa, Genkin and Tromer (BCGT13),
their reduction from random-access machines (BSCGT13) and a randomness-efficient soundness amplification
(`lem:patch-r`). The Lean proof does not use
that appendix: input 6 is an assumption of the main theorem, as are the other eight inputs.

**Documented deviations:** none. Items 4, 7 and 9 claim less than the printed statement, and item 10 is an
encoding.

**Class:** adapted: A is also given T(n) in binary, so no computability hypothesis on T is needed (item 9); the verifier V is a multitape machine and the algorithm A a Mathlib TM2 machine.
