# 9. Three-query PCP of proximity and linear code: CW19 Lemmas 24 and 27 (paper v2 `imp:three-pcpp`)

[Mapping index](README.md) · input 9 of 9 · field `threeQueryPCPP` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `threeQueryPCPP` of `NineInputs`). The other rows
show every definition that statement uses: all 45 declarations of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. The input is the conjunction
of two published lemmas. Paper v2 derives its pointwise form from them with the code's decoder (lines 2398–2415);
the proof derives the same pointwise form in Lean through a checked relation instead (item 8 below).

**Source.** L. Chen, R. R. Williams, “Stronger Connections Between Circuit Analysis and Circuit Lower Bounds, via PCPs of Proximity”, 34th Computational Complexity Conference (CCC 2019), LIPIcs 137, 19:1–19:43, [https://drops.dagstuhl.de/storage/00lipics/lipics-vol137-ccc2019/LIPIcs.CCC.2019.19/LIPIcs.CCC.2019.19.pdf](https://drops.dagstuhl.de/storage/00lipics/lipics-vol137-ccc2019/LIPIcs.CCC.2019.19/LIPIcs.CCC.2019.19.pdf). Page numbers refer to that PDF, SHA-256 `c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533`.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>CW19, PDF p. 15</b>
<pre>
Lemma 24 (3-query PCPP with perfect completeness).
</pre>

<b>CW19, PDF p. 16</b>
<pre>
Lemma 27. There is a constant δ &gt; 0 such that there
is a constant-rate linear error correcting code ECC
</pre>

The input is the conjunction of these two lemmas, quoted in full in the rows below.

<b>Paper v2, lines 2381–2415</b> ([paper/paper.tex](../paper/paper.tex#L2381-L2415))

<pre>
\begin{import}[Pointwise three-query PCPP]\label{imp:three-pcpp}
There are a rational constant $0&lt;\gamma&lt;1$, a polynomial-time
computable linear encoding $\operatorname{Enc}$, and a polynomial-time
transformation taking a Boolean circuit $D$ on $q$ inputs to a
polynomial-size list of three-literal clauses on variables $Y\cup Z$,
such that the following hold for every $x\in\{0,1\}^q$ with
$Y=\operatorname{Enc}(x)$:
\begin{itemize}
\item If $D(x)=1$, an auxiliary assignment computable in polynomial
time satisfies every clause.
\item If $D(x)=0$, every auxiliary assignment leaves at least a
$\gamma$ fraction of the clauses false.
\end{itemize}
Each systematic coordinate is a parity of input coordinates. The
number of clauses can be taken to be a power of two.
\end{import}

This is the pointwise form of Chen--Williams' perfectly complete
three-query PCPP~\cite[Lemma~24 and Appendix~A]{CW19}, using their
linear code and decoder~\cite[Lemma~27]{CW19}. As in the proof of
\cite[Theorem~5]{CW19}, here is the reduction to the stated form. Take a fixed proximity radius smaller than the
code's decoding radius, totalize the decoder by returning an arbitrary
fixed string on failure, and apply the PCPP to
$\widetilde D(y)=D(\operatorname{Dec}(y))$. If $D(x)=0$, every word sufficiently
close to $\operatorname{Enc}(x)$ decodes to $x$, and is therefore
rejected by $\widetilde D$. Thus $\operatorname{Enc}(x)$ is farther than the
proximity radius from every accepting input of $\widetilde D$, and proximity
soundness applies. If $D(x)=1$, perfect completeness and the efficient
honest-proof procedure of~\cite[Lemma~24]{CW19} apply. The underlying proximity construction
is due to Ben-Sasson, Goldreich, Harsha, Sudan, and
Vadhan~\cite{BGHSV06}. In the constant-size clause conversion in
the proof of \cite[Lemma~24]{CW19}, pad to a power-of-two number of
clauses with tautologies before selecting a clause uniformly. This
preserves perfect completeness and changes only the fixed rejection
constant. Finally choose a smaller rational $\gamma$ if necessary.
</pre>

<b>Paper v2, lines 4756–4758</b> ([paper/paper.tex](../paper/paper.tex#L4756-L4758))

<pre>
\Cref{imp:three-pcpp}, three-query PCPP &amp;
\cite[Lemma~24, Appendix~A, Lemma~27, and the proof of Theorem~5]{CW19}; \cite{BGHSV06} &amp;
Adapted: totalized decoder; tautology padding to a power of two; \(\gamma\) rounded down to a rational.\\
</pre>

</td><td>

[Statement.lean, lines 1411–1413](../Statement.lean#L1411-L1413)

<pre>
/-- Input 9: CW19 Lemmas 24 and 27 together. The pointwise form the paper uses is proved from them. -/
def ThreeQuerySourceGroup : Prop :=
  PerfectThreeQueryProximityLiteral ∧ EfficientLinearCodeLiteral
</pre>

</td></tr>
<tr><td>

<b>CW19, PDF p. 15</b>
<pre>
Lemma 24 (3-query PCPP with perfect completeness).
For any constant δ &gt; 0 there is a constant 0 &lt; s &lt; 1,
such that there is a PCP of proximity system for
Circuit-Eval with proximity δ, soundness s, random
bits r = O(log n), and query complexity q = 3.
Moreover, the system satisfies two additional
properties:
(1) Given the random coins, the verifier simply
computes an OR on these 3 queried bits or their
negations, and accepts iff the OR is true.
(2) Given the pair (C, w) ∈ Circuit-Eval, we can
construct a proof π in poly(|C| + |w|) time that makes
V(C) accept with probability 1.
</pre>

<b>CW19, PDF p. 21</b>
<pre>
We can view the verification of V(D) as m = 2^{r(|D|)} = poly(n) many constraints on the
oracle y ◦ π. We can also assume |π| = ℓ = poly(n).
</pre>

From CW19's proof of its Theorem 5, which applies Lemma 24 to a circuit D (items 9
and 10).

</td><td>

[Statement.lean, lines 1393–1409](../Statement.lean#L1393-L1409)

<pre>
/-- CW19 Lemma 24: three queries, OR predicates, proximity soundness,
perfect completeness, and a uniform honest-proof procedure on YES inputs. -/
def PerfectThreeQueryProximityLiteral : Prop :=
  ∀ delta : ℝ, 0 &lt; delta → delta &lt; 1 →
    ∃ s : ℝ, 0 &lt; s ∧ s &lt; 1 ∧
    ∃ output : (C : Circuit) → RawThreeQueryPCPP C.n,
      Nonempty (Turing.TM2ComputableInPolyTime (fun C : Circuit =&gt; C.word)
        (fun word : List Bool =&gt; word) (fun C =&gt; (output C).word)) ∧
      (∃ K e : ℕ, ∀ C,
        (output C).proofBits ≤ K * (C.m + 1) ^ e ∧
        2 ^ (output C).randomBits ≤ K * (C.m + 1) ^ e) ∧
      (∀ C input, ProximityFar delta C input →
        ∀ proof, (output C).fraction input proof ≤ s) ∧
      ∃ honest : (p : AcceptedCircuitInput) → BitInput (output p.1).proofBits,
        (∀ p coins, (output p.1).accepts p.2.val (honest p) coins = true) ∧
        Nonempty (Turing.TM2ComputableInPolyTime acceptedCircuitInputWord
          (fun word : List Bool =&gt; word) (fun p =&gt; List.ofFn (honest p)))
</pre>

[Statement.lean, lines 1363–1366](../Statement.lean#L1363-L1366)

<pre>
structure RawThreeQueryPCPP (n : ℕ) where
  proofBits : ℕ
  randomBits : ℕ
  clause : Fin (2 ^ randomBits) → Fin 3 → Literal (n + proofBits)
</pre>

[Statement.lean, lines 1368–1371](../Statement.lean#L1368-L1371)

<pre>
def RawThreeQueryPCPP.accepts {n : ℕ} (P : RawThreeQueryPCPP n)
    (input : BitInput n) (proof : BitInput P.proofBits)
    (coins : Fin (2 ^ P.randomBits)) : Bool :=
  (List.ofFn fun i : Fin 3 =&gt; (P.clause coins i).eval (Fin.addCases input proof)).any id
</pre>

[Statement.lean, lines 1373–1376](../Statement.lean#L1373-L1376)

<pre>
noncomputable def RawThreeQueryPCPP.fraction {n : ℕ} (P : RawThreeQueryPCPP n)
    (input : BitInput n) (proof : BitInput P.proofBits) : ℝ :=
  ((Finset.univ.filter fun coins =&gt; P.accepts input proof coins = true).card : ℝ) /
    (2 ^ P.randomBits : ℝ)
</pre>

[Statement.lean, line 1388](../Statement.lean#L1388)

<pre>
abbrev AcceptedCircuitInput := Σ C : Circuit, {x : BitInput C.n // C.D.eval x = true}
</pre>

[Statement.lean, lines 1390–1391](../Statement.lean#L1390-L1391)

<pre>
def acceptedCircuitInputWord (p : AcceptedCircuitInput) : List Bool :=
  p.1.word ++ List.ofFn p.2.val
</pre>

[Statement.lean, lines 1378–1382](../Statement.lean#L1378-L1382)

<pre>
def RawThreeQueryPCPP.word {n : ℕ} (P : RawThreeQueryPCPP n) : List Bool :=
  RepairOrdinary.frame P.proofBits.bits ++ RepairOrdinary.frame P.randomBits.bits ++
    (List.ofFn fun coins : Fin (2 ^ P.randomBits) =&gt;
      (List.ofFn fun i : Fin 3 =&gt;
        RepairOrdinary.frame (literalCode (P.clause coins i)).bits).flatten).flatten
</pre>

[Statement.lean, lines 258–260](../Statement.lean#L258-L260)

<pre>
inductive Literal (arity : ℕ) where
  | positive (index : Fin arity)
  | negative (index : Fin arity)
</pre>

[Statement.lean, lines 262–266](../Statement.lean#L262-L266)

<pre>
def Literal.eval {arity : ℕ} (literal : Literal arity)
    (assignment : BitInput arity) : Bool :=
  match literal with
  | .positive index =&gt; assignment index
  | .negative index =&gt; !(assignment index)
</pre>

[Statement.lean, lines 627–628](../Statement.lean#L627-L628)

<pre>
def literalCode {t : ℕ} (l : Literal t) : ℕ :=
  match l with | .positive i =&gt; 2*i.val | .negative i =&gt; 2*i.val+1
</pre>

</td></tr>
<tr><td>

<b>CW19, PDF p. 15</b>
<pre>
Definition 20 (Probabilistic Checkable Proofs of
Proximity (PCP of proximity, or PCPP)).
…
If (x, y) ∈ L, there is a proof π such that V(x) accepts
oracle y ◦ π with probability 1.
If y is δ(|x|)-far from L(x) := {z : (x, z) ∈ L}, then for
all proofs π, V(x) accepts oracle y ◦ π with probability
at most s(|x|).
V(x) tosses r(|x|) random coins, and makes at most
q(|x|) non-adaptive queries.
</pre>

<b>CW19, PDF p. 11</b>
<pre>
we are saying that if x has hamming distance more
than δn from all y that satisfy E
</pre>

<b>CW19, PDF p. 13</b>
<pre>
The Circuit Evaluation Problem (Circuit-Eval) is the
language of pairs {(C, w)} such that when C is a
general fan-in-2 circuit and w is a Boolean input,
(C, w) ∈ Circuit-Eval if and only if C(w) = 1.
</pre>

</td><td>

[Statement.lean, lines 1384–1386](../Statement.lean#L1384-L1386)

<pre>
def ProximityFar (delta : ℝ) (C : Circuit) (input : BitInput C.n) : Prop :=
  ∀ accepted : BitInput C.n, C.D.eval accepted = true →
    delta ≤ relativeHamming input accepted
</pre>

[Statement.lean, lines 1324–1325](../Statement.lean#L1324-L1325)

<pre>
noncomputable def relativeHamming {n : ℕ} (x y : BitInput n) : ℝ :=
  ((Finset.univ.filter fun i =&gt; x i ≠ y i).card : ℝ) / n
</pre>

[Statement.lean, lines 954–958](../Statement.lean#L954-L958)

<pre>
/-- "a circuit D on n inputs of size m ≥ n". -/
structure Circuit where
  n : ℕ
  D : BooleanCircuit n
  sizeAtLeast : n ≤ D.size
</pre>

[Statement.lean, lines 960–961](../Statement.lean#L960-L961)

<pre>
/-- The size `m` of `D`: its number of nodes. -/
def Circuit.m (C : Circuit) : ℕ := C.D.size
</pre>

[Statement.lean, lines 963–965](../Statement.lean#L963-L965)

<pre>
/-- Tier 1: the circuit as a bit word, `n` and then the code of `D`. -/
def Circuit.word (C : Circuit) : List Bool :=
  natWord C.n ++ (encodeBooleanCircuit C.D).bits
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

</td></tr>
<tr><td>

<b>CW19, PDF p. 16</b>
<pre>
Lemma 27. There is a constant δ &gt; 0 such that there
is a constant-rate linear error correcting code ECC
with minimum relative distance δ, an efficient encoder
Enc and an efficient decoder Dec recovering error up to
c1 · δ, where c1 is a universal constant. Moreover,
each bit of the codeword depends on at most n/2 bits
of the input.
</pre>

</td><td>

[Statement.lean, lines 1347–1361](../Statement.lean#L1347-L1361)

<pre>
/-- CW19 Lemma 27's constant-rate linear code, in explicit support form.
The n/2 support claim is stated for n ≥ 2. -/
def EfficientLinearCodeLiteral : Prop :=
  ∃ E : LinearCodeFamily, ∃ distance radius : ℝ,
    0 &lt; radius ∧ radius &lt; distance ∧ distance &lt; 1 ∧
    (∃ K : ℕ, ∀ n, 2 ≤ n → E.length n ≤ K * (n + 1)) ∧
    (∀ n, 2 ≤ n → ∀ i, (E.support n i).card ≤ n / 2) ∧
    (∀ n, 2 ≤ n → ∀ x y : BitInput n, x ≠ y →
      distance ≤ relativeHamming (E.enc n x) (E.enc n y)) ∧
    (∀ n, 2 ≤ n → ∀ x : BitInput n, ∀ y : BitInput (E.length n),
      relativeHamming (E.enc n x) y ≤ radius → E.decoder n y = x) ∧
    Nonempty (Turing.TM2ComputableInPolyTime messageWord
      (fun word : List Bool =&gt; word) (fun p =&gt; List.ofFn (E.enc p.1 p.2.val))) ∧
    Nonempty (Turing.TM2ComputableInPolyTime (codewordWord E)
      (fun word : List Bool =&gt; word) (fun p =&gt; List.ofFn (E.decoder p.1 p.2.val)))
</pre>

[Statement.lean, lines 1327–1330](../Statement.lean#L1327-L1330)

<pre>
structure LinearCodeFamily where
  length : ℕ → ℕ
  support : (n : ℕ) → Fin (length n) → Finset (Fin n)
  decoder : (n : ℕ) → BitInput (length n) → BitInput n
</pre>

[Statement.lean, lines 1332–1334](../Statement.lean#L1332-L1334)

<pre>
noncomputable def LinearCodeFamily.enc (E : LinearCodeFamily)
    (n : ℕ) (x : BitInput n) : BitInput (E.length n) :=
  fun i =&gt; parityOn (E.support n i) x
</pre>

[Statement.lean, lines 268–270](../Statement.lean#L268-L270)

<pre>
noncomputable def parityOn {n : ℕ} (support : Finset (Fin n))
    (input : BitInput n) : Bool :=
  support.toList.foldl (fun parity i =&gt; xor parity (input i)) false
</pre>

[Statement.lean, line 1336](../Statement.lean#L1336)

<pre>
abbrev MessageRequest := Σ n : ℕ, {_x : BitInput n // 2 ≤ n}
</pre>

[Statement.lean, lines 1338–1339](../Statement.lean#L1338-L1339)

<pre>
def messageWord (p : MessageRequest) : List Bool :=
  RepairOrdinary.frame p.1.bits ++ RepairOrdinary.frame (List.ofFn p.2.val)
</pre>

[Statement.lean, lines 1341–1342](../Statement.lean#L1341-L1342)

<pre>
abbrev CodewordRequest (E : LinearCodeFamily) :=
  Σ n : ℕ, {_y : BitInput (E.length n) // 2 ≤ n}
</pre>

[Statement.lean, lines 1344–1345](../Statement.lean#L1344-L1345)

<pre>
def codewordWord (E : LinearCodeFamily) (p : CodewordRequest E) : List Bool :=
  RepairOrdinary.frame p.1.bits ++ RepairOrdinary.frame (List.ofFn p.2.val)
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

[Statement.lean, lines 128–133](../Statement.lean#L128-L133)

<pre>
/-- A zero-terminated list whose cells expose both payload and tail through
two `unpair` instructions. -/
def encodeTaggedList : List ℕ → ℕ
  | [] =&gt; 0
  | value :: rest =&gt;
      Nat.pair 1 (Nat.pair value (encodeTaggedList rest))
</pre>

[Statement.lean, line 135](../Statement.lean#L135)

<pre>
def boolCode (value : Bool) : ℕ := value.toNat
</pre>

[Statement.lean, lines 137–138](../Statement.lean#L137-L138)

<pre>
def encodeBoolList (values : List Bool) : ℕ :=
  encodeBalancedList (values.map boolCode)
</pre>

[Statement.lean, lines 140–141](../Statement.lean#L140-L141)

<pre>
def encodeBits (values : List Bool) : ℕ :=
  encodeBoolList values
</pre>

[Statement.lean, lines 147–149](../Statement.lean#L147-L149)

<pre>
/-- Canonical naturals are explicit little-endian bit lists, never raw machine
integers hidden behind `Encodable`. -/
def encodeNat (value : ℕ) : ℕ := encodeBits value.bits
</pre>

[Statement.lean, line 163](../Statement.lean#L163)

<pre>
abbrev BitInput (n : ℕ) := Fin n → Bool
</pre>

[Statement.lean, lines 292–302](../Statement.lean#L292-L302)

<pre>
def encodeBooleanNode {n : ℕ} : BooleanNode n → ℕ
  | .const value =&gt;
      encodeTaggedList [encodeNat 0, encodeNat value.toNat]
  | .input index =&gt;
      encodeTaggedList [encodeNat 1, encodeNat index.val]
  | .not child =&gt;
      encodeTaggedList [encodeNat 2, encodeNat child]
  | .and left right =&gt;
      encodeTaggedList [encodeNat 3, encodeNat left, encodeNat right]
  | .or left right =&gt;
      encodeTaggedList [encodeNat 4, encodeNat left, encodeNat right]
</pre>

[Statement.lean, lines 304–309](../Statement.lean#L304-L309)

<pre>
/-- Canonical DAG encoding: the topological node list is occurrence-sensitive,
and the distinguished output address is encoded separately. -/
def encodeBooleanCircuit {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  encodeTaggedList
    [encodeBalancedList (circuit.nodes.map encodeBooleanNode),
      encodeNat circuit.output.val]
</pre>

[Statement.lean, lines 508–509](../Statement.lean#L508-L509)

<pre>
def fixedWidthNatBits (width value : ℕ) : List Bool :=
  List.ofFn fun bit : Fin width =&gt; value.testBit bit.val
</pre>

[Statement.lean, lines 511–515](../Statement.lean#L511-L515)

<pre>
/-- A self-delimiting binary word.  Its length prefix makes concatenation of
the variable-width fields unambiguous. -/
def framedNatBits (value : ℕ) : List Bool :=
  List.replicate (natBitLength value) true ++
    false :: fixedWidthNatBits (natBitLength value) value
</pre>

[Statement.lean, lines 530–532](../Statement.lean#L530-L532)

<pre>
def frame : List Bool → List Bool
  | [] =&gt; [false]
  | b :: bs =&gt; true :: b :: frame bs
</pre>

[Statement.lean, line 860](../Statement.lean#L860)

<pre>
def natWord (n : ℕ) : List Bool := framedNatBits n
</pre>

</td></tr>
</table>

**Auxiliary constants.** Lean stores small generated proofs and pattern-matching helpers under the name of the first declaration that needed them, and later declarations reuse them. The statement uses the following ones, whose own declarations are not part of the statement; each is fully determined by its type shown here (a proof of a proposition, or the standard case-analysis principle of the type it matches on).

- `NearCubicWires.CanonicalBinary.bitsValue.match_1` : `(motive : List Bool → Sort u_1) → (x : List Bool) → (Unit → motive []) → ((bit : Bool) → (rest : List Bool) → motive (bit :: rest)) → motive x`, generated by Lean with the declaration at [Statement.lean, lines 143–145](../Statement.lean#L143-L145).
- `NearCubicWires.Bindings.CLW20Lemma39.CannotBeApproximated._proof_1` : `(1 + 1).AtLeastTwo`, generated by Lean with the declaration at [Statement.lean, lines 931–936](../Statement.lean#L931-L936).

**What to check** (about ten minutes):

1. The input is the conjunction of Lemma 24 (`PerfectThreeQueryProximityLiteral`) and Lemma 27
   (`EfficientLinearCodeLiteral`).
2. Lemma 24, for every δ with 0 < δ < 1: there are s with 0 < s < 1 and a map `output` from circuits C to
   verifiers (`RawThreeQueryPCPP`). A verifier has `proofBits` proof bits and r = `randomBits` coins, and for each
   of the 2<sup>r</sup> coin outcomes one clause of three literals over the input bits and the proof bits. A
   polynomial-time Mathlib TM2 machine computes the verifier from the code of C (item 10). There are constants K and e with
   2<sup>r</sup> ≤ K(m+1)<sup>e</sup> and proofBits ≤ K(m+1)<sup>e</sup> for every C, where m is the size of C;
   the first bound is r = O(log n), the second is justified in item 9. Property (1) is `accepts`: on a coin
   outcome the verifier accepts exactly when the OR of the clause's three literal values is true.
3. Proximity soundness: if the input is δ-far from every accepted input of C, measured in relative Hamming distance
   (`ProximityFar`: relative distance at least δ), then every proof is accepted on at most an s fraction of the
   coins (`fraction`). For the boundary case, distance exactly δ, see item 7.
4. Perfect completeness and property (2): for every accepted pair (C, w) an honest proof is accepted on every coin
   outcome, and is computed by a polynomial-time Mathlib TM2 machine from the pair (polynomial time is the same
   class for TM2 machines as for multitape machines; see the mapping README, “Models”).
5. Lemma 27: a linear code family (each codeword bit is the parity of a support set of input bits, `parityOn`)
   with length at most K(n+1) (constant rate), supports of at most n/2 bits, relative distance at least `distance`
   between distinct codewords, and a decoder that recovers every word within relative distance `radius` <
   `distance`; encoder and decoder are polynomial-time Mathlib TM2 machines. The properties are stated for n ≥ 2.
   Over {0, 1}, a linear code is one whose every codeword bit is the parity of a set of input bits. `distance` and
   `radius` are existential, and smaller values only weaken the claims: Lemma 27's δ and c1 · δ give them, for
   example distance = min(δ, 1/2) and radius = min(c1 · δ, distance/2).
6. Circuit-Eval: `Circuit` is a fan-in-two Boolean circuit on n inputs with at least n nodes; its size m is the
   node count. Restricting Lemma 24 to circuits of size at least n only weakens it.
7. The distance boundary. CW19 calls an input δ-far when its Hamming distance from every accepted input is more
   than δn (strict; PDF p. 11, quoted above), while `ProximityFar δ` asks for relative distance at least δ
   (non-strict). So at distance exactly δn the Lean soundness clause applies where the printed one does not. The
   published lemma still implies the Lean one: for a given δ, apply Lemma 24 at δ' = δ/2. Relative distance at
   least δ is more than δ', so the verifier returned for δ' meets the Lean soundness clause at δ, equality
   included. Its soundness constant s is the one for δ'; the input lets s and the size constants depend on δ.
8. How the proof uses the input (not part of the input). Paper v2 applies the PCPP to D(Dec(y)), with the decoder
   totalized, and argues that a word close to Enc(x) decodes to x. The proof instead applies it to a checked
   relation, the circuit that accepts y exactly when y = (x, Enc(x)) for its prefix x and D(x) = 1, and evaluates
   it on the systematic word (x, Enc(x)) ([`threeQuery_of_source`](../Proof/Gates/Gadget/ThreeQuery.lean#L66), in [`Proof/Gates/Gadget/ThreeQuery.lean`](../Proof/Gates/Gadget/ThreeQuery.lean)). If D(x) = 0, every
   accepted word is (x′, Enc(x′)) with x′ ≠ x, and the code distance makes it differ from (x, Enc(x)) in at least
   half the code's relative distance, so proximity soundness applies; if D(x) = 1, perfect completeness and the
   honest proof apply. The decoder of Lemma 27 is not used. Both routes reach the same pointwise statement
   (paper v2 `imp:three-pcpp`), and the Lean route is a theorem checked with the rest of the proof.
9. The size bounds. In Lemma 24, n is the length of the explicit input |x| = |C| (Definition 20: “V(x) tosses
   r(|x|) random coins”), and the code of C has length polynomial in its size m, so r = O(log n) gives
   2<sup>r</sup> ≤ K(m+1)<sup>e</sup>. Lemma 24 states no bound on the proof length; the Lean input asks for
   proofBits ≤ K(m+1)<sup>e</sup> as well. This follows from the lemma: the verifier makes three queries for each
   of its 2<sup>r</sup> coin outcomes, so at most 3 · 2<sup>r</sup> proof positions are ever read. Dropping the
   positions that are never read and renumbering the others changes no acceptance probability, and the renumbered
   verifier and the honest proof restricted to the read positions are still computed in polynomial time. (For accepted pairs, property (2)
   gives a polynomial bound directly: a proof constructed in poly(|C| + |w|) time has polynomial length.) CW19's
   own proof of Theorem 5 makes the same assumption when it applies Lemma 24: “We can also assume |π| = ℓ =
   poly(n)” (PDF p. 21, quoted above).
10. The verifier's running time, a documented reading. The Lean input asks for one polynomial-time Mathlib TM2
   machine that computes the verifier's whole table of 2<sup>r</sup> clauses from the code of C. CW19's
   Definition 20 states no running time for the verifier. CW19's own proof of Theorem 5 uses the verifier of
   Lemma 24 in this form: it views the verification of V(D) “as m = 2<sup>r(|D|)</sup> = poly(n) many constraints
   on the oracle y ◦ π” (PDF p. 21, quoted above). Reading the verifier as a polynomial-time algorithm, its
   2<sup>r</sup> = poly(|C|) clauses are computed in polynomial time, and the TM2 model has the same polynomial
   time (see the mapping README, “Models”). This reading is not checked by Lean.

**Documented deviations:** (a) the distance boundary (item 7): CW19's “more than δn” is stated as relative
distance at least δ; the published lemma at δ/2 implies it. (b) The proof-length bound (item 9), which Lemma 24
does not state; the lemma implies it after dropping the proof positions that are never read, and CW19's proof of
Theorem 5 assumes it too. Restrictions to δ < 1 and n ≥ 2 only weaken the statement. **Documented reading:** the
verifier is a polynomial-time algorithm (item 10).

**Class:** literal (two published lemmas, with the boundary of item 7, the proof-length bound of item 9 and the
verifier reading of item 10); the pointwise form is proved in Lean.
