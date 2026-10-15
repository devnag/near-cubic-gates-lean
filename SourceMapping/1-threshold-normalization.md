# 1. Threshold normalization: CTW26 Lemma 3.2 (paper v2 `lem:integer`)

[Mapping index](README.md) · input 1 of 9 · field `normalization` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `normalization` of `NineInputs`). The other rows
show every definition that statement uses: all 7 declarations of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. CTW26 attributes the lemma to Muroga,
Toda and Takasu (1961).

**Source.** L. Chen, A. Tal, Y. Wang, “Super-quadratic Lower Bounds for Depth-2 Linear Threshold Circuits”, ECCC report TR26-039 (2026), [https://eccc.weizmann.ac.il/report/2026/039/download/](https://eccc.weizmann.ac.il/report/2026/039/download/). Page numbers refer to that PDF, SHA-256 `b461919916161705a41f43866538d954bd100ca1d4c89451ba734d1caff9987d`.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>CTW26, PDF p. 10</b>
<pre>
Lemma 3.2 ([MTT61]). For any THR gate on m input
bits, there is an equivalent THR gate where all
parameters are integers in range ±m^m.
</pre>

<b>Paper v2, lines 1069–1077</b> ([paper/paper.tex](../paper/paper.tex#L1069-L1077))

<pre>
\begin{lemma}\label{lem:integer}
Every threshold function on \(m\ge1\) Boolean inputs has an equivalent
representation whose weights and threshold are integers in the range
\(\pm m^m\). In particular their bit lengths are \(O(m\log(m+1))\).
\end{lemma}
This is \cite[Lemma~3.2]{CTW26}, attributed there to Muroga, Toda, and
Takasu~\cite{MTT61}. H{\aa}stad~\cite[Section~3]{Has94} gives the sharper
bound \((m+1)^{(m+1)/2}\), by Cramer's rule and Hadamard's inequality; the
weaker bound suffices here.
</pre>

<b>Paper v2, lines 4769–4771</b> ([paper/paper.tex](../paper/paper.tex#L4769-L4771))

<pre>
\Cref{lem:integer}, integer weights &amp;
\cite[Lemma~3.2]{CTW26}; the classical fact is \cite{MTT61}; sharper bound in \cite[Section~3]{Has94} &amp;
Verbatim.\\
</pre>

</td><td>

[Statement.lean, lines 900–909](../Statement.lean#L900-L909)

<pre>
/-- **CTW26 Lemma 3.2 ([MTT61]), PDF page 10, verbatim:**
"For any THR gate on m input bits, there is an equivalent THR gate where all parameters are
integers in range ±m^m."

Every `m : ℕ` is quantified (no positivity; Lean's `0 ^ 0 = 1`). "All parameters" are the
weights `w i` and the threshold `t` of Definition 3.1. -/
def CTW26_Lemma3_2 : Prop :=
  ∀ (m : ℕ) (g : THRGate m), ∃ h : THRGate m,
    Equivalent g h ∧
      (∀ i, IsIntegerInRange (h.w i) (m ^ m)) ∧ IsIntegerInRange h.t (m ^ m)
</pre>

</td></tr>
<tr><td>

<b>CTW26, PDF p. 9</b>
<pre>
Definition 3.1. (Gates) We define the following
gates (on input (x1, x2, · · · , xm) ∈ {0, 1}^m):
…
THR: This gate has parameters w1, w2, · · · , wm,
t ∈ R, and outputs
I[w1x1 + w2x2 + · · · + wmxm ≥ t].
(Replacing ≥ by &gt;, &lt; or ≤ gives the same
definition.)
</pre>

</td><td>

[Statement.lean, lines 880–883](../Statement.lean#L880-L883)

<pre>
/-- CTW26 Definition 3.1, PDF p.9: "THR: This gate has parameters w1, w2, · · · , wm, t ∈ R". -/
structure THRGate (m : ℕ) where
  w : Fin m → ℝ
  t : ℝ
</pre>

[Statement.lean, lines 885–887](../Statement.lean#L885-L887)

<pre>
/-- CTW26 Definition 3.1, PDF p.9: the THR gate "outputs I[w1x1 + w2x2 + · · · + wmxm ≥ t]". -/
noncomputable def THRGate.output {m : ℕ} (g : THRGate m) (x : Fin m → ℝ) : ℕ :=
  I (∑ i, g.w i * x i ≥ g.t)
</pre>

[Statement.lean, lines 889–890](../Statement.lean#L889-L890)

<pre>
/-- CTW26 Definition 3.1, PDF p.9: "on input (x1, x2, · · · , xm) ∈ {0, 1}^m". -/
def IsInput {m : ℕ} (x : Fin m → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1
</pre>

</td></tr>
<tr><td>

<b>CTW26, PDF p. 9</b>
<pre>
For any mathematical statement α, let I[α] be the
indicator that α holds, i.e., it equals 1 if α holds
and 0 otherwise.
</pre>

</td><td>

[Statement.lean, lines 876–878](../Statement.lean#L876-L878)

<pre>
/-- CTW26 §3, PDF p.9: "let I[α] be the indicator that α holds, i.e., it equals 1 if α holds
and 0 otherwise." -/
def I (α : Prop) [Decidable α] : ℕ := if α then 1 else 0
</pre>

</td></tr>
<tr><td>

<b>CTW26, PDF p. 10</b>
<pre>
there is an equivalent THR gate
</pre>

The paper does not define “equivalent” separately; it is read as “gives the same
output on every input in {0, 1}<sup>m</sup>”.

</td><td>

[Statement.lean, lines 892–894](../Statement.lean#L892-L894)

<pre>
/-- "an equivalent THR gate": the same output on every input in `{0,1}^m`. -/
def Equivalent {m : ℕ} (g h : THRGate m) : Prop :=
  ∀ x : Fin m → ℝ, IsInput x → g.output x = h.output x
</pre>

</td></tr>
<tr><td>

<b>CTW26, PDF p. 10</b>
<pre>
all parameters are integers in range ±m^m
</pre>

</td><td>

[Statement.lean, lines 896–898](../Statement.lean#L896-L898)

<pre>
/-- "an integer in range ±R": `p = k` for an integer `k` with `-R ≤ k ≤ R`. -/
def IsIntegerInRange (p : ℝ) (R : ℕ) : Prop :=
  ∃ k : ℤ, p = (k : ℝ) ∧ -(R : ℤ) ≤ k ∧ k ≤ (R : ℤ)
</pre>

</td></tr>
</table>

Superscripts are written with `^`: `±m^m` is ±m<sup>m</sup>.

**What to check** (a few minutes):

1. The quantifiers are in the paper's order: for every number of inputs m and every THR gate g on m inputs there
   is a gate h, equivalent to g, whose parameters are all integers in range ±m<sup>m</sup>.
2. A THR gate has real weights w<sub>1</sub>, …, w<sub>m</sub> and a real threshold t, and outputs
   I[w<sub>1</sub>x<sub>1</sub> + · · · + w<sub>m</sub>x<sub>m</sub> ≥ t]; the comparison in `THRGate.output` is
   ≥, as printed.
3. The inputs are the 0-1 vectors (`IsInput`), and “equivalent” means the same output on every such input
   (`Equivalent`).
4. “All parameters” are the weights and the threshold, which Definition 3.1 lists: the statement bounds every
   weight of h and its threshold, each an integer k with −m<sup>m</sup> ≤ k ≤ m<sup>m</sup> (`IsIntegerInRange`).
5. m ranges over every natural number, including m = 0, where Lean reads 0<sup>0</sup> as 1. This repository proves
   that the statement holds at m = 0, and that it would be false there under the reading 0<sup>0</sup> = 0
   ([`ctw26_lemma3_2_at_zero`](../Bindings/CTW26_Lemma3_2.lean#L50) and [`ctw26_at_zero_needs_zero_pow_zero_eq_one`](../Bindings/CTW26_Lemma3_2.lean#L75), in [`Bindings/CTW26_Lemma3_2.lean`](../Bindings/CTW26_Lemma3_2.lean)),
   so the convention used is the true one.
6. Paper v2 states the lemma for m ≥ 1 and adds that the bit lengths are O(m log(m+1)). The Lean input is the
   source's sentence for every m, which implies the paper's lemma; the bit-length sentence is a consequence the
   proof derives in Lean, not part of the input.

**Documented deviations:** none.

**Class:** literal.
