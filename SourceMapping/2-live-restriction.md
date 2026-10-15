# 2. Live gates under random restrictions: CTW26 Lemma 4.1, Appendix A.3 (paper v2 `lem:live`)

[Mapping index](README.md) · input 2 of 9 · field `restriction` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `restriction` of `NineInputs`). The other rows
show every definition that statement uses: all 10 declarations of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. The statement is the exact
central-binomial bound of the chain-counting proof in CTW26 Appendix A.3 (its equations (14) and (15)), before the
final O(·) step.

**Source.** L. Chen, A. Tal, Y. Wang, “Super-quadratic Lower Bounds for Depth-2 Linear Threshold Circuits”, ECCC report TR26-039 (2026), [https://eccc.weizmann.ac.il/report/2026/039/download/](https://eccc.weizmann.ac.il/report/2026/039/download/). Page numbers refer to that PDF, SHA-256 `b461919916161705a41f43866538d954bd100ca1d4c89451ba734d1caff9987d`.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>CTW26, PDF p. 27</b>
<pre>
Lemma A.3.1. Let n &gt; k be positive integers. Let
f : {0, 1}^n → {0, 1} be a unate function. Then
for a random restriction ρ ∈ {0, 1, ∗}^n which has
exactly k many ∗-s, the probability that f|ρ is a
constant function is ≥ 1 − O(k/√n).
…
Combining Equations (14) and (15), we have
#{ρ ∈ P : f|ρ is non-constant} / |P|
  ≤ binom(n,k) · binom(n−k, ⌊(n−k)/2⌋) / n! · |E| / |P|
  ≤ binom(n,k) · binom(n−k, ⌊(n−k)/2⌋) / n! · k · n! / (binom(n,k) · 2^{n−k})
</pre>

<b>CTW26, PDF p. 28</b>
<pre>
  = k · binom(n−k, ⌊(n−k)/2⌋) / 2^{n−k} ≤ O(k/√(n − k)) ≤ O(k/√n).
</pre>

The displayed chain is transcribed linearly; binom(a, b) is the binomial coefficient,
printed as a stacked pair.

<b>Paper v2, lines 1087–1103</b> ([paper/paper.tex](../paper/paper.tex#L1087-L1103))

<pre>
\begin{lemma}\label{lem:live}
For a threshold gate \(g\), a uniform \(k\)-subset \(I\subseteq[n]\),
and uniform outer assignment \(y\),
\[
 \Pr[g\text{ is live on }C_y]
 \le \frac{k\binom{n-k}{\floor{(n-k)/2}}}{2^{n-k}}
 \le \frac{k}{\sqrt{n-k+1}}.
\]
Consequently, for any collection of circuits of total top weight
\(W\), and any \(\beta&gt;0\), some fixed \(I\) has
\[
 \sum_r\ell^r(y)\le \frac{Wk}{\beta\sqrt{n-k+1}}
\]
on all but a \(\beta\) fraction of cells.
\end{lemma}
The proof specializes the chain-counting argument of
\cite[Appendix~A.3]{CTW26}; it is in \cref{app:live}.
</pre>

<b>Paper v2, lines 4772–4774</b> ([paper/paper.tex](../paper/paper.tex#L4772-L4774))

<pre>
\Cref{lem:live}, live gates &amp;
\cite[Lemma~4.1; Lemma~A.3.1, (14)--(15)]{CTW26}; \cite{KW16,Lub66} &amp;
Adapted: the explicit bound \(k/\sqrt{n-k+1}\) and the Markov step are added.\\
</pre>

</td><td>

[Statement.lean, lines 1274–1280](../Statement.lean#L1274-L1280)

<pre>
/-- The published per-gate estimate. The paper's square-root estimate and its weight selection are proved from
it, not assumed. -/
noncomputable def CTW26_AppendixA3_CentralBinomialRestriction : Prop := by
  classical
  exact ∀ (n k : ℕ), 0 &lt; k → k &lt; n → ∀ g : RealThresholdGate n,
    mean (fun ρ : FiniteRestriction n k =&gt; indicator (gateLive g ρ)) ≤
      ((k * Nat.choose (n - k) ((n - k) / 2) : ℕ) : ℝ) / (2 : ℝ) ^ (n - k)
</pre>

</td></tr>
<tr><td>

<b>CTW26, PDF p. 27</b>
<pre>
Let P be the set of all restriction ρ ∈ {0, 1, ∗}^n
which has exactly k many ∗-s. |P| = binom(n,k) · 2^{n−k}.
</pre>

</td><td>

[Statement.lean, lines 1257–1260](../Statement.lean#L1257-L1260)

<pre>
/-- Every k-subset occurs once, and every assignment on its complement occurs
once. Uniform averaging over this finite type is the published restriction law. -/
abbrev FiniteRestriction (n k : ℕ) :=
  Σ I : {I : Finset (Fin n) // I.card = k}, {i : Fin n // i ∉ I.val} → Bool
</pre>

[Statement.lean, lines 1155–1156](../Statement.lean#L1155-L1156)

<pre>
noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α
</pre>

[Statement.lean, lines 1270–1272](../Statement.lean#L1270-L1272)

<pre>
noncomputable def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0
</pre>

</td></tr>
<tr><td>

<b>CTW26, PDF p. 27</b>
<pre>
f|ρ is a constant function
</pre>

<b>CTW26, PDF p. 27</b>
<pre>
(We remark that ρ(0^n), ρ(1^n) are strings obtained by
replacing all ∗-s in ρ by 0-s, 1-s.)
</pre>

</td><td>

[Statement.lean, lines 1262–1264](../Statement.lean#L1262-L1264)

<pre>
/-- The full input lies in the cell specified by the outer assignment. -/
def cellAgrees {n k : ℕ} (ρ : FiniteRestriction n k) (x : BitInput n) : Prop :=
  ∀ (i : Fin n) (hi : i ∉ ρ.1.val), x i = ρ.2 ⟨i, hi⟩
</pre>

[Statement.lean, lines 1266–1268](../Statement.lean#L1266-L1268)

<pre>
/-- The gate is not constant on the cell. -/
def gateLive {n k : ℕ} (g : RealThresholdGate n) (ρ : FiniteRestriction n k) : Prop :=
  ∃ x z : BitInput n, cellAgrees ρ x ∧ cellAgrees ρ z ∧ g.eval x ≠ g.eval z
</pre>

</td></tr>
<tr><td>

<b>CTW26, PDF p. 27</b>
<pre>
Lemma A.3. Let n &gt; k be positive integers. Let
f : {0, 1}^n → {0, 1} be a linear threshold
function.
</pre>

<b>CTW26, PDF p. 28</b>
<pre>
Proof of Lemma A.3. Note that linear threshold
functions are unate, so this is just a subcase of
Lemma A.3.1.
</pre>

<b>CTW26, PDF p. 9</b>
<pre>
THR: This gate has parameters w1, w2, · · · , wm,
t ∈ R, and outputs
I[w1x1 + w2x2 + · · · + wmxm ≥ t].
</pre>

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
</table>

**Auxiliary constants.** Lean stores small generated proofs and pattern-matching helpers under the name of the first declaration that needed them, and later declarations reuse them. The statement uses the following ones, whose own declarations are not part of the statement; each is fully determined by its type shown here (a proof of a proposition, or the standard case-analysis principle of the type it matches on).

- `NearCubicWires.Bindings.CLW20Lemma39.CannotBeApproximated._proof_1` : `(1 + 1).AtLeastTwo`, generated by Lean with the declaration at [Statement.lean, lines 931–936](../Statement.lean#L931-L936).

**What to check** (a few minutes):

1. The hypotheses are the lemma's: 0 < k < n (“Let n > k be positive integers”), and g is a linear threshold
   function on n inputs (`RealThresholdGate`: real weights, real threshold, output 1 exactly when
   threshold ≤ Σ weight<sub>i</sub>x<sub>i</sub>). Lemma A.3 is the threshold case of Lemma A.3.1 (PDF p. 28).
2. The random restriction: `FiniteRestriction n k` is the set of pairs (I, y) of a k-subset I (the ∗ positions)
   and an assignment y to the other n − k coordinates; it is in bijection with P, and `mean` over it is the
   uniform average over P.
3. “f|ρ is non-constant” is `gateLive`: two inputs that agree with y outside I (`cellAgrees`) on which the gate
   differs.
4. The bound is exactly k · binom(n−k, ⌊(n−k)/2⌋) / 2<sup>n−k</sup>, the value the chain reaches on PDF p. 28
   before the O(·) estimate; `(n - k) / 2` is the floor in ℕ.
5. Paper v2's second inequality k/√(n−k+1) and the Markov consequence for a collection of circuits are proved in
   Lean from this statement; they are not part of the input (paper v2, line 4774: “Adapted: the explicit bound
   … and the Markov step are added”).

**Documented deviations:** none. The statement is the source's exact counting bound, a step of its proof of
Lemma A.3.1 for the threshold case.

**Class:** literal (exact bound from the proof).
