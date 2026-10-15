# 3. Bernstein's inequality: Vershynin Theorem 2.8.4 with K = 1 (paper v2 `lem:bernstein`)

[Mapping index](README.md) · input 3 of 9 · field `bernstein` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `bernstein` of `NineInputs`). The other rows
show every definition that statement uses: all 4 declarations of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. The statement is the theorem for
K = 1 on finite uniform probability spaces, which is all the proof uses.

**Source.** R. Vershynin, “High-Dimensional Probability: An Introduction with Applications in Data Science”, first edition, Cambridge University Press (2018); author-hosted PDF of the first edition, [https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf](https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf). Page numbers refer to that PDF, SHA-256 `681b6f3d947f71c023f3d1090e7aa33fd7e302647a6dfb6e69bd272363b6f462`. The theorem is on printed page 38.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>Vershynin, PDF p. 46</b>
<pre>
Theorem 2.8.4 (Bernstein’s inequality for bounded
distributions). Let X1, . . . , XN be independent,
mean zero random variables, such that |Xi| ≤ K
all i. Then, for every t ≥ 0, we have
P{ |Σ_{i=1}^N Xi| ≥ t } ≤ 2 exp( −(t²/2) / (σ² + Kt/3) ).
Here σ² = Σ_{i=1}^N E Xi² is the variance of the sum.
</pre>

The displayed inequality and the definition of σ² are transcribed linearly.

<b>Paper v2, lines 1105–1115</b> ([paper/paper.tex](../paper/paper.tex#L1105-L1115))

<pre>
We also use the bounded-variable Bernstein inequality,
Vershynin~\cite[Theorem~2.8.4, first edition]{Vershynin18} with \(K=1\).
\begin{lemma}\label{lem:bernstein}
If independent centered random variables \(Y_t\) satisfy
\(\abs{Y_t}\le1\) and \(\sum_t\E Y_t^2\le V\), then for every \(s&gt;0\),
\[
 \Pr\!\left[\abs{\sum_tY_t}\ge s\right]
 \le2\exp\!\left(-\frac{s^2}{2(V+s/3)}\right).
\]
In particular, for \(T&gt;0\), \(s=\sqrt{2TV}+2T/3\) gives a bound of \(2e^{-T}\).
\end{lemma}
</pre>

<b>Paper v2, lines 4775–4777</b> ([paper/paper.tex](../paper/paper.tex#L4775-L4777))

<pre>
\Cref{lem:bernstein} &amp;
\cite[Theorem~2.8.4, first edition]{Vershynin18}, with \(K=1\) &amp;
Verbatim.\\
</pre>

</td><td>

[Statement.lean, lines 1294–1306](../Statement.lean#L1294-L1306)

<pre>
/-- The finite uniform K = 1 specialization of the published bounded-variable
Bernstein inequality. The variance is the literal sum of second moments. -/
noncomputable def Vershynin18_Theorem2_8_4_FiniteBernstein : Prop := by
  classical
  exact ∀ (Samples Terms : Type*) [Fintype Samples] [Nonempty Samples]
      [Fintype Terms] [Nonempty Terms] (Y : Terms → Samples → ℝ),
    finiteIndependent Y →
    (∀ i, mean (Y i) = 0) →
    (∀ i sample, |Y i sample| ≤ 1) →
    ∀ s : ℝ, 0 &lt; s →
      mean (fun sample =&gt; indicator (s ≤ |∑ i, Y i sample|)) ≤
        2 * Real.exp (-(s ^ 2) /
          (2 * ((∑ i, mean (fun sample =&gt; (Y i sample) ^ 2)) + s / 3)))
</pre>

</td></tr>
<tr><td>

<b>Vershynin, PDF p. 46</b>
<pre>
be independent,
</pre>

</td><td>

[Statement.lean, lines 1282–1292](../Statement.lean#L1282-L1292)

<pre>
/-- Mutual independence under uniform averaging, stated as joint-event
factorization for every finite subfamily (a hypothesis of the inequality).
For each i the range of Y i is finite. Any real event can be replaced by its
intersection with that finite range, a Borel set with the same preimage, so
this imposes no stronger notion of independence through measurability. -/
noncomputable def finiteIndependent {Samples Terms : Type*} [Fintype Samples]
    (Y : Terms → Samples → ℝ) : Prop := by
  classical
  exact ∀ (S : Finset Terms) (events : Terms → Set ℝ),
    mean (fun sample =&gt; indicator (∀ i ∈ S, Y i sample ∈ events i)) =
      ∏ i ∈ S, mean (fun sample =&gt; indicator (Y i sample ∈ events i))
</pre>

</td></tr>
<tr><td>

P and E: probability and expectation. On a finite sample set with the uniform
measure, both are averages: P[A] is the average of the indicator of A, and E[X] the average of X.

</td><td>

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
</table>

**Auxiliary constants.** Lean stores small generated proofs and pattern-matching helpers under the name of the first declaration that needed them, and later declarations reuse them. The statement uses the following ones, whose own declarations are not part of the statement; each is fully determined by its type shown here (a proof of a proposition, or the standard case-analysis principle of the type it matches on).

- `NearCubicWires.Bindings.CLW20Lemma39.CannotBeApproximated._proof_1` : `(1 + 1).AtLeastTwo`, generated by Lean with the declaration at [Statement.lean, lines 931–936](../Statement.lean#L931-L936).

**What to check** (a few minutes):

1. The probability space is a finite, nonempty sample set with the uniform measure; the random variables are
   Y<sub>i</sub>, for i in a finite, nonempty index set (N ≥ 1). P[·] and E[·] are `mean` of indicators and of
   values.
2. Independence (`finiteIndependent`) is mutual independence: for every finite subfamily S and every choice of
   real events A<sub>i</sub>, P[Y<sub>i</sub> ∈ A<sub>i</sub> for all i ∈ S] = Π<sub>i∈S</sub>
   P[Y<sub>i</sub> ∈ A<sub>i</sub>]. Lean lets A<sub>i</sub> be any set of reals, where measure theory takes Borel
   sets; on a finite space this is the same condition, because Y<sub>i</sub> takes finitely many values and
   A<sub>i</sub> can be replaced by its intersection with that finite set of values, which is Borel.
3. The hypotheses are mean zero and |Y<sub>i</sub>| ≤ 1, that is K = 1.
4. The conclusion, for every s > 0: P[|Σ Y<sub>i</sub>| ≥ s] ≤ 2 exp(−s²/(2(σ² + s/3))) with
   σ² = Σ E Y<sub>i</sub>². At K = 1 the printed exponent (t²/2)/(σ² + Kt/3) equals t²/(2(σ² + t/3)).
5. The universe annotation `.{0, 0}` in `NineInputs` instantiates the sample and index types in `Type`.

**Documented deviations:** none beyond specialization: finite uniform spaces, K = 1 and t > 0 are special cases of
the theorem, so the source implies the statement.

**Class:** literal (specialized).
