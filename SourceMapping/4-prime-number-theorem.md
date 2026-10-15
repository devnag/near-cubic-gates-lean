# 4. The prime number theorem: Apostol, Chapters 4 and 13 (paper v2 `lem:primes`)

[Mapping index](README.md) · input 4 of 9 · field `primes` of `NineInputs`

The main theorem assumes the Lean statement in the first row of the table below (field `primes` of `NineInputs`). The other rows
show every definition that statement uses: the single declaration of its closure in the trusted statement file,
each printed exactly as it appears in that file. The closure stops at Lean's core library and Mathlib, whose
definitions are not printed. The prime-counting function and the
logarithm are Mathlib's.

**Source.** T. M. Apostol, “Introduction to Analytic Number Theory”, Undergraduate Texts in Mathematics, Springer (1976), Chapter 4 (pp. 74–105) and Chapter 13 (pp. 278–303). No copy of the book was available; the quotation below is the publisher's abstract of Chapter 4, [https://link.springer.com/chapter/10.1007/978-1-4757-5579-4_5](https://link.springer.com/chapter/10.1007/978-1-4757-5579-4_5), as retrieved on 2026-10-09 (the saved page has SHA-256 `d869deff87446022e1d30e28d3c5b065e9c814d33b303ae7a1c16274aac6c052`). **Provenance limitation.** The pinned item is that Chapter 4 abstract, not the book. Chapter 13, “Analytic Proof of the Prime Number Theorem” (pp. 278–303), is identified as the proof by the publisher's chapter page, [https://link.springer.com/chapter/10.1007/978-1-4757-5579-4_14](https://link.springer.com/chapter/10.1007/978-1-4757-5579-4_14); its text was not read from a pinned copy.

**Paper v2.** [`paper/paper.tex`](../paper/paper.tex) (SHA-256 `24e6ea2a2dfad613d21dd7e0e536365dfa4c2fe6085cd8b3aeaab36af937d302`); the line numbers below are of that file.

**Lean.** [`Statement.lean`](../Statement.lean) (SHA-256 `3f8d0943773ccba67099f633c458aabbf57e954f98c4898490cd3f9961d6125f`); the line numbers below are of that file.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>

<b>Apostol, Chapter 4 abstract, publisher's chapter page</b>
<pre>
If x &gt; 0 let π(x) denote the number of primes not
exceeding x.
…
Inspection of tables of primes led Gauss (1792) and
Legendre (1798) to conjecture that π(x) is asymptotic
to x/log x, that is
lim_{x→∞} π(x) log x / x = 1.
</pre>

The displayed limit is transcribed linearly. Chapter 13 of the book proves this
limit, the prime number theorem.

<b>Paper v2, lines 1281–1295</b> ([paper/paper.tex](../paper/paper.tex#L1281-L1295))

<pre>
\begin{lemma}\label{lem:primes}
For this prime set, as \(P\to\infty\),
\[
 D'=\Theta(P^2/\ln P),\qquad
 L_2=\Theta\!\left(P^{3/2}/(\ln P)^{3/4}\right).
\]
\end{lemma}
\begin{proof}
By the prime number theorem~\cite[Chapters~4 and~13]{Apostol76}, the
interval \((P/2,P]\) contains \((1+o(1))P/(2\ln P)\) primes;
Erd\H{o}s' elementary argument for Bertrand's postulate~\cite{Erdos32}
already gives this order of magnitude. Each such prime contributes
more than \(P/2-1\) and at most \(P\) to \(D'\), so
\(D'=\Theta(P^2/\ln P)\). Apply \cref{lem:window-size}.
\end{proof}
</pre>

<b>Paper v2, lines 4790–4792</b> ([paper/paper.tex](../paper/paper.tex#L4790-L4792))

<pre>
\Cref{lem:primes}, prime count &amp;
Prime number theorem \cite[Chapters~4 and~13]{Apostol76}; \cite{Erdos32} &amp;
Verbatim.\\
</pre>

</td><td>

[Statement.lean, lines 1236–1242](../Statement.lean#L1236-L1242)

<pre>
/-- The prime number theorem at natural arguments: `|π(n) log n / n - 1| &lt; ε` from an onset on, which may
depend on `ε`. -/
def ApostolPrimeNumberTheorem : Prop :=
  ∀ epsilon : ℝ, 0 &lt; epsilon →
    ∃ onset : ℕ, 2 ≤ onset ∧
      ∀ n : ℕ, onset ≤ n →
        |(Nat.primeCounting n : ℝ) * Real.log (n : ℝ) / (n : ℝ) - 1| &lt; epsilon
</pre>

</td></tr>
</table>

**What to check** (a few minutes):

1. π(n) is Mathlib's `Nat.primeCounting n`, the number of primes at most n; `Real.log` is the natural logarithm.
2. The limit π(x) log x / x → 1, restricted to natural arguments, is: for every ε > 0 there is an onset such that
   |π(n) log n / n − 1| < ε for every natural n past it. The restriction to naturals is implied by the real limit.
3. The onset is required to be at least 2. This loses nothing: any onset can be increased.
4. Paper v2 uses the theorem only for the count of primes in (P/2, P] (line 1290); that count is derived in Lean
   from this statement.
5. Provenance: the quotation is the publisher's abstract of Chapter 4, which states the limit as Gauss's and
   Legendre's conjecture; the proof is Chapter 13, identified from the publisher's page (see **Source** above),
   not read from a pinned copy. The statement is the usual prime number theorem.

**Documented deviations:** none.

**Class:** literal (restricted to natural arguments).
