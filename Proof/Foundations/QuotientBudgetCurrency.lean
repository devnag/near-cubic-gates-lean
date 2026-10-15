import Proof.Foundations.Semantics

/-!
# The quotient-budget currency at low import depth

The frozen constants and the budget currency, placed below `ExecutableInterfaces` so that the
machine interface, the closure lemmas and `PublishedRecoveryClosure`'s clock literal can all
reference them without import cycles.

Contents:
* `recoveryVerifierDegree` names only the clock: `recoveryVerifierDegree + 1` is the frozen
  depth 5.
* `honestRecoveryDegree = 2 ^ (recoveryVerifierDegree + 1) = 32` — the machine's honest declared
  degree.  It must equal `2 ^ clockDepth` exactly: the no-go theorem
  `clockExponentFloor_not_recoveryRequestPolyBoundedAt` applies at every degree `≤ 31` and fails
  at exactly `32`, so `32` is the first admissible value.
* `savingExponent` (σ_net := 1), `columnTableExponent` (h_D),
  `savingKappa` (κ > h_D + σ + 10, paper.tex:949), `batchWidthParameter`
  (K = κ·L(q), paper.tex:979-981), `quotientBudget` — the declared-budget currency.
* The two lemmas (K-freeze saving threshold; printer-constraint feasibility) and the
  eventual-domination engine behind them.

Statement-form notes: the printer bracket is bounded with `logScale`
(`⌈log₂(·+2)⌉ ≥ log₂(·+1)`), pointwise larger than the paper's terms —
conservative direction.  The budget ledger consumes the tree's own
`normalizedLiveCount` (min-q-clamped) rather than `batchWidthParameter`,
which is kept as the paper's value.
-/

namespace NearCubicWires

namespace ExecutableRecoveryMachine

/-- **The source-independent degree envelope.**  Four stages are linked
(request front end, lowering, preserved validator call, gate) below the
semantic stage, and the composed budget is charged as
`coefficient * (measure + 1) ^ recoveryVerifierDegree`.  The numeral mentions
no refuter source, no outer PCP, no schedule coordinate and no field of
`PublishedContracts`; every schedule-dependent growth is charged to the
coefficient instead.  This is what makes the derived clock depth
`recoveryVerifierDegree + 1` available *before* the source is selected.

This constant names only the clock; the machine's declared degree is
`honestRecoveryDegree`. -/
def recoveryVerifierDegree : ℕ := 4

/-- **Frozen: the honest machine degree** `2 ^ (recoveryVerifierDegree
+ 1) = 2 ^ clockDepth = 32` — the verifier body's true polynomial scale at
the frozen clock depth, and the unique first degree the
width-envelope no-go theorems allow. -/
def honestRecoveryDegree : ℕ := 2 ^ (recoveryVerifierDegree + 1)

theorem honestRecoveryDegree_eq_thirtyTwo : honestRecoveryDegree = 32 := rfl

end ExecutableRecoveryMachine

/-! ## §1 The frozen saving constants -/

/-- **Frozen: the net saving exponent** `σ_net`.  The little-o discharge
needs only positivity; the budget ledger certifies the body fuel at
exactly this exponent.  The paper-side σ is a parameter; the machine's is frozen at `1`. -/
def savingExponent : ℕ := 1

theorem savingExponent_pos : 0 < savingExponent := Nat.one_pos

/-- **Frozen: the external-row exponent** — the paper's `h_D`
(paper.tex:945), at a conservative upper bound (module header). -/
def columnTableExponent : ℕ := 12

/-- **Frozen: the batch-bits multiplier** — the paper's `κ`, at the least
integer clearing the strict `κ > h_D + σ + 10` (paper.tex:949). -/
def savingKappa : ℕ := columnTableExponent + savingExponent + 11

theorem lt_savingKappa :
    columnTableExponent + savingExponent + 10 < savingKappa := by
  decide

/-- **The batch width parameter** `K(q) = κ · L(q)` — `Θ(log q)` batch bits
(paper.tex:979-981).  Kept as the paper's value; the body
program consumes `normalizedLiveCount`. -/
def batchWidthParameter (q : ℕ) : ℕ := savingKappa * logScale q

/-- **The quotient budget** — the declared-budget currency:
`⌊coefficient · (measure+1)^degree / L(measure)^saving⌋`.
Floor division only SHRINKS the declared budget, so `halts` stated at this
budget is harder, never easier, than the paper's real-valued quotient. -/
def quotientBudget (coefficient degree saving measure : ℕ) : ℕ :=
  coefficient * (measure + 1) ^ degree / logScale measure ^ saving

theorem quotientBudget_le_pure (coefficient degree saving measure : ℕ) :
    quotientBudget coefficient degree saving measure ≤
      coefficient * (measure + 1) ^ degree :=
  Nat.div_le_self _ _

/-! ## §2 Elementary `logScale` facts -/

/-- `q + 2 ≤ 2 ^ L(q)` — the defining upper crossing of the ceiling log. -/
theorem le_two_pow_logScale (q : ℕ) : q + 2 ≤ 2 ^ logScale q :=
  Nat.le_pow_clog (by norm_num) _

/-- `2 ^ (L(q) − 1) < q + 2` — the defining lower crossing. -/
theorem two_pow_logScale_pred_lt (q : ℕ) : 2 ^ (logScale q - 1) < q + 2 :=
  Nat.pow_pred_clog_lt_self (b := 2) (x := q + 2) (by norm_num) (by omega)

/-- `logScale` eventually clears every threshold: `2^bound ≤ q` forces
`bound ≤ L(q)`.  (The onset chooser for the quotient little-o lemma.) -/
theorem le_logScale_of_two_pow_le {bound q : ℕ} (h : 2 ^ bound ≤ q) :
    bound ≤ logScale q := by
  have hmono : Nat.clog 2 (2 ^ bound) ≤ Nat.clog 2 (q + 2) :=
    Nat.clog_mono_right _ (by omega)
  rwa [Nat.clog_pow _ _ (by norm_num)] at hmono

/-- Budget monotonicity: one `logScale` power is dominated by two polynomial degrees,
universally in the measure. -/
theorem logScale_le_sq_succ (m : ℕ) : logScale m ≤ (m + 1) ^ 2 := by
  have h : m + 2 ≤ 2 ^ ((m + 1) ^ 2) := by
    have hlin : m + 2 ≤ 2 ^ (m + 1) := by
      have := Nat.lt_two_pow_self (n := m + 1)
      omega
    have hexp : m + 1 ≤ (m + 1) ^ 2 := by nlinarith
    exact hlin.trans (Nat.pow_le_pow_right (by norm_num) hexp)
  exact Nat.clog_le_of_le_pow h

/-! ## §3 Lemma one — `K` meets the saving threshold -/

/-- **The K-freeze saving lemma** (paper.tex:1172-1178).
`2^K` dominates `(q+2)^{h_D+σ+10}`: dividing the `2^{q−K}`-column
enumeration by `2^K ≥ q^{h_D}·q^{σ}·q^{10}` pays the external-row factor
`q^{h_D}`, the saving `q^{σ}`, and leaves ten powers of `q` for every
polynomial overhead. -/
theorem batchWidth_meets_savingThreshold (q : ℕ) :
    (q + 2) ^ (columnTableExponent + savingExponent + 10) ≤
      2 ^ batchWidthParameter q := by
  have hbase : q + 2 ≤ 2 ^ logScale q := le_two_pow_logScale q
  have hone : 1 ≤ 2 ^ logScale q := Nat.one_le_two_pow
  calc
    (q + 2) ^ (columnTableExponent + savingExponent + 10)
        ≤ (2 ^ logScale q) ^ (columnTableExponent + savingExponent + 10) :=
          Nat.pow_le_pow_left hbase _
    _ ≤ (2 ^ logScale q) ^ savingKappa :=
          Nat.pow_le_pow_right hone (Nat.le_of_lt lt_savingKappa)
    _ = 2 ^ (savingKappa * logScale q) := by
          rw [← pow_mul, Nat.mul_comm]
    _ = 2 ^ batchWidthParameter q := rfl

/-! ## §4 The eventual-domination engine

`Θ(log² q) ≤ q` eventually, in fully explicit Nat form: no analysis, no
asymptotic classes, onset computable from the constants. -/

private theorem cube_le_two_pow (a : ℕ) :
    81 * (a + 1) ^ 3 ≤ 2 ^ (8 * a + 7) := by
  induction a with
  | zero => decide
  | succ a ih =>
      have hstep : (a + 2) ^ 3 ≤ 8 * (a + 1) ^ 3 := by
        have hbase : a + 2 ≤ 2 * (a + 1) := by omega
        calc (a + 2) ^ 3 ≤ (2 * (a + 1)) ^ 3 := Nat.pow_le_pow_left hbase 3
          _ = 8 * (a + 1) ^ 3 := by ring
      calc 81 * (a + 1 + 1) ^ 3 = 81 * (a + 2) ^ 3 := by ring_nf
        _ ≤ 8 * (81 * (a + 1) ^ 3) := by omega
        _ ≤ 8 * 2 ^ (8 * a + 7) := Nat.mul_le_mul_left 8 ih
        _ = 2 ^ (8 * a + 10) := by rw [pow_add]; ring
        _ ≤ 2 ^ (8 * (a + 1) + 7) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The square-vs-power crossing: past onset `8·(a+1)`, the parabola
`a·(L+1)²` sits below `2^{L−1}`. -/
private theorem sq_mul_le_two_pow {a L : ℕ} (h : 8 * (a + 1) ≤ L) :
    a * (L + 1) ^ 2 ≤ 2 ^ (L - 1) := by
  induction L with
  | zero => omega
  | succ L ih =>
      rcases Nat.lt_or_ge L (8 * (a + 1)) with hbase | hind
      · -- the base rung: `L + 1 = 8·(a+1)` exactly
        have hL : L + 1 = 8 * (a + 1) := by omega
        have hsq : a * (L + 1 + 1) ^ 2 ≤ 81 * (a + 1) ^ 3 := by
          have hlin : L + 1 + 1 ≤ 9 * (a + 1) := by omega
          calc a * (L + 1 + 1) ^ 2 ≤ a * (9 * (a + 1)) ^ 2 :=
                Nat.mul_le_mul_left a (Nat.pow_le_pow_left hlin 2)
            _ = 81 * (a * (a + 1) ^ 2) := by ring
            _ ≤ 81 * ((a + 1) * (a + 1) ^ 2) := by
                have : a * (a + 1) ^ 2 ≤ (a + 1) * (a + 1) ^ 2 :=
                  Nat.mul_le_mul_right _ (Nat.le_succ a)
                omega
            _ = 81 * (a + 1) ^ 3 := by ring
        calc a * (L + 1 + 1) ^ 2 ≤ 81 * (a + 1) ^ 3 := hsq
          _ ≤ 2 ^ (8 * a + 7) := cube_le_two_pow a
          _ ≤ 2 ^ (L + 1 - 1) := by
              apply Nat.pow_le_pow_right (by norm_num)
              omega
      · -- the induction rung: doubling beats `((L+2)/(L+1))²`
        have hprev : a * (L + 1) ^ 2 ≤ 2 ^ (L - 1) := ih hind
        have hLpos : 2 ≤ L := by omega
        have hsq : a * (L + 1 + 1) ^ 2 ≤ 2 * (a * (L + 1) ^ 2) := by
          have hgrow : (L + 2) ^ 2 ≤ 2 * (L + 1) ^ 2 := by nlinarith
          calc a * (L + 1 + 1) ^ 2 = a * (L + 2) ^ 2 := by ring_nf
            _ ≤ a * (2 * (L + 1) ^ 2) := Nat.mul_le_mul_left a hgrow
            _ = 2 * (a * (L + 1) ^ 2) := by ring
        calc a * (L + 1 + 1) ^ 2 ≤ 2 * (a * (L + 1) ^ 2) := hsq
          _ ≤ 2 * 2 ^ (L - 1) := Nat.mul_le_mul_left 2 hprev
          _ = 2 ^ (L - 1 + 1) := by rw [pow_succ]; ring
          _ = 2 ^ (L + 1 - 1) := by congr 1; omega

/-- **The engine**: past the explicit onset `2^{8·(a+3)}`, the square of
the log-scale (times any constant) is dominated by `q` itself. -/
theorem sq_logScale_le_of_onset {a q : ℕ}
    (h : 2 ^ (8 * (a + 3)) ≤ q) :
    a * (logScale q + 1) ^ 2 ≤ q := by
  have hL : 8 * (a + 2 + 1) ≤ logScale q := le_logScale_of_two_pow_le h
  have hcross : (a + 2) * (logScale q + 1) ^ 2 ≤ 2 ^ (logScale q - 1) :=
    sq_mul_le_two_pow hL
  have hlow : 2 ^ (logScale q - 1) < q + 2 := two_pow_logScale_pred_lt q
  have hslack : 2 * 1 ^ 2 ≤ 2 * (logScale q + 1) ^ 2 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2)
  nlinarith [sq_nonneg (logScale q + 1)]

/-! ## §5 Lemma two — the printer constraint clears eventually -/

/-- **The printer-constraint feasibility lemma** (paper.tex:2719-2726).  For every constant triple `(c₀, d, b)` there is an
explicit onset `q₀` past which the Theorem A.12.1 bracket — with
`Q ≤ K + 1` (the minimal modulus exponent, paper.tex:979) and the gate
pool bounded by `B ≤ (q+2)^b` — clears `(q − K)/100`.  The bracket is
`Θ(log² q)` against a linear right side; no constraint on the clock depth
arises. -/
theorem printerConstraint_eventually (c₀ d b : ℕ) :
    ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ B Q, B ≤ (q + 2) ^ b →
      Q ≤ batchWidthParameter q + 1 →
      c₀ * (batchWidthParameter q + logScale Q + Q * d * logScale B +
          logScale q) ≤
        (q - batchWidthParameter q) / 100 := by
  classical
  -- the assembled quadratic coefficient and the explicit onset
  set A : ℕ :=
    c₀ * (2 * savingKappa + 4 + (savingKappa + 1) * d * (b + 2)) with hA
  refine ⟨2 ^ (8 * ((100 * A + savingKappa) + 3)), ?_⟩
  intro q hq B Q hB hQ
  set L : ℕ := logScale q with hLdef
  have hK : batchWidthParameter q = savingKappa * L := rfl
  -- component bounds, all against (L+1)
  have hlogQ : logScale Q ≤ (savingKappa + 3) * (L + 1) := by
    have hclog : logScale Q ≤ Q + 2 := by
      have : Nat.clog 2 (Q + 2) ≤ Q + 2 :=
        Nat.clog_le_of_le_pow
          (Nat.le_of_lt (Nat.lt_two_pow_self))
      exact this
    have : Q + 2 ≤ savingKappa * L + 3 := by omega
    nlinarith
  have hQle : Q ≤ (savingKappa + 1) * (L + 1) := by
    have : Q ≤ savingKappa * L + 1 := by omega
    nlinarith
  have hlogB : logScale B ≤ (b + 2) * (L + 1) := by
    have hpow : (q + 2) ^ b ≤ 2 ^ (b * L) := by
      calc (q + 2) ^ b ≤ (2 ^ L) ^ b :=
            Nat.pow_le_pow_left (le_two_pow_logScale q) b
        _ = 2 ^ (b * L) := by rw [← pow_mul, Nat.mul_comm]
    have hBsucc : B + 2 ≤ 2 ^ (b * L + 2) := by
      have hone : 1 ≤ 2 ^ (b * L) := Nat.one_le_two_pow
      have : B + 2 ≤ 2 ^ (b * L) + 2 := by omega
      calc B + 2 ≤ 2 ^ (b * L) + 2 := this
        _ ≤ 4 * 2 ^ (b * L) := by omega
        _ = 2 ^ (b * L + 2) := by rw [pow_add]; ring
    have hclogB : Nat.clog 2 (B + 2) ≤ b * L + 2 :=
      Nat.clog_le_of_le_pow hBsucc
    have : logScale B = Nat.clog 2 (B + 2) := rfl
    nlinarith
  -- the bracket sits below A·(L+1)²
  have hbracket :
      c₀ * (batchWidthParameter q + logScale Q + Q * d * logScale B + L) ≤
        A * (L + 1) ^ 2 := by
    have hmid : Q * d * logScale B ≤
        (savingKappa + 1) * d * (b + 2) * (L + 1) ^ 2 := by
      calc Q * d * logScale B
          ≤ ((savingKappa + 1) * (L + 1)) * d * ((b + 2) * (L + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right d hQle) hlogB
        _ = (savingKappa + 1) * d * (b + 2) * (L + 1) ^ 2 := by ring
    have hlin :
        batchWidthParameter q + logScale Q + L ≤
          (2 * savingKappa + 4) * (L + 1) := by
      have h1 : batchWidthParameter q ≤ savingKappa * (L + 1) := by
        rw [hK]; exact Nat.mul_le_mul_left _ (Nat.le_succ L)
      nlinarith
    have hsum :
        batchWidthParameter q + logScale Q + Q * d * logScale B + L ≤
          (2 * savingKappa + 4 + (savingKappa + 1) * d * (b + 2)) *
            (L + 1) ^ 2 := by
      have hlift : (2 * savingKappa + 4) * (L + 1) ≤
          (2 * savingKappa + 4) * (L + 1) ^ 2 := by
        have : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
        exact Nat.mul_le_mul_left _ this
      nlinarith
    calc c₀ * (batchWidthParameter q + logScale Q + Q * d * logScale B + L)
        ≤ c₀ * ((2 * savingKappa + 4 + (savingKappa + 1) * d * (b + 2)) *
            (L + 1) ^ 2) := Nat.mul_le_mul_left c₀ hsum
      _ = A * (L + 1) ^ 2 := by rw [hA]; ring
  -- the right side dominates: q ≥ (100·A + κ)·(L+1)²
  have hdom : (100 * A + savingKappa) * (L + 1) ^ 2 ≤ q :=
    sq_logScale_le_of_onset hq
  have hKle : batchWidthParameter q ≤ savingKappa * (L + 1) ^ 2 := by
    rw [hK]
    have : L ≤ (L + 1) ^ 2 := by nlinarith
    exact Nat.mul_le_mul_left _ this
  have hgoal : A * (L + 1) ^ 2 * 100 ≤ q - batchWidthParameter q := by
    have : A * (L + 1) ^ 2 * 100 + batchWidthParameter q ≤ q := by
      nlinarith
    omega
  exact hbracket.trans (Nat.le_div_iff_mul_le (by norm_num) |>.mpr hgoal)

end NearCubicWires
