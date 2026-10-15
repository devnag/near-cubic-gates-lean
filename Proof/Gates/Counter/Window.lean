import Proof.Gates.Counter.Eventual

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates

def scalarWindowConstant (Kp C0 : ℕ) : ℕ :=
  8 * 256 ^ 2 * Kp ^ 6 * C0 ^ 2 + 1

def pairWindowConstant (Kp C0 Cg : ℕ) : ℕ :=
  64 * Cg * 16 ^ 4 * Kp ^ 10 * C0 ^ 4 + 1

theorem scalar_window_nat (n L M P h s R u w a Kp C0 : ℕ)
    (lpos : 0 < L) (mpos : 0 < M) (kpos : 0 < Kp)
    (hpos : 0 < h) (spos : 0 < s) (rpos : 0 < R) (upos : 0 < u)
    (prime : n ≤ Kp * L * M ^ 2 * P)
    (root : n ≤ 8 * R ^ 2) (height : P ≤ 8 * h)
    (side : P ^ 2 ≤ 32 * s * L)
    (live : a ≤ C0 * w * L ^ 2 * M ^ 2)
    (cap : (scalarWindowConstant Kp C0 * w * L ^ 6 * M ^ 8) ^ 2 ≤ n ^ 7 * u ^ 2) :
    a < h * s * u * R := by
  by_cases wz : w = 0
  · have az : a = 0 := by simp only [wz, mul_zero, zero_mul] at live; omega
    rw [az]
    positivity
  have wpos : 0 < w := by omega
  let F := 8 * 256 ^ 2 * Kp ^ 6 * L ^ 8 * M ^ 12
  have fp : 0 < F := by dsimp only [F]; positivity
  have cubic : P ^ 3 ≤ 256 * h * s * L := by
    calc
      _ = P * P ^ 2 := by ring
      _ ≤ (8 * h) * (32 * s * L) := Nat.mul_le_mul height side
      _ = _ := by ring
  have nupper : n ^ 7 * u ^ 2 ≤ F * (h * s * u * R) ^ 2 := by
    calc
      _ = (n ^ 3) ^ 2 * n * u ^ 2 := by ring
      _ ≤ ((Kp * L * M ^ 2 * P) ^ 3) ^ 2 * (8 * R ^ 2) * u ^ 2 := by
        gcongr
      _ = (Kp ^ 3 * L ^ 3 * M ^ 6) ^ 2 * (P ^ 3) ^ 2 *
          (8 * R ^ 2) * u ^ 2 := by ring
      _ ≤ (Kp ^ 3 * L ^ 3 * M ^ 6) ^ 2 * (256 * h * s * L) ^ 2 *
          (8 * R ^ 2) * u ^ 2 := by gcongr
      _ = _ := by dsimp only [F]; ring
  have coefficient : 8 * 256 ^ 2 * Kp ^ 6 * C0 ^ 2 <
      scalarWindowConstant Kp C0 ^ 2 := by
    dsimp only [scalarWindowConstant]
    nlinarith only [Nat.zero_le (8 * 256 ^ 2 * Kp ^ 6 * C0 ^ 2)]
  have strict : F * a ^ 2 < (scalarWindowConstant Kp C0 * w * L ^ 6 * M ^ 8) ^ 2 := by
    calc
      _ ≤ F * (C0 * w * L ^ 2 * M ^ 2) ^ 2 := Nat.mul_le_mul_left F
        (Nat.pow_le_pow_left live 2)
      _ = (8 * 256 ^ 2 * Kp ^ 6 * C0 ^ 2) * (w ^ 2 * L ^ 12 * M ^ 16) := by
        dsimp only [F]; ring
      _ < scalarWindowConstant Kp C0 ^ 2 * (w ^ 2 * L ^ 12 * M ^ 16) :=
        Nat.mul_lt_mul_of_pos_right coefficient (by positivity)
      _ = _ := by ring
  have powers : a ^ 2 < (h * s * u * R) ^ 2 :=
    Nat.lt_of_mul_lt_mul_left (strict.trans_le (cap.trans nupper))
  by_contra fail
  have backwards : h * s * u * R ≤ a := by omega
  exact (not_le_of_gt powers) (Nat.pow_le_pow_left backwards 2)

theorem pair_window_nat (n L M P h s R u w a Kp C0 Cg : ℕ)
    (lpos : 0 < L) (mpos : 0 < M) (kpos : 0 < Kp) (cgpos : 0 < Cg)
    (hpos : 0 < h) (spos : 0 < s) (rpos : 0 < R) (upos : 0 < u)
    (prime : n ≤ Kp * L * M ^ 2 * P)
    (root : n ≤ 8 * R ^ 2) (height : P ≤ 8 * h)
    (side : P ^ 6 ≤ Cg * L ^ 3 * (2 * s) ^ 4)
    (live : a ≤ C0 * w * L ^ 2 * M ^ 2)
    (cap : (pairWindowConstant Kp C0 Cg * w * M ^ 7) ^ 4 * L ^ 21 ≤ n ^ 12 * u ^ 4) :
    a < h * s * u * R := by
  by_cases wz : w = 0
  · have az : a = 0 := by simp only [wz, mul_zero, zero_mul] at live; omega
    rw [az]
    positivity
  have wpos : 0 < w := by omega
  let F := 64 * Cg * 16 ^ 4 * Kp ^ 10 * L ^ 13 * M ^ 20
  have fp : 0 < F := by dsimp only [F]; positivity
  have tenth : P ^ 10 ≤ 16 ^ 4 * Cg * L ^ 3 * (h * s) ^ 4 := by
    calc
      _ = P ^ 4 * P ^ 6 := by ring
      _ ≤ (8 * h) ^ 4 * (Cg * L ^ 3 * (2 * s) ^ 4) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left height 4) side
      _ = _ := by ring
  have nupper : n ^ 12 * u ^ 4 ≤ F * (h * s * u * R) ^ 4 := by
    calc
      _ = n ^ 10 * n ^ 2 * u ^ 4 := by ring
      _ ≤ (Kp * L * M ^ 2 * P) ^ 10 * (8 * R ^ 2) ^ 2 * u ^ 4 := by
        gcongr
      _ = Kp ^ 10 * L ^ 10 * M ^ 20 * P ^ 10 * (8 * R ^ 2) ^ 2 * u ^ 4 := by ring
      _ ≤ Kp ^ 10 * L ^ 10 * M ^ 20 *
          (16 ^ 4 * Cg * L ^ 3 * (h * s) ^ 4) * (8 * R ^ 2) ^ 2 * u ^ 4 := by
        gcongr
      _ = _ := by dsimp only [F]; ring
  have coefficient : 64 * Cg * 16 ^ 4 * Kp ^ 10 * C0 ^ 4 <
      pairWindowConstant Kp C0 Cg ^ 4 := by
    have one : 0 < pairWindowConstant Kp C0 Cg := by dsimp only [pairWindowConstant]; omega
    have powers := Nat.pow_le_pow_right one (by decide : 1 ≤ 4)
    simp only [pow_one] at powers
    dsimp only [pairWindowConstant] at powers ⊢
    omega
  have strict : F * a ^ 4 < (pairWindowConstant Kp C0 Cg * w * M ^ 7) ^ 4 * L ^ 21 := by
    calc
      _ ≤ F * (C0 * w * L ^ 2 * M ^ 2) ^ 4 := Nat.mul_le_mul_left F
        (Nat.pow_le_pow_left live 4)
      _ = (64 * Cg * 16 ^ 4 * Kp ^ 10 * C0 ^ 4) * (w ^ 4 * L ^ 21 * M ^ 28) := by
        dsimp only [F]; ring
      _ < pairWindowConstant Kp C0 Cg ^ 4 * (w ^ 4 * L ^ 21 * M ^ 28) :=
        Nat.mul_lt_mul_of_pos_right coefficient (by positivity)
      _ = _ := by ring
  have powers : a ^ 4 < (h * s * u * R) ^ 4 :=
    Nat.lt_of_mul_lt_mul_left (strict.trans_le (cap.trans nupper))
  by_contra fail
  have backwards : h * s * u * R ≤ a := by omega
  exact (not_le_of_gt powers) (Nat.pow_le_pow_left backwards 4)

/-! ## Window geometry at selected parameters -/

def pairGrowthConstant : ℕ := 32 ^ 3 * (16 ^ 3 * 48 ^ 4)

theorem inner_log_bound (cT n : ℕ) (muPositive : 0 < Target.mu n) :
    inner cT n ≤ (cT + 5) * Target.lambda n * Target.mu n := by
  have coefficient : 3 * Target.mu n + cT + 2 ≤ (cT + 5) * Target.mu n := by
    nlinarith only [muPositive]
  have scaled := Nat.mul_le_mul_right (Target.lambda n) coefficient
  rw [inner_eq]
  nlinarith only [scaled]

theorem rootRadius_bound (n k : ℕ) (large : 4 ≤ n) (passed : DegreePass n k (outer n k) 0) :
    0 < Nat.sqrt (n - k + 1) ∧ n ≤ 8 * Nat.sqrt (n - k + 1) ^ 2 := by
  have powers : 2 ^ (100 * (k + 2)) ≤ 2 ^ outer n k := by
    simpa only [DegreePass, mul_zero, pow_zero, mul_one] using passed
  have exponents : 100 * (k + 2) ≤ outer n k := by
    by_contra fail
    have smaller : outer n k < 100 * (k + 2) := by omega
    have strict := Nat.pow_lt_pow_right (by decide : 1 < 2) smaller
    omega
  have outerBound := outer_le_succ n k
  have innerSmall : 2 * k ≤ n := by omega
  let q := n - k + 1
  have qPositive : 1 ≤ q := by dsimp only [q]; omega
  have rootPositive : 1 ≤ Nat.sqrt q := Nat.le_sqrt'.mpr (by simpa using qPositive)
  have upper := Nat.lt_succ_sqrt' q
  have nBound : n ≤ 2 * q := by dsimp only [q]; omega
  have square : (Nat.sqrt q + 1) ^ 2 ≤ 4 * (Nat.sqrt q) ^ 2 := by
    nlinarith only [rootPositive]
  have paid : n ≤ 8 * (Nat.sqrt q) ^ 2 := by
    nlinarith only [nBound, upper, square]
  exact ⟨by change 0 < Nat.sqrt q; omega, paid⟩

theorem height_scaled (P : ℕ) (large : 8 ≤ P) :
    0 < Nat.sqrt (2 * (P / 4) ^ 2) ∧ P ≤ 8 * Nat.sqrt (2 * (P / 4) ^ 2) := by
  have bounds := height_bounds P
  have remainder := Nat.mod_lt P (by decide : 0 < 4)
  have division := Nat.mod_add_div P 4
  have divided : 1 ≤ P / 4 := by omega
  exact ⟨by omega, by omega⟩

theorem scalar_side_dominates (P L s : ℕ) (_positive : 0 < P)
    (paid : 32 * L ≤ P) (growth : P ^ 2 ≤ 32 * s * L) : P ≤ s := by
  have multiply := Nat.mul_le_mul_right s paid
  have bound : P ^ 2 ≤ P * s := growth.trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using multiply)
  by_contra fail
  have smaller : s < P := by omega
  nlinarith only [bound, smaller]

theorem pair_side_dominates (P L side : ℕ) (large : 2 ≤ P)
    (paid : pairGrowthConstant * L ^ 3 ≤ P)
    (growth : P ^ 6 ≤ pairGrowthConstant * L ^ 3 * side ^ 4) : P < side := by
  by_contra fail
  have smaller : side ≤ P := by omega
  have upper : P ^ 6 ≤ P ^ 5 := by
    calc
      _ ≤ pairGrowthConstant * L ^ 3 * side ^ 4 := growth
      _ ≤ P * P ^ 4 := Nat.mul_le_mul paid (Nat.pow_le_pow_left smaller 4)
      _ = _ := by ring
  have backward : P ^ 6 < P ^ 6 := by
    exact upper.trans_lt (Nat.pow_lt_pow_right (by omega : 1 < P) (by decide : 5 < 6))
  exact (lt_irrefl _) backward

structure WindowGeometry (B1 cT : ℕ) (hd : Header) (p : Params) : Prop where
  lambdaPositive : 0 < Target.lambda hd.n
  muPositive : 0 < Target.mu hd.n
  time : p.T ≤ tCoefficient B1 cT * Target.lambda hd.n * Target.mu hd.n
  innerBound : p.k ≤ (cT + 5) * Target.lambda hd.n * Target.mu hd.n
  prime : hd.n ≤ primeCoefficient cT * Target.lambda hd.n * (Target.mu hd.n) ^ 2 * p.P
  rootPositive : 0 < p.R0
  root : hd.n ≤ 8 * p.R0 ^ 2
  heightPositive : 0 < p.h
  height : p.P ≤ 8 * p.h
  sidePositive : 0 < p.Lw - 1
  heightGap : p.h ≤ p.Lw - 1
  scalar : hd.pair = false → p.P ^ 2 ≤ 32 * (p.Lw - 1) * Target.lambda hd.n
  pair : hd.pair = true → p.P ^ 6 ≤ pairGrowthConstant * (Target.lambda hd.n) ^ 3 * (2 * (p.Lw - 1)) ^ 4

theorem window_geometry_eventually (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem)
    (B1 cT : ℕ) : ∃ onset : ℕ, ∀ (hd : Header) (p : Params), HeaderOK B1 hd → onset ≤ hd.n →
      selectParams cT hd = some p → WindowGeometry B1 cT hd p := by
  obtain ⟨a, _, scalar⟩ := dyadic_window_growth source
  obtain ⟨b, _, pair⟩ := dyadic_pair_growth source
  obtain ⟨e0, e0Bound, data⟩ := eventual_data source B1 cT
  let required := max a b
  obtain ⟨d, _, sideWork⟩ := polynomial_lambda_binary pairGrowthConstant 3
  let onset := max e0 (max d (2 ^ (4 * required)))
  refine ⟨onset, ?_⟩
  intro hd p hok large success
  have eLarge : e0 ≤ hd.n := (le_max_left _ _).trans large
  have dLarge : d ≤ hd.n := (le_max_left _ _).trans ((le_max_right _ _).trans large)
  have sourceLarge : 2 ^ (4 * required) ≤ hd.n := (le_max_right _ _).trans ((le_max_right _ _).trans large)
  obtain ⟨q, hq, binaryQ, nBound, timeBound, logLarge⟩ := data hd hok eLarge
  have hqp : q = p := Option.some.inj (hq.symm.trans success)
  subst hqp
  have hs := selectParams_spec cT hd q success
  have nLarge : 65536 ≤ hd.n := e0Bound.trans eLarge
  have lambdaPositive : 0 < Target.lambda hd.n := by omega
  have muPositive : 0 < Target.mu hd.n := Nat.clog_pos (by decide : 1 < 2) (by omega)
  have PLarge : 100 ≤ q.P := hs.P_large
  have PSmall : q.P ≤ hd.n := by
    rw [hs.P_eq]; exact (Nat.findGreatest_le _).trans (Nat.min_le_left _ _)
  have PRequired : required ≤ q.P := by
    have monotone := Nat.clog_mono_right 2 sourceLarge
    have logSource : 4 * required ≤ Target.lambda hd.n := by
      simpa only [Nat.clog_pow, show 1 < 2 by decide, if_pos, Target.lambda] using monotone
    have scale : required ≤ Target.lambda hd.n / 4 := by omega
    exact Nat.lt_two_pow_self.le.trans ((Nat.pow_le_pow_right (by decide : 0 < 2) scale).trans binaryQ)
  have hwin : q.window = ScalarWindow.window (dyadicPrimes q.P) := by rw [hs.window_eq, hs.primes_eq]
  have scalarBound := scalar q.P hd.n ((le_max_left _ _).trans PRequired) PSmall
  obtain ⟨pairPositive, pairBound⟩ := pair q.P hd.n ((le_max_right _ _).trans PRequired) PSmall
  have paidPair : pairGrowthConstant * (Target.lambda hd.n) ^ 3 ≤ q.P :=
    (sideWork hd.n dLarge).2.trans binaryQ
  have cubicLog : Target.lambda hd.n ≤ (Target.lambda hd.n) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right lambdaPositive (by decide : 1 ≤ 3)
  have paidScalar : 32 * Target.lambda hd.n ≤ q.P := by
    calc
      _ ≤ pairGrowthConstant * Target.lambda hd.n := Nat.mul_le_mul_right _
        (by norm_num [pairGrowthConstant] : 32 ≤ pairGrowthConstant)
      _ ≤ pairGrowthConstant * (Target.lambda hd.n) ^ 3 := Nat.mul_le_mul_left _ cubicLog
      _ ≤ _ := paidPair
  have scalarGap := scalar_side_dominates q.P (Target.lambda hd.n)
    (ScalarWindow.window (dyadicPrimes q.P) - 1) (by omega) paidScalar scalarBound
  have pairGap := pair_side_dominates q.P (Target.lambda hd.n)
    (pairSide (ScalarWindow.window (dyadicPrimes q.P))) (by omega) paidPair pairBound
  have hh : q.h = Nat.sqrt (2 * (q.P / 4) ^ 2) := by rw [hs.h_eq, hs.hE_eq]
  have heights := height_scaled q.P (by omega)
  rw [← hh] at heights
  have hR : q.R0 = Nat.sqrt (hd.n - q.k + 1) := hs.R0_eq
  have hzero := hs.zero_pass
  rw [hs.m_eq] at hzero
  have root := rootRadius_bound hd.n q.k hok.1 hzero
  rw [← hR] at root
  have hupper : q.h ≤ q.P := by rw [hh]; exact (height_bounds q.P).2
  have hLw : q.Lw = windowInUse hd.pair (pairSide (ScalarWindow.window (dyadicPrimes q.P)))
      (ScalarWindow.window (dyadicPrimes q.P)) := by rw [hs.Lw_eq, hs.L2_eq, hwin]
  have gap : q.h ≤ q.Lw - 1 := by
    rw [hLw]
    unfold windowInUse
    cases hd.pair <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  refine ⟨lambdaPositive, muPositive, ?_, ?_, nBound, root.1, root.2, heights.1, heights.2, ?_, gap, ?_, ?_⟩
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using timeBound
  · rw [hs.k_eq]; exact inner_log_bound cT hd.n muPositive
  · have := heights.1; omega
  · intro hp
    rw [hLw]
    simpa only [windowInUse, hp, Bool.false_eq_true, if_false] using scalarBound
  · intro hp
    rw [hLw]
    have retained : pairSide (ScalarWindow.window (dyadicPrimes q.P)) ≤
        2 * (pairSide (ScalarWindow.window (dyadicPrimes q.P)) - 1) := by omega
    simpa only [windowInUse, hp, if_true, pairGrowthConstant] using
      pairBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left retained 4))

/-! ## The caps pay the live term (proof of thm:pair-uniform, lines 1909–1934) -/

def liveCoefficient (B1 cT : ℕ) : ℕ := 244 * tCoefficient B1 cT * (cT + 5)

def scalarConstant (B1 cT : ℕ) : ℕ := scalarWindowConstant (primeCoefficient cT) (liveCoefficient B1 cT)

def pairConstant (B1 cT : ℕ) : ℕ :=
  pairWindowConstant (primeCoefficient cT) (liveCoefficient B1 cT) pairGrowthConstant

/-- The pair cap `W ≤ β 𝒜₃(n)/K`, raised to the fourth power. -/
def PairCapQ (K : ℕ) (hd : Header) : Prop :=
  ((K * hd.W * (Target.mu hd.n) ^ 7 : ℕ) : ℚ) ^ 4 * ((Target.lambda hd.n : ℕ) : ℚ) ^ 21 ≤
    (hd.n : ℚ) ^ 12 * hd.beta ^ 4

/-- The scalar cap `W ≤ β 𝒜₁(n)/K`, squared. -/
def ScalarCapQ (K : ℕ) (hd : Header) : Prop :=
  ((K * hd.W * (Target.lambda hd.n) ^ 6 * (Target.mu hd.n) ^ 8 : ℕ) : ℚ) ^ 2 ≤ (hd.n : ℚ) ^ 7 * hd.beta ^ 2

theorem Spec.T_pos {cT : ℕ} {hd : Header} {p : Params} (hs : Spec cT hd p) (hβ : hd.beta ≤ 1 / 16) : 0 < p.T := by
  have hpass := hs.T_pass
  by_contra h0
  have hT0 : p.T = 0 := by omega
  rw [hT0] at hpass
  unfold TPass at hpass
  have h1 : (1 : ℚ) ≤ ((4 * Jmax hd.n * 2 ^ p.k : ℕ) : ℚ) := by
    have : 1 ≤ 4 * Jmax hd.n * 2 ^ p.k := Nat.succ_le_iff.mpr (by unfold Jmax; positivity)
    exact_mod_cast this
  simp only [pow_zero, one_mul] at hpass
  linarith

theorem num_natAbs_cast (β : ℚ) (hβ : 0 < β) : ((β.num.natAbs : ℕ) : ℚ) = β * β.den := by
  rw [Rat.mul_den_eq_num]
  have h : 0 ≤ β.num := (Rat.num_pos.mpr hβ).le
  rw [Nat.cast_natAbs]
  push_cast
  exact abs_of_nonneg (by exact_mod_cast h)

theorem useful_of_geometry {B1 cT : ℕ} {hd : Header} {p : Params} (hs : Spec cT hd p) (hok : HeaderOK B1 hd)
    (geometry : WindowGeometry B1 cT hd p)
    (cap : if hd.pair then PairCapQ (pairConstant B1 cT) hd else ScalarCapQ (scalarConstant B1 cT) hd) :
    244 * (p.T : ℚ) * ellBar p.ell0 p.h p.T < (p.h : ℚ) * ((p.Lw : ℚ) - 1) := by
  have hβ := hok.beta_pos
  set u := hd.beta.num.natAbs with hu
  set den := hd.beta.den with hden
  have hucast : (u : ℚ) = hd.beta * den := num_natAbs_cast hd.beta hβ
  have denpos : (0 : ℚ) < den := by exact_mod_cast hd.beta.den_pos
  have upos : 0 < u := by
    have h : (0 : ℚ) < u := by rw [hucast]; positivity
    exact_mod_cast h
  have coefficientPositive : 0 < primeCoefficient cT := by dsimp only [primeCoefficient]; positivity
  have live : 244 * p.T * hd.W * p.k * den ≤
      liveCoefficient B1 cT * (hd.W * den) * (Target.lambda hd.n) ^ 2 * (Target.mu hd.n) ^ 2 := by
    calc
      _ = 244 * (p.T * p.k) * (hd.W * den) := by ring
      _ ≤ 244 * ((tCoefficient B1 cT * Target.lambda hd.n * Target.mu hd.n) *
          ((cT + 5) * Target.lambda hd.n * Target.mu hd.n)) * (hd.W * den) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul geometry.time geometry.innerBound))
      _ = _ := by dsimp only [liveCoefficient]; ring
  have cross : 244 * p.T * hd.W * p.k * den < p.h * (p.Lw - 1) * u * p.R0 := by
    cases hp : hd.pair with
    | false =>
      have capQ : ScalarCapQ (scalarConstant B1 cT) hd := by simpa only [hp, Bool.false_eq_true, if_false] using cap
      have actualCap : (scalarWindowConstant (primeCoefficient cT) (liveCoefficient B1 cT) *
          (hd.W * den) * (Target.lambda hd.n) ^ 6 * (Target.mu hd.n) ^ 8) ^ 2 ≤ hd.n ^ 7 * u ^ 2 := by
        have hq : ((scalarConstant B1 cT * hd.W * (Target.lambda hd.n) ^ 6 * (Target.mu hd.n) ^ 8 : ℕ) : ℚ) ^ 2 *
            (den : ℚ) ^ 2 ≤ (hd.n : ℚ) ^ 7 * hd.beta ^ 2 * (den : ℚ) ^ 2 :=
          mul_le_mul_of_nonneg_right capQ (by positivity)
        have : ((scalarWindowConstant (primeCoefficient cT) (liveCoefficient B1 cT) *
            (hd.W * den) * (Target.lambda hd.n) ^ 6 * (Target.mu hd.n) ^ 8 : ℕ) : ℚ) ^ 2 ≤
            ((hd.n ^ 7 * u ^ 2 : ℕ) : ℚ) := by
          push_cast
          rw [hucast]
          simp only [scalarConstant] at hq
          push_cast at hq
          nlinarith [hq]
        exact_mod_cast this
      exact scalar_window_nat hd.n (Target.lambda hd.n) (Target.mu hd.n) p.P p.h (p.Lw - 1)
        p.R0 u (hd.W * den) _ (primeCoefficient cT) (liveCoefficient B1 cT)
        geometry.lambdaPositive geometry.muPositive coefficientPositive geometry.heightPositive
        geometry.sidePositive geometry.rootPositive upos geometry.prime geometry.root
        geometry.height (geometry.scalar hp) live actualCap
    | true =>
      have capQ : PairCapQ (pairConstant B1 cT) hd := by simpa only [hp, if_true] using cap
      have actualCap : (pairWindowConstant (primeCoefficient cT) (liveCoefficient B1 cT) pairGrowthConstant *
          (hd.W * den) * (Target.mu hd.n) ^ 7) ^ 4 * (Target.lambda hd.n) ^ 21 ≤ hd.n ^ 12 * u ^ 4 := by
        have hq : ((pairConstant B1 cT * hd.W * (Target.mu hd.n) ^ 7 : ℕ) : ℚ) ^ 4 *
            ((Target.lambda hd.n : ℕ) : ℚ) ^ 21 * (den : ℚ) ^ 4 ≤ (hd.n : ℚ) ^ 12 * hd.beta ^ 4 * (den : ℚ) ^ 4 :=
          mul_le_mul_of_nonneg_right capQ (by positivity)
        have : ((pairWindowConstant (primeCoefficient cT) (liveCoefficient B1 cT) pairGrowthConstant *
            (hd.W * den) * (Target.mu hd.n) ^ 7) ^ 4 * (Target.lambda hd.n) ^ 21 : ℕ) ≤
            ((hd.n ^ 12 * u ^ 4 : ℕ) : ℚ) := by
          push_cast
          rw [hucast]
          simp only [pairConstant] at hq
          push_cast at hq
          nlinarith [hq]
        exact_mod_cast this
      exact pair_window_nat hd.n (Target.lambda hd.n) (Target.mu hd.n) p.P p.h (p.Lw - 1)
        p.R0 u (hd.W * den) _ (primeCoefficient cT) (liveCoefficient B1 cT) pairGrowthConstant
        geometry.lambdaPositive geometry.muPositive coefficientPositive (by norm_num [pairGrowthConstant])
        geometry.heightPositive geometry.sidePositive geometry.rootPositive upos
        geometry.prime geometry.root geometry.height (geometry.pair hp) live actualCap
  have Tpos : 0 < p.T := hs.T_pos hok.2.2.2
  have TQ : (0 : ℚ) < p.T := by exact_mod_cast Tpos
  have hQ : (0 : ℚ) < p.h := by exact_mod_cast geometry.heightPositive
  have RQ : (0 : ℚ) < p.R0 := by exact_mod_cast geometry.rootPositive
  have sideOne : 1 ≤ p.Lw := by have := geometry.sidePositive; omega
  have sideCast : ((p.Lw - 1 : ℕ) : ℚ) = (p.Lw : ℚ) - 1 := by
    simp only [Nat.cast_sub sideOne, Nat.cast_one]
  have initialBound : 244 * (p.T : ℚ) * p.ell0 < (p.h : ℚ) * ((p.Lw : ℚ) - 1) := by
    rw [hs.ell0_eq]
    have uQ : (0 : ℚ) < u := by exact_mod_cast upos
    have hβeq : hd.beta = (u : ℚ) / den := by rw [hucast]; field_simp
    rw [hβeq]
    have casted : (244 : ℚ) * p.T * hd.W * p.k * den < (p.h : ℚ) * ((p.Lw - 1 : ℕ) : ℚ) * u * p.R0 := by
      exact_mod_cast cross
    rw [sideCast] at casted
    have hk : ((hd.W * p.k : ℕ) : ℚ) = (hd.W : ℚ) * p.k := by push_cast; ring
    rw [hk]
    rw [show (244 : ℚ) * p.T * ((hd.W : ℚ) * p.k / ((u : ℚ) / den * p.R0)) =
      (244 * p.T * hd.W * p.k * den) / (u * p.R0) by field_simp]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have gapQ : (p.h : ℚ) ≤ (p.Lw : ℚ) - 1 := by rw [← sideCast]; exact_mod_cast geometry.heightGap
  have baseBound : 244 * (p.T : ℚ) * ((p.h : ℚ) ^ 2 / (256 * p.T)) < (p.h : ℚ) * ((p.Lw : ℚ) - 1) := by
    have factor : 244 * (p.T : ℚ) * ((p.h : ℚ) ^ 2 / (256 * p.T)) = (61 / 64 : ℚ) * (p.h : ℚ) ^ 2 := by
      field_simp
      ring
    rw [factor]
    have scaled := mul_le_mul_of_nonneg_left gapQ hQ.le
    nlinarith only [scaled, hQ]
  unfold ellBar
  rcases le_total p.ell0 ((p.h : ℚ) ^ 2 / (256 * p.T)) with order | order
  · rw [max_eq_right order]; exact baseBound
  · rw [max_eq_left order]; exact initialBound

/-- eq:window-condition under the caps, for all large `n` (proof of thm:pair-uniform). -/
theorem useful_window (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) (B1 cT : ℕ) :
    ∃ onset : ℕ, ∀ (hd : Header) (p : Params), HeaderOK B1 hd → onset ≤ hd.n → selectParams cT hd = some p →
      (if hd.pair then PairCapQ (pairConstant B1 cT) hd else ScalarCapQ (scalarConstant B1 cT) hd) →
        244 * (p.T : ℚ) * ellBar p.ell0 p.h p.T < (p.h : ℚ) * ((p.Lw : ℚ) - 1) := by
  obtain ⟨onset, geometry⟩ := window_geometry_eventually source B1 cT
  exact ⟨onset, fun hd p hok hn hsel cap =>
    useful_of_geometry (selectParams_spec cT hd p hsel) hok (geometry hd p hok hn hsel) cap⟩

end NearCubicGates.Close.Counter
