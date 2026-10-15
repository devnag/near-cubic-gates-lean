import Proof.Gates.Dispatch.ParamsW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces

variable {C : Ctx}

def paramsP (cT : ℕ) : St VV := .seq (pS0 cT) (.seq (guard pS1) (.seq (guard pS2) (.seq (guard pS3) (guard pS4))))

def paramsT : List (Fin VV) := s0T ++ s1T ++ s2T ++ s3T ++ s4T ++ [vJ]

/-- The parameter variables hold the fields of `p`. -/
structure PV (p : Params) (b : DS VV) : Prop where
  n : b.env vN = p.n
  W : b.env pW = p.W
  k : b.env pK = p.k
  T : b.env pT = p.T
  m : b.env pM = p.m
  Dmax : b.env pDM = p.Dmax
  P : b.env pP = p.P
  e : b.env pE = p.e
  card : b.env pNP = p.primes.card
  window : b.env pWIN = p.window
  L2 : b.env pL2 = p.L2
  Lw : b.env pLW = p.Lw
  hE : b.env pHE = p.hE
  h : b.env pH = p.h
  R0 : b.env pR0 = p.R0
  en : p.ell0.num = (b.env pEN : ℤ)
  ed : p.ell0.den = b.env pED
  M1 : b.env pM1 = p.M1
  J : b.env pJ = p.J
  A : b.env pA = p.A
  Lam : b.env pLB = p.Lambda
  JM : b.env pJM = Jmax p.n
  lam : b.env pLAM = Target.lambda p.n
  x1 : firstRatio p.ell0 p.h p.T = (b.env pXN : ℚ) / b.env pXD
  xn : 0 < b.env pXN
  xnd : b.env pXN ≤ b.env pXD
  xd : b.env pXD ≤ (p.h + 32) * b.env pXN

/-! ## Failed exits skip the remaining stages -/

/-- A failed run: flag zero, `selectParams = none`. -/
def PFail (cT : ℕ) (c : Call) (a b : DS VV) : Prop :=
  b.env vADM = 0 ∧ selectParams cT (header c) = none ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
    FrS a b paramsT

theorem guard_fail (cT : ℕ) (c : Call) (a : DS VV) (X : St VV) (b : DS VV) (hb : PFail cT c a b) :
    Hs C (guard X) b 3 (PFail cT c a) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb
  refine Hs.ite (show vADM ≠ v1 by decide) (fun he => ?_) (fun _ => ?_)
  · exfalso; simp [Cnd.eval, b1, b6.one] at he
  · refine Hs.mono (skip_spec b) (by omega) ?_
    rintro g rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide), b1], b2, b3, b4, b5, Cst.set b6 _ _ (by decide),
      FrS.trans b7 (Fr.toS (Fr.set _ _ (by decide)))⟩

theorem fail_G4 (cT : ℕ) (c : Call) (a b : DS VV) (hb : PFail cT c a b) :
    Hs C (guard pS4) b 3 (PFail cT c a) := guard_fail cT c a _ b hb

theorem fail_G34 (cT : ℕ) (c : Call) (a b : DS VV) (hb : PFail cT c a b) :
    Hs C (.seq (guard pS3) (guard pS4)) b 7 (PFail cT c a) :=
  Hs.seq (guard_fail cT c a _ b hb) (fun d hd => fail_G4 cT c a d hd)

theorem fail_G234 (cT : ℕ) (c : Call) (a b : DS VV) (hb : PFail cT c a b) :
    Hs C (.seq (guard pS2) (.seq (guard pS3) (guard pS4))) b 11 (PFail cT c a) :=
  Hs.seq (guard_fail cT c a _ b hb) (fun d hd => fail_G34 cT c a d hd)

theorem fail_G1234 (cT : ℕ) (c : Call) (a b : DS VV) (hb : PFail cT c a b) :
    Hs C (.seq (guard pS1) (.seq (guard pS2) (.seq (guard pS3) (guard pS4)))) b 15 (PFail cT c a) :=
  Hs.seq (guard_fail cT c a _ b hb) (fun d hd => fail_G234 cT c a d hd)

/-! ## Widths -/

section Widths
variable {B Wd : ℕ}

theorem lt_pow_mul_le {x y a b : ℕ} (hx : x < 2 ^ a) (hy : y ≤ 2 ^ b) : x * y < 2 ^ (a + b) := by
  rw [pow_add]
  rcases Nat.eq_zero_or_pos y with h | h
  · rw [h, mul_zero]; positivity
  · exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx h) (Nat.mul_le_mul_left _ hy)

theorem big_lin (hB : 4 ≤ B) (hBig : 4000 * B ^ 2 ≤ Wd) : 4000 * B ≤ Wd := by
  have := (B_pows B (by omega)).1; omega

theorem B_lt (B : ℕ) : B < 2 ^ B := Nat.lt_two_pow_self

theorem tbound_le (k J den : ℕ) (β : ℚ) (hβ : β.den = den) (hk : k ≤ B) (hJ : J ≤ B) (hden : den < 2 ^ B)
    (hJ1 : 1 ≤ J) : TBound k J β ≤ 3 * B + 2 := by
  unfold TBound
  rw [hβ]
  have h1 : 4 * J * den < 2 ^ (B + 2 + B) := by
    have : 4 * J < 2 ^ (B + 2) := by
      have := B_lt B; rw [pow_add]; omega
    exact lt_pow_mul this hden
  have hd : 1 ≤ den := by rw [← hβ]; exact β.den_pos
  have h2 : Nat.log 2 (4 * J * den) < B + 2 + B :=
    Nat.log_lt_of_lt_pow (by positivity) h1
  omega

theorem w_s0 (n cT Wc : ℕ) (hn : n + cT + 4 ≤ B) (hB : 4 ≤ B) (hWc : Wc ≤ 2 * n ^ 4)
    (hBig : 4000 * B ^ 2 ≤ Wd) : (3 * n + cT + 4) * (n + 1) + Wc + 2 * n + 4 < 2 ^ Wd := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := B_pows B (by omega)
  have h1 : (3 * n + cT + 4) * (n + 1) ≤ 3 * B * B := Nat.mul_le_mul (by omega) (by omega)
  have h2 : n ^ 4 ≤ B ^ 4 := pow_mono_B (by omega) 4
  have e : 3 * B * B = 3 * B ^ 2 := by ring
  refine pw (c := 8) (d := 4) (B := B) ?_ (by have := big_lin hB hBig; omega)
  omega

theorem w_s1 (n k J den num : ℕ) (β : ℚ) (hβ : β.den = den) (hk : k < n) (hn : n + 1 ≤ B) (hJ : J ≤ B)
    (hJ1 : 1 ≤ J) (hden : den < 2 ^ B) (hnum : num < 2 ^ B) (hB : 4 ≤ B) (hBig : 4000 * B ^ 2 ≤ Wd) :
    k < Wd ∧ 4 * J * 2 ^ k * den < 2 ^ Wd ∧ 2 ^ TBound k J β * num < 2 ^ Wd ∧ TBound k J β + 2 < Wd ∧
    100 * (k + 2) + 2 * n + 4 < 2 ^ Wd := by
  have hl := big_lin hB hBig
  have ht := tbound_le k J den β hβ (by omega) hJ (by omega) hJ1
  refine ⟨by omega, ?_, ?_, by omega, ?_⟩
  · have h4 : 4 * J < 2 ^ (B + 2) := by have := B_lt B; rw [pow_add]; omega
    have h5 : 4 * J * 2 ^ k < 2 ^ (B + 2 + B) := lt_pow_mul_le h4 (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact lt_pow_mono (lt_pow_mul h5 hden) (by omega)
  · have : 2 ^ TBound k J β * num < 2 ^ (3 * B + 2 + B) := by
      rw [mul_comm]; rw [show 3 * B + 2 + B = B + (3 * B + 2) by ring]
      exact lt_pow_mul_le hnum (Nat.pow_le_pow_right (by norm_num) ht)
    exact lt_pow_mono this (by omega)
  · refine pw (c := 210) (d := 1) (B := B) ?_ (by omega)
    rw [pow_one]; omega

theorem ubase_le (n m : ℕ) (hn : n + 1 ≤ B) (hm : m ≤ B) (hB : 4 ≤ B) :
    Bb n m ≤ 6 * B ^ 2 ∧ Ubase n m ≤ 30 * B ^ 8 := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := B_pows B (by omega)
  have c1 : Nat.clog 2 (n + 1) ≤ n + 1 := clog_le_self _
  have c2 : Nat.clog 2 (m + 1) ≤ m + 1 := clog_le_self _
  have hB0 : B0 n ≤ 4 * B * B := by unfold B0; exact Nat.mul_le_mul (by omega) (by omega)
  have e1 : 4 * B * B = 4 * B ^ 2 := by ring
  have q4 : 4 * B ≤ B ^ 2 := by nlinarith
  have hBb : Bb n m ≤ 6 * B ^ 2 := by unfold Bb; omega
  refine ⟨hBb, ?_⟩
  have hmT : mT n m ≤ 1 + 6 * B ^ 4 := by
    unfold mT
    have : Bb n m * m * ((m + 1) / 2) ≤ 6 * B ^ 2 * B * B :=
      Nat.mul_le_mul (Nat.mul_le_mul hBb hm) (by omega)
    have e : 6 * B ^ 2 * B * B = 6 * B ^ 4 := by ring
    omega
  unfold Ubase G0
  have h4 : n ^ 4 ≤ B ^ 4 := pow_mono_B (by omega) 4
  have : 2 * (2 * n ^ 4) * mT n m ≤ 4 * B ^ 4 * (1 + 6 * B ^ 4) := by
    calc 2 * (2 * n ^ 4) * mT n m = 4 * n ^ 4 * mT n m := by ring
      _ ≤ 4 * B ^ 4 * (1 + 6 * B ^ 4) := Nat.mul_le_mul (by omega) hmT
  have e2 : 4 * B ^ 4 * (1 + 6 * B ^ 4) = 4 * B ^ 4 + 24 * B ^ 8 := by ring
  omega

theorem w_s2 (n k m J Dm : ℕ) (hk : k < n) (hn : n + 4 ≤ B) (hm : m ≤ n + 1) (hJ : J ≤ n + 1) (hDm : Dm ≤ m)
    (hB : 4 ≤ B) (hBig : 4000 * B ^ 2 ≤ Wd) :
    4 * Ubase n m + 4 * n + 4 * m + 4 * Bb n m + 16 < 2 ^ Wd ∧ 100 * (k + 2) + m + 1 < Wd ∧
    2 ^ (100 * (k + 2)) * Ubase n m ^ (100 * m) < 2 ^ Wd ∧ 100 * m + 200 < 2 ^ Wd ∧ 3 * k + 4 < Wd ∧
    (∀ j ≤ 2 * (k + 1), n ^ j < 2 ^ Wd) ∧ (4 * k + 4) * (2 * J + 2) * n + Dm + 4 < 2 ^ Wd := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := B_pows B (by omega)
  have hl := big_lin hB hBig
  obtain ⟨hBb, hU⟩ := ubase_le n m (B := B) (by omega) (by omega) hB
  have hB8 : B ≤ B ^ 8 := by omega
  refine ⟨?_, by omega, ?_, ?_, by omega, ?_, ?_⟩
  · exact pw (c := 200) (d := 8) (B := B) (by omega) (by omega)
  · have hU' : Ubase n m < 2 ^ (30 + 8 * B) := pw (c := 30) (d := 8) (B := B) hU le_rfl
    have h1 : Ubase n m ^ (100 * m) ≤ 2 ^ ((30 + 8 * B) * (100 * B)) := pow_le_of_lt _ _ _ _ hU' (by omega)
    have h2 : (2 : ℕ) ^ (100 * (k + 2)) ≤ 2 ^ (100 * (B + 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (100 * (k + 2)) * Ubase n m ^ (100 * m) ≤ 2 ^ (100 * (B + 2) + (30 + 8 * B) * (100 * B)) := by
      rw [pow_add]; exact Nat.mul_le_mul h2 h1
    refine lt_of_le_of_lt h3 (Nat.pow_lt_pow_right (by norm_num) ?_)
    have e : 100 * (B + 2) + (30 + 8 * B) * (100 * B) = 800 * B ^ 2 + 3100 * B + 200 := by ring
    rw [e]; nlinarith
  · exact pw (c := 300) (d := 1) (B := B) (by rw [pow_one]; omega) (by omega)
  · intro j hj
    have : n ^ j ≤ 2 ^ (B * (2 * B + 2)) := pow_le_of_lt _ _ _ _ (lt_of_le_of_lt (by omega) (B_lt B)) (by omega)
    refine lt_of_le_of_lt this (Nat.pow_lt_pow_right (by norm_num) ?_)
    have e : B * (2 * B + 2) = 2 * B ^ 2 + 2 * B := by ring
    omega
  · have h1 : (4 * k + 4) * (2 * J + 2) * n ≤ 4 * B * (3 * B) * B :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    have e : 4 * B * (3 * B) * B = 12 * B ^ 3 := by ring
    exact pw (c := 20) (d := 3) (B := B) (by omega) (by omega)

theorem w_s3 (n k P T : ℕ) (hk : k < n) (hn : n + 4 ≤ B) (hP : P ≤ n) (hT : T ≤ 3 * B + 2) (hB : 4 ≤ B)
    (hBig : 4000 * B ^ 2 ≤ Wd) :
    2 * (P + 1) * (P + 1) + 8 < 2 ^ Wd ∧
    2 * (ScalarWindow.window (dyadicPrimes P) * (ScalarWindow.window (dyadicPrimes P) *
      ScalarWindow.window (dyadicPrimes P))) + 2 * ScalarWindow.window (dyadicPrimes P) + 8 < 2 ^ Wd ∧
    4 * (n + 1) * (n + 1) * ((n + 1) * (n + 1)) + 16 < 2 ^ Wd ∧ 64 * T + 2 * k + 300 < 2 ^ Wd := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := B_pows B (by omega)
  have hl := big_lin hB hBig
  have hD : ScalarWindow.window (dyadicPrimes P) ≤ B ^ 2 :=
    le_trans (window_le P) (by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega))
  have hB6 : B ^ 2 * (B ^ 2 * B ^ 2) = B ^ 6 := by ring
  have hB46 : B ^ 4 ≤ B ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (P + 1) * (P + 1) ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
    have e : B * B = B ^ 2 := by ring
    have e' : 2 * (P + 1) * (P + 1) = 2 * ((P + 1) * (P + 1)) := by ring
    exact pw (c := 20) (d := 2) (B := B) (by omega) (by omega)
  · have h3 : ScalarWindow.window (dyadicPrimes P) * (ScalarWindow.window (dyadicPrimes P) *
        ScalarWindow.window (dyadicPrimes P)) ≤ B ^ 2 * (B ^ 2 * B ^ 2) := Nat.mul_le_mul hD (Nat.mul_le_mul hD hD)
    exact pw (c := 20) (d := 6) (B := B) (by omega) (by omega)
  · have : (n + 1) * (n + 1) * ((n + 1) * (n + 1)) ≤ B * B * (B * B) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul (by omega) (by omega))
    have e : B * B * (B * B) = B ^ 4 := by ring
    have e2 : 4 * (n + 1) * (n + 1) * ((n + 1) * (n + 1)) = 4 * ((n + 1) * (n + 1) * ((n + 1) * (n + 1))) := by ring
    exact pw (c := 30) (d := 4) (B := B) (by omega) (by omega)
  · exact pw (c := 600) (d := 1) (B := B) (by rw [pow_one]; omega) (by omega)

theorem w_s4 (n Wc k den num R0 h T Lw J : ℕ) (hWc : Wc ≤ 2 * n ^ 4) (hk : k < n) (hn : n + 4 ≤ B)
    (hden : den < 2 ^ B) (hnum : num < 2 ^ B) (hR : R0 ≤ n + 1) (hh : h ≤ n) (hT : T ≤ 3 * B + 2)
    (hLw : Lw ≤ B ^ 2) (hJ : J ≤ n + 1) (hB : 4 ≤ B) (hBig : 4000 * B ^ 2 ≤ Wd) :
    Wc * k * den < 2 ^ (8 * B) ∧ num * R0 < 2 ^ (8 * B) ∧ h < 2 ^ (8 * B) ∧ T < 2 ^ (8 * B) ∧
    Lw < 2 ^ (8 * B) ∧ J < 2 ^ (8 * B) ∧ 6 * (8 * B) + 40 ≤ Wd := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := B_pows B (by omega)
  have hl := big_lin hB hBig
  have hBl := B_lt B
  have m8 : ∀ x, x ≤ B → x < 2 ^ (8 * B) := fun x hx => lt_pow_mono (lt_of_le_of_lt hx hBl) (by omega)
  refine ⟨?_, ?_, m8 h (by omega), ?_, ?_, m8 J (by omega), by omega⟩
  · have h1 : Wc * k ≤ 2 * B ^ 5 := by
      have : n ^ 4 ≤ B ^ 4 := pow_mono_B (by omega) 4
      calc Wc * k ≤ (2 * B ^ 4) * B := Nat.mul_le_mul (by omega) (by omega)
        _ = 2 * B ^ 5 := by ring
    have h2 : Wc * k < 2 ^ (2 + 5 * B) := pw (c := 2) (d := 5) (B := B) h1 le_rfl
    exact lt_pow_mono (lt_pow_mul h2 hden) (by omega)
  · exact lt_pow_mono (lt_pow_mul hnum (lt_of_le_of_lt (by omega : R0 ≤ B) hBl)) (by omega)
  · exact lt_pow_mono (show T < 2 ^ (3 * B + 2) from lt_of_le_of_lt hT Nat.lt_two_pow_self) (by omega)
  · exact lt_pow_mono (pw (c := 1) (d := 2) (B := B) (x := Lw) (by omega) le_rfl) (by omega)

end Widths

/-! ## Costs -/

theorem s2Cost_mono {n k m B : ℕ} (hn : n ≤ B) (hk : k ≤ B) (hm : m ≤ B) : s2Cost n k m ≤ s2Cost B B B := by
  unfold s2Cost dmaxCost primeCost liftCost; gcongr

theorem s3Cost_mono {n P D B : ℕ} (hn : n ≤ B) (hP : P ≤ B) (hD : D ≤ B ^ 2) :
    s3Cost n P D ≤ s3Cost B B (B ^ 2) := by
  unfold s3Cost primesCost pairCost aCost; gcongr

theorem chainCost_mono {J h B : ℕ} (hJ : J ≤ B) (hh : h ≤ B) : chainCost J h ≤ chainCost B B := by
  unfold chainCost bodyCost; gcongr

def s1Bound (B : ℕ) : ℕ := 5 * B + 900 + 10 * (3 * B + 2) + (3 * B + 5) * (5 * (3 * B + 2) + 60)

def paramsCost (B : ℕ) : ℕ :=
  (22 * B + 200) + (s1Bound B + 2) + (s2Cost B B B + 2) + (s3Cost B B (B ^ 2) + 2) +
    (30 * (8 * B) + 3300 + chainCost B B + 2) + 20

/-! ## The parameter theorem -/

theorem guard_run (X : St VV) (a : DS VV) (hc : Cst a) (hA : a.env vADM = 1) (t : ℕ) (R : DS VV → Prop)
    (h : Hs C X a t R) : Hs C (guard X) a (t + 2) R :=
  guard_spec X a hc t R (fun _ => h) (fun h' => absurd hA h')

theorem bnat_zero_of_not {P : Prop} [Decidable P] (h : ¬ P) : bnat P = 0 := by unfold bnat; simp [h]
theorem bnat_one_of {P : Prop} [Decidable P] (h : P) : bnat P = 1 := by unfold bnat; simp [h]

/-- Admission facts used by the parameters. -/
theorem adm_facts (B1 B2 : ℕ) (c : Call) (hadm : c.Admitted B1 B2) :
    4 ≤ c.n ∧ c.W ≤ 2 * c.n ^ 4 ∧ 0 < c.radius ∧ c.radius ≤ 1 / 16 := by
  obtain ⟨h4, -, -, -, -, -, hWle, hr1, hr2, -, -⟩ := hadm
  refine ⟨h4, hWle, ?_, hr2⟩
  by_contra h
  have h' : c.radius ≤ 0 := not_lt.1 h
  have : c.radius * (c.n : ℚ) ^ B1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h' (by positivity)
  linarith

theorem inner_pos (cT n : ℕ) (hn : 4 ≤ n) : 1 ≤ inner cT n := by
  unfold Counter.inner Jmax
  have : 1 ≤ Target.lambda n := Nat.clog_pos (by norm_num) (by omega)
  nlinarith

theorem jmax_le (n : ℕ) : 1 ≤ Jmax n ∧ Jmax n ≤ n + 1 := by
  unfold Jmax
  have : Target.mu n ≤ n := le_trans (clog_le_self _) (clog_le_self _)
  omega

/-- The postcondition of the parameter program. -/
def ParamsOut (cT : ℕ) (c : Call) (a b : DS VV) : Prop :=
  ((b.env vADM = 0 ∧ selectParams cT (header c) = none) ∨
    (b.env vADM = 1 ∧ ∃ p, selectParams cT (header c) = some p ∧ PV p b ∧
      1024 * b.env pXD + (p.h + 33) * (p.h + 33) + Jmax p.n + 1000 < 2 ^ C.Wd)) ∧
  b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b paramsT

theorem pfail_out (cT : ℕ) (c : Call) (a b : DS VV) (h : PFail cT c a b) : ParamsOut (C := C) cT c a b :=
  ⟨Or.inl ⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem paramsP_spec (B1 B2 cT : ℕ) (c : Call) (a : DS VV) (hc : Cst a) (hp : ParseOut c a)
    (hadm : c.Admitted B1 B2) (hW0 : c.W ≠ 0) (L : ℕ) (hnL : c.n ≤ L) (hnum : c.radius.num.natAbs < 2 ^ L)
    (hden : c.radius.den < 2 ^ L) (hBig : 4000 * (L + cT + 4) ^ 2 ≤ C.Wd) :
    Hs C (paramsP cT) a (paramsCost (L + cT + 4)) (ParamsOut (C := C) cT c a) := by
  set B := L + cT + 4 with hBdef
  have hB4 : 4 ≤ B := by omega
  obtain ⟨h4, hWle, hβ0, hβ16⟩ := adm_facts B1 B2 c hadm
  set n := c.n with hndef
  set k := inner cT n with hkdef
  set β := c.radius with hβdef
  set num := β.num.natAbs with hnumdef
  set den := β.den with hdendef
  have hβn : β.num = (num : ℤ) := (Int.natAbs_of_nonneg (Rat.num_nonneg.2 hβ0.le)).symm
  have hnum1 : 1 ≤ num := by
    have : 0 < β.num := Rat.num_pos.2 hβ0
    omega
  have hden1 : 1 ≤ den := β.den_pos
  have hβq : β = (num : ℚ) / den := by
    rw [← Rat.num_div_den β]; rw [hβn]; push_cast; rfl
  obtain ⟨hJ1, hJn⟩ := jmax_le n
  have hkpos : 1 ≤ k := inner_pos cT n h4
  have hnB : n + cT + 4 ≤ B := by omega
  have hnumB : num < 2 ^ B := lt_pow_mono hnum (by omega)
  have hdenB : den < 2 ^ B := lt_pow_mono hden (by omega)
  -- stage 0
  refine Hx.hs (Hs.then (pS0_spec cT c a hc hp (w_s0 n cT c.W hnB hB4 hWle hBig))
    (fun b0 ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11⟩ k0 hk0 => ?_))
  by_cases hkn : k < n
  swap
  · -- `k ≥ n`: the default
    have hf : PFail cT c a b0 := ⟨by rw [o1]; exact bnat_zero_of_not hkn, sp_none1 cT (header c) hkn, o7, o8, o9, o10,
      o11.weaken (by decide)⟩
    refine Hs.last (fail_G1234 cT c a b0 hf) (fun g hg k1 hk1 => ⟨pfail_out cT c a g hg, ?_⟩)
    unfold paramsCost; omega
  have hA0 : b0.env vADM = 1 := by rw [o1]; exact bnat_one_of hkn
  have b0N : b0.env vN = n := by simp (disch := decide) only [o11.ev]; exact hp.n
  have b0num : b0.env vNUM = num := by simp (disch := decide) only [o11.ev]; exact hp.num
  have b0den : b0.env vDEN = den := by simp (disch := decide) only [o11.ev]; exact hp.den
  obtain ⟨w1a, w1b, w1c, w1d, w1e⟩ := w_s1 (B := B) (Wd := C.Wd) n k (Jmax n) den num β rfl hkn (by omega) (by omega)
    hJ1 hdenB hnumB hB4 hBig
  have hTB := tbound_le (B := B) k (Jmax n) den β rfl (by omega) (by omega) hdenB hJ1
  -- stage 1
  refine Hs.then (guard_run pS1 b0 o10 hA0 _ _ (pS1_spec b0 o10 n k (Jmax n) num den β hβn rfl b0N o5 o4 b0num b0den
    hA0 w1a w1b w1c w1d w1e)) (fun b1 ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ k1 hk1 => ?_)
  have hc1 : k1 ≤ s1Bound B + 2 := by
    have : (TBound k (Jmax n) β + 3) * (5 * TBound k (Jmax n) β + 60) ≤ (3 * B + 5) * (5 * (3 * B + 2) + 60) :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold s1Bound; omega
  by_cases hQ1 : (leastT k (Jmax n) β).isSome = true ∧ DegreePass n k (outer n k) 0
  swap
  · have hnone : selectParams cT (header c) = none := by
      by_cases hs : (leastT k (Jmax n) β).isSome = true
      · obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hs
        exact sp_none3 cT (header c) hkn hβ0 T hT (fun h => hQ1 ⟨hs, h⟩)
      · exact sp_none2 cT (header c) hkn hβ0 (Option.not_isSome_iff_eq_none.1 hs)
    have hf : PFail cT c a b1 := ⟨by rw [q1]; exact bnat_zero_of_not hQ1, hnone, by rw [q4, o7], by rw [q5, o8],
      by rw [q6, o9], q7, FrS.trans (o11.weaken (by decide)) (q8.weaken (by decide))⟩
    refine Hs.last (fail_G234 cT c a b1 hf) (fun g hg k2 hk2 => ⟨pfail_out cT c a g hg, ?_⟩)
    unfold paramsCost; omega
  obtain ⟨hQ1a, hQ1b⟩ := hQ1
  have hTeq := q2 hQ1a
  obtain ⟨T, hTd⟩ : ∃ T, b1.env pT = T := ⟨_, rfl⟩
  rw [hTd] at hTeq
  have hTle : T ≤ 3 * B + 2 := le_trans (leastUpTo_spec _ _ _ hTeq).2.1 hTB
  have hT1 : 1 ≤ T := T_pos k (Jmax n) β T hJ1 hβ16 (leastUpTo_spec _ _ _ hTeq).1
  have hA1 : b1.env vADM = 1 := by rw [q1]; exact bnat_one_of ⟨hQ1a, hQ1b⟩
  set m := outer n k with hmdef
  have hmn : m ≤ n + 1 := by rw [hmdef]; unfold outer; omega
  have b1N : b1.env vN = n := by simp (disch := decide) only [q8.ev]; exact b0N
  have b1K : b1.env pK = k := by simp (disch := decide) only [q8.ev]; exact o5
  have b1B : b1.env vB0 = B0 n := by simp (disch := decide) only [q8.ev, o11.ev]; exact hp.b0
  have b1J : b1.env pJM = Jmax n := by simp (disch := decide) only [q8.ev]; exact o4
  set Dm := greatestDegree n k m with hDmdef
  have hDm : Dm ≤ m := Nat.findGreatest_le _
  obtain ⟨w2a, w2b, w2c, w2d, w2e, w2f, w2g⟩ := w_s2 (B := B) (Wd := C.Wd) n k m (Jmax n) Dm hkn (by omega) hmn hJn
    hDm hB4 hBig
  -- stage 2
  refine Hs.then (guard_run pS2 b1 q7 hA1 _ _ (pS2_spec b1 q7 n k m (Jmax n) b1N b1K q3 b1B b1J hA1 (by omega)
    w2a w2b w2c w2d w2e w2f w2g)) (fun b2 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ k2 hk2 => ?_)
  have hs2m := s2Cost_mono (show n ≤ B by omega) (show k ≤ B by omega) (show m ≤ B by omega)
  have hc2 : k2 ≤ s2Cost B B B + 2 := by omega
  set P := Nat.findGreatest (PrimeCandidate n k (Jmax n) Dm) (min n (Dm + 1)) with hPdef
  rw [r2] at r3 r4
  have hPn : P ≤ n := le_trans (Nat.findGreatest_le _) (min_le_left _ _)
  by_cases hQ2 : (liftExp k P).isSome = true
  swap
  · have hnone : selectParams cT (header c) = none :=
      sp_none4 cT (header c) hkn hβ0 T hTeq hQ1b (Option.not_isSome_iff_eq_none.1 hQ2)
    have hf : PFail cT c a b2 := ⟨by rw [r3]; exact bnat_zero_of_not hQ2, hnone, by rw [r5, q4, o7],
      by rw [r6, q5, o8], by rw [r7, q6, o9], r8,
      FrS.trans (o11.weaken (by decide)) (FrS.trans (q8.weaken (by decide)) (r9.weaken (by decide)))⟩
    refine Hs.last (fail_G34 cT c a b2 hf) (fun g hg k3 hk3 => ⟨pfail_out cT c a g hg, ?_⟩)
    unfold paramsCost; omega
  have heq := r4 hQ2
  obtain ⟨e, hed⟩ : ∃ e, b2.env pE = e := ⟨_, rfl⟩
  rw [hed] at heq
  have hA2 : b2.env vADM = 1 := by rw [r3]; exact bnat_one_of hQ2
  have b2N : b2.env vN = n := by simp (disch := decide) only [r9.ev]; exact b1N
  have b2K : b2.env pK = k := by simp (disch := decide) only [r9.ev]; exact b1K
  have b2T : b2.env pT = T := by simp (disch := decide) only [r9.ev]; exact hTd
  have b2Tag : b2.env vTAG = 1 ↔ decide (c.kind = .pair) = true := by
    rw [show b2.env vTAG = a.env vTAG by simp (disch := decide) only [r9.ev, q8.ev, o11.ev], hp.tag,
      kindTag_eq_one, decide_eq_true_iff]
  obtain ⟨w3a, w3b, w3c, w3d⟩ := w_s3 (B := B) (Wd := C.Wd) n k P T hkn (by omega) hPn hTle hB4 hBig
  -- stage 3
  refine Hs.then (guard_run pS3 b2 r8 hA2 _ _ (pS3_spec b2 r8 n k P T Dm (decide (c.kind = .pair)) b2N b2K r2 b2T r1
    b2Tag hA2 hPn w3a w3b w3c w3d)) (fun b3 ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ k3 hk3 => ?_)
  have hD' : ScalarWindow.window (dyadicPrimes P) ≤ B ^ 2 :=
    le_trans (window_le P) (by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega))
  have hs3m := s3Cost_mono (show n ≤ B by omega) (show P ≤ B by omega) hD'
  have hc3 : k3 ≤ s3Cost B B (B ^ 2) + 2 := by omega
  set G := 3 ≤ P ∧ (dyadicPrimes P).Nonempty ∧ 100 ≤ P ∧ 64 * T ≤ Nat.sqrt (2 * (P / 4) ^ 2) ∧ 2 * k ≤ Dm with hGdef
  by_cases hQ3 : G
  swap
  · have hnone : selectParams cT (header c) = none :=
      sp_none5 cT (header c) hkn hβ0 T hTeq hQ1b e heq hQ3
    have hf : PFail cT c a b3 := ⟨by rw [s8]; exact bnat_zero_of_not hQ3, hnone, by rw [s9, r5, q4, o7],
      by rw [s10, r6, q5, o8], by rw [s11, r7, q6, o9], s12,
      FrS.trans (o11.weaken (by decide)) (FrS.trans (q8.weaken (by decide)) (FrS.trans (r9.weaken (by decide))
        (s13.weaken (by decide))))⟩
    refine Hs.last (fail_G4 cT c a b3 hf) (fun g hg k4 hk4 => ⟨pfail_out cT c a g hg, ?_⟩)
    unfold paramsCost; omega
  obtain ⟨g1, g2, g3, g4, g5⟩ := hQ3
  have hA3 : b3.env vADM = 1 := by rw [s8]; exact bnat_one_of ⟨g1, g2, g3, g4, g5⟩
  set h := Nat.sqrt (2 * (P / 4) ^ 2) with hhdef
  set R0 := Nat.sqrt (n - k + 1) with hR0def
  set D' := ScalarWindow.window (dyadicPrimes P) with hD'def
  set Lw := windowInUse (decide (c.kind = .pair)) (pairSide D') D' with hLwdef
  have hhP : h ≤ P := sqrt_hE_le P
  have hR0n : R0 ≤ n + 1 := le_trans (Nat.sqrt_le_self _) (by omega)
  have hR01 : 1 ≤ R0 := by rw [hR0def]; exact Nat.sqrt_pos.2 (by omega)
  have hLwD : Lw ≤ D' := windowInUse_le _ _ _ (pairSide_le D' (window_pos P))
  obtain ⟨w4a, w4b, w4c, w4d, w4e, w4f, w4g⟩ := w_s4 (B := B) (Wd := C.Wd) n c.W k den num R0 h T Lw (Jmax n) hWle hkn
    (by omega) hdenB hnumB hR0n (by omega) hTle (le_trans hLwD hD') hJn hB4 hBig
  have b3W : b3.env pW = c.W := by simp (disch := decide) only [s13.ev, r9.ev, q8.ev]; exact o6
  have b3K : b3.env pK = k := by simp (disch := decide) only [s13.ev]; exact b2K
  have b3den : b3.env vDEN = den := by simp (disch := decide) only [s13.ev, r9.ev, q8.ev]; exact b0den
  have b3num : b3.env vNUM = num := by simp (disch := decide) only [s13.ev, r9.ev, q8.ev]; exact b0num
  have b3T : b3.env pT = T := by simp (disch := decide) only [s13.ev]; exact b2T
  have b3J : b3.env pJM = Jmax n := by simp (disch := decide) only [s13.ev, r9.ev]; exact b1J
  -- stage 4
  refine Hs.last (guard_run pS4 b3 s12 hA3 _ _ (pS4_spec b3 s12 n c.W k den num R0 h T Lw (8 * B) β hβq b3W b3K b3den
    b3num s7 s6 b3T b3J s4 hA3 (by omega) hkpos hden1 hnum1 hR01 hT1 g4 w4a w4b w4c w4d w4e w4f w4g))
    (fun b4 ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15, u16⟩ k4 hk4 => ?_)
  have hs4m := chainCost_mono (show Jmax n ≤ B by omega) (show h ≤ B by omega)
  have hc4 : k4 ≤ 30 * (8 * B) + 3300 + chainCost B B + 2 := by unfold s4Cost at hk4; omega
  have hcost : k0 + (k1 + (k2 + (k3 + k4 + 1) + 1) + 1) + 1 ≤ paramsCost B := by unfold paramsCost; omega
  set x1 := firstRatio (((c.W * k : ℕ) : ℚ) / (β * R0)) h T with hx1def
  by_cases hQ4 : (stopIndex x1 n).isSome = true
  swap
  · have hnone : selectParams cT (header c) = none :=
      sp_none6 cT (header c) hkn hβ0 T hTeq hQ1b e heq ⟨g1, g2, g3, g4, g5⟩ (Option.not_isSome_iff_eq_none.1 hQ4)
    exact ⟨pfail_out cT c a b4 ⟨by rw [u10]; exact bnat_zero_of_not hQ4, hnone, by rw [u12, s9, r5, q4, o7],
      by rw [u13, s10, r6, q5, o8], by rw [u14, s11, r7, q6, o9], u15,
      FrS.trans (o11.weaken (by decide)) (FrS.trans (q8.weaken (by decide)) (FrS.trans (r9.weaken (by decide))
        (FrS.trans (s13.weaken (by decide)) (u16.weaken (by decide)))))⟩, hcost⟩
  obtain ⟨hJl, hJd, hAd, hLd⟩ := u11 hQ4
  obtain ⟨p, hsp⟩ := sp_some cT (header c) hkn hβ0 T hTeq hQ1b e heq ⟨g1, g2, g3, g4, g5⟩ _ hJl
  have hS := selectParams_spec cT (header c) p hsp
  have pn : p.n = n := hS.n_eq
  have pk : p.k = k := hS.k_eq
  have pW' : p.W = c.W := hS.W_eq
  have pT' : p.T = T := by
    have h1 := (leastUpTo_spec _ _ _ hTeq)
    have h2 := hS.T_pass
    have h3 := hS.T_least
    rw [pk] at h2 h3
    rcases Nat.lt_trichotomy p.T T with hl | he | hl
    · exact absurd h2 (h1.2.2 _ hl)
    · exact he
    · exact absurd h1.1 (h3 T hl)
  have pm : p.m = m := by rw [hS.m_eq, pk]; rfl
  have pD : p.Dmax = Dm := by rw [hS.Dmax_eq, pk, pm]; rfl
  have pP' : p.P = P := by rw [hS.P_eq, pk, pD]; rfl
  have pe : p.e = e := by
    have := hS.e_eq; rw [pk, pP', heq] at this; exact (Option.some.inj this).symm
  have ppr : p.primes = dyadicPrimes P := by rw [hS.primes_eq, pP']
  have pwin : p.window = D' := by rw [hS.window_eq, ppr]
  have pL2 : p.L2 = pairSide D' := by rw [hS.L2_eq, pwin]
  have pLw : p.Lw = Lw := by rw [hS.Lw_eq, pL2, pwin]; rfl
  have phE : p.hE = P / 4 := by rw [hS.hE_eq, pP']
  have ph : p.h = h := by rw [hS.h_eq, phE]
  have pR : p.R0 = R0 := by rw [hS.R0_eq, pk]; rfl
  have pell : p.ell0 = ((c.W * k : ℕ) : ℚ) / (β * R0) := by rw [hS.ell0_eq, pk, pR]; rfl
  have px1 : firstRatio p.ell0 p.h p.T = x1 := by rw [pell, ph, pT']
  have pJ' : p.J = b4.env pCI + 1 := by
    have h1 := hS.J_eq
    rw [px1] at h1
    have h2 : p.J - 1 = b4.env pCI := by
      have : (some (p.J - 1) : Option ℕ) = some (b4.env pCI) := by rw [← h1, ← hJl]; rfl
      exact Option.some.inj this
    have := hS.J_pos
    omega
  have pA' : p.A = b4.env pA := by
    rw [hS.A_eq, hS.factors_eq, px1, hAd, pJ']; rfl
  -- frames from the stage boundaries
  have F4 : ∀ y : Fin VV, y.val < 200 → y ∉ s4T → b4.env y = b3.env y := fun y hy h => u16 y hy h
  refine ⟨?_, hcost⟩
  unfold ParamsOut
  refine ⟨Or.inr ⟨by rw [u10]; exact bnat_one_of hQ4, p, hsp, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, u5, u6, ?_⟩, ?_⟩, by rw [u12, s9, r5, q4, o7], by rw [u13, s10, r6, q5, o8],
    by rw [u14, s11, r7, q6, o9], u15, FrS.trans (o11.weaken (by decide)) (FrS.trans (q8.weaken (by decide))
      (FrS.trans (r9.weaken (by decide)) (FrS.trans (s13.weaken (by decide)) (u16.weaken (by decide)))))⟩
  · rw [pn]; simp (disch := decide) only [u16.ev, s13.ev, r9.ev]; exact b1N
  · rw [pW']; simp (disch := decide) only [u16.ev]; exact b3W
  · rw [pk]; simp (disch := decide) only [u16.ev]; exact b3K
  · rw [pT']; simp (disch := decide) only [u16.ev]; exact b3T
  · rw [pm]; simp (disch := decide) only [u16.ev, s13.ev, r9.ev]; exact q3
  · rw [pD]; simp (disch := decide) only [u16.ev, s13.ev]; exact r1
  · rw [pP']; simp (disch := decide) only [u16.ev, s13.ev]; exact r2
  · rw [pe]; simp (disch := decide) only [u16.ev, s13.ev]; exact hed
  · rw [ppr]; simp (disch := decide) only [u16.ev]; exact s1
  · rw [pwin]; simp (disch := decide) only [u16.ev]; exact s2
  · rw [pL2]; simp (disch := decide) only [u16.ev]; exact s3
  · rw [pLw]; simp (disch := decide) only [u16.ev]; exact s4
  · rw [phE]; simp (disch := decide) only [u16.ev]; exact s5
  · rw [ph]; simp (disch := decide) only [u16.ev]; exact s6
  · rw [pR]; simp (disch := decide) only [u16.ev]; exact s7
  · rw [pell]; exact u1
  · rw [pell]; exact u2
  · rw [hS.M1_eq, pell, ph, pT']; exact u3
  · rw [pJ']; exact hJd
  · exact pA'.symm
  · rw [hS.Lambda_eq, pLw, pA']; exact hLd
  · rw [pn]; simp (disch := decide) only [u16.ev]; exact b3J
  · rw [pn]; simp (disch := decide) only [u16.ev, s13.ev, r9.ev, q8.ev]; exact o2
  · rw [px1]; exact u4
  · rw [ph]; exact u7
  · rw [ph, pn]; exact u9

end NearCubicGates.Close.Dispatch
