import Proof.Gates.Target
import Proof.Gates.ScalarWindow
import Proof.Gates.TomographyDirections
import Proof.Gates.RationalRateChain
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Proof.Gates.PublicSamplingRates

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open NearCubicGates

/-! ## Bounded least search -/

/-- The least `t ≤ B` with `Q t`, or `none` if there is none. -/
def leastUpTo (Q : ℕ → Prop) [DecidablePred Q] (B : ℕ) : Option ℕ :=
  if Q (Nat.find (⟨B, Or.inr rfl⟩ : ∃ t, Q t ∨ t = B)) then
    some (Nat.find (⟨B, Or.inr rfl⟩ : ∃ t, Q t ∨ t = B))
  else none

theorem leastUpTo_spec (Q : ℕ → Prop) [DecidablePred Q] (B t : ℕ) (h : leastUpTo Q B = some t) :
    Q t ∧ t ≤ B ∧ ∀ s, s < t → ¬ Q s := by
  unfold leastUpTo at h
  split_ifs at h with hq
  cases h
  refine ⟨hq, ?_, ?_⟩
  · exact Nat.find_min' _ (Or.inr rfl)
  · intro s hs hQ
    exact Nat.find_min _ hs (Or.inl hQ)

theorem leastUpTo_isSome (Q : ℕ → Prop) [DecidablePred Q] (B t : ℕ) (ht : t ≤ B) (hQ : Q t) :
    ∃ s, leastUpTo Q B = some s := by
  unfold leastUpTo
  have hle : Nat.find (⟨B, Or.inr rfl⟩ : ∃ t, Q t ∨ t = B) ≤ t := Nat.find_min' _ (Or.inl hQ)
  have hspec := Nat.find_spec (⟨B, Or.inr rfl⟩ : ∃ t, Q t ∨ t = B)
  have hq : Q (Nat.find (⟨B, Or.inr rfl⟩ : ∃ t, Q t ∨ t = B)) := by
    rcases hspec with h | h
    · exact h
    · have : t = B := le_antisymm ht (h ▸ hle)
      rw [h, ← this]; exact hQ
  exact ⟨_, if_pos hq⟩

theorem leastUpTo_eq (Q : ℕ → Prop) [DecidablePred Q] (B t : ℕ) (ht : t ≤ B) (hQ : Q t)
    (hmin : ∀ s, s < t → ¬ Q s) : leastUpTo Q B = some t := by
  obtain ⟨s, hs⟩ := leastUpTo_isSome Q B t ht hQ
  obtain ⟨hQs, _, hsmin⟩ := leastUpTo_spec Q B s hs
  have h1 : ¬ s < t := fun h => hmin s h hQs
  have h2 : ¬ t < s := fun h => hsmin t h hQ
  rw [hs, show s = t by omega]

/-! ## The header and the fixed scales -/

/-- The public data the parameters depend on (the rules of `sec:finite` use only these). -/
structure Header where
  n : ℕ
  W : ℕ
  pair : Bool
  beta : ℚ

/-- `J_max = μ_n + 1` (`sec:finite`). -/
def Jmax (n : ℕ) : ℕ := Target.mu n + 1

/-- `k = (2J_max + c_T + μ_n) λ_n` (`sec:finite`). -/
def inner (cT n : ℕ) : ℕ := (2 * Jmax n + cT + Target.mu n) * Target.lambda n

/-- `B₀ = 4n⌈lg(n+1)⌉` (`sec:algorithm`). -/
def B0 (n : ℕ) : ℕ := 4 * n * Nat.clog 2 (n + 1)

/-- `G₀ = 2n⁴` (`sec:algorithm`). -/
def G0 (n : ℕ) : ℕ := 2 * n ^ 4

/-- `m`: `n − k` rounded up to even (`sec:finite`, rule 1). -/
def outer (n k : ℕ) : ℕ := (n - k) + (n - k) % 2

/-- `B_b = B₀ + ⌈lg(n+1)⌉ + ⌈lg(m+1)⌉ + 2` (`sec:finite`, rule 1). -/
def Bb (n m : ℕ) : ℕ := B0 n + Nat.clog 2 (n + 1) + Nat.clog 2 (m + 1) + 2

/-- `m_T = 1 + B_b m ⌈m/2⌉` (`sec:finite`, rule 1). -/
def mT (n m : ℕ) : ℕ := 1 + Bb n m * m * ((m + 1) / 2)

/-- `U = 1 + 2G₀m_T` (`sec:finite`, rule 1). -/
def Ubase (n m : ℕ) : ℕ := 1 + 2 * G0 n * mT n m

/-! ## Rule 1: the concentration parameter `T` -/

/-- `2^t β ≥ 4 J_max 2^k` (`sec:finite`, rule 1). -/
def TPass (k J : ℕ) (β : ℚ) (t : ℕ) : Prop := (((4 * J * 2 ^ k : ℕ)) : ℚ) ≤ 2 ^ t * β

instance (k J : ℕ) (β : ℚ) : DecidablePred (TPass k J β) := fun t => by
  unfold TPass; infer_instance

/-- A search bound for `T`: at `t = k + ⌊lg(4 J den β)⌋ + 1` the test holds when `β > 0`. -/
def TBound (k J : ℕ) (β : ℚ) : ℕ := k + Nat.log 2 (4 * J * β.den) + 1

/-- The least `T` (rule 1). -/
def leastT (k J : ℕ) (β : ℚ) : Option ℕ := leastUpTo (TPass k J β) (TBound k J β)

/-! ## Rule 2: the degree budget, eq:degree-budget with the constant 100 -/

/-- `2^{100(k+2)} U^{100 D} ≤ 2^m` (eq:degree-budget). -/
def DegreePass (n k m D : ℕ) : Prop := 2 ^ (100 * (k + 2)) * Ubase n m ^ (100 * D) ≤ 2 ^ m

instance (n k m : ℕ) : DecidablePred (DegreePass n k m) := fun D => by
  unfold DegreePass; infer_instance

/-- `D_max`: the largest passing degree; passing degrees are at most `m` since `U ≥ 2`. -/
def greatestDegree (n k m : ℕ) : ℕ := Nat.findGreatest (DegreePass n k m) m

/-! ## Rule 3: the prime scale, eq:prime-budget -/

/-- `P^e ≥ 2^{k+1+e}` with `e ≥ 1` (`sec:finite`, rule 3). -/
def LiftPass (k P e : ℕ) : Prop := 1 ≤ e ∧ 2 ^ (k + 1 + e) ≤ P ^ e

instance (k P : ℕ) : DecidablePred (LiftPass k P) := fun e => by
  unfold LiftPass; infer_instance

/-- `e_P`, the least positive lift exponent; for `P ≥ 3` it is at most `2(k+1)`. -/
def liftExp (k P : ℕ) : Option ℕ := leastUpTo (LiftPass k P) (2 * (k + 1))

/-- `3 ≤ P ≤ min(n, D_max+1)` satisfying eq:prime-budget (`sec:finite`, rule 3). -/
def PrimeCandidate (n k J Dmax P : ℕ) : Prop :=
  3 ≤ P ∧ P ≤ min n (Dmax + 1) ∧
    ∃ e, liftExp k P = some e ∧ (2 * e - 1) * (2 * J + 2) * (P - 1) ≤ Dmax

instance (n k J Dmax : ℕ) : DecidablePred (PrimeCandidate n k J Dmax) := fun P => by
  unfold PrimeCandidate
  exact instDecidableAnd (dp := inferInstance) (dq := instDecidableAnd (dp := inferInstance)
    (dq := decidable_of_iff (∃ e, liftExp k P = some e ∧ (2 * e - 1) * (2 * J + 2) * (P - 1) ≤ Dmax)
      Iff.rfl))

/-- The prime set `𝒫`: all primes in `(P/2, P]` (`sec:finite`, rule 3). -/
def dyadicPrimes (P : ℕ) : Finset ℕ :=
  (Finset.range (P + 1)).filter (fun p => Nat.Prime p ∧ P < 2 * p)

/-- `L ≥ 2` is admissible if `S(⌊(D'−1)/(L−1)⌋) ≥ L` (lem:window-size). -/
def Admissible (D' L : ℕ) : Prop :=
  2 ≤ L ∧ L ≤ TomographyDirections.degreeSum ((D' - 1) / (L - 1))

instance (D' : ℕ) : DecidablePred (Admissible D') := fun L => by
  unfold Admissible; infer_instance

/-- `L₂`: the largest admissible `L`, or one if none exists (lem:window-size). Admissible `L` are at most `D'`. -/
def pairSide (D' : ℕ) : ℕ :=
  if Nat.findGreatest (Admissible D') D' = 0 then 1 else Nat.findGreatest (Admissible D') D'

/-- `L_w = L₂` for a two-circuit call and `D'` for the other kinds (`sec:finite`, rule 3). -/
def windowInUse (pair : Bool) (L2 D' : ℕ) : ℕ := if pair then L2 else D'

/-! ## Rule 4: the chain of lem:chain -/

/-- `ℓ̄ = max(ℓ₀, h²/(256T))`. -/
def ellBar (ell0 : ℚ) (h T : ℕ) : ℚ := max ell0 ((h : ℚ) ^ 2 / (256 * T))

/-- `π* = h²/(8Tℓ̄)`. -/
def piStar (ell0 : ℚ) (h T : ℕ) : ℚ := (h : ℚ) ^ 2 / (8 * T * ellBar ell0 h T)

/-- `M₁ = ⌈4ℓ̄/h⌉`. -/
def firstDen (ell0 : ℚ) (h T : ℕ) : ℕ := ⌈4 * ellBar ell0 h T / h⌉₊

/-- `x₁ = π₁/π*` with `π₁ = 1/M₁`. -/
def firstRatio (ell0 : ℚ) (h T : ℕ) : ℚ := (1 / (firstDen ell0 h T : ℚ)) / piStar ell0 h T

/-- The 0-based stopping index `J − 1`: the least `i ≤ J_max − 1` with `x_{i+1} ≥ 2^{−8}`. -/
def stopIndex (x1 : ℚ) (n : ℕ) : Option ℕ :=
  leastUpTo (fun i => (1 : ℚ) / 256 ≤ RationalRateChain.ratio x1 i) (Jmax n - 1)

/-- The rate ratios `a_1, …, a_{J−1}` (0-based list). -/
def chainFactors (x1 : ℚ) (Jlean : ℕ) : List ℕ :=
  (List.range Jlean).map fun i => RationalRateChain.factorRat (RationalRateChain.ratio x1 i)

/-! ## The parameter record -/

structure Params where
  n : ℕ
  pair : Bool
  W : ℕ
  beta : ℚ
  k : ℕ
  T : ℕ
  m : ℕ
  Dmax : ℕ
  P : ℕ
  e : ℕ
  primes : Finset ℕ
  window : ℕ
  L2 : ℕ
  Lw : ℕ
  hE : ℕ
  h : ℕ
  R0 : ℕ
  ell0 : ℚ
  M1 : ℕ
  J : ℕ
  factors : List ℕ
  A : ℕ
  Lambda : ℕ

/-- The computed record, with the default (`none`) at every failed guard of `sec:finite`. -/
def selectParams (cT : ℕ) (hd : Header) : Option Params :=
  let n := hd.n
  let k := inner cT n
  if k < n ∧ 0 < hd.beta then
    match leastT k (Jmax n) hd.beta with
    | none => none
    | some T =>
      let m := outer n k
      if DegreePass n k m 0 then
        let Dmax := greatestDegree n k m
        let P := Nat.findGreatest (PrimeCandidate n k (Jmax n) Dmax) (min n (Dmax + 1))
        match liftExp k P with
        | none => none
        | some e =>
          let primes := dyadicPrimes P
          let D' := ScalarWindow.window primes
          let L2 := pairSide D'
          let Lw := windowInUse hd.pair L2 D'
          let hE := P / 4
          let h := Nat.sqrt (2 * hE ^ 2)
          let R0 := Nat.sqrt (n - k + 1)
          let ell0 : ℚ := ((hd.W * k : ℕ) : ℚ) / (hd.beta * R0)
          if 3 ≤ P ∧ primes.Nonempty ∧ 100 ≤ P ∧ 64 * T ≤ h ∧ 2 * k ≤ Dmax then
            let x1 := firstRatio ell0 h T
            match stopIndex x1 n with
            | none => none
            | some Jlean =>
              let factors := chainFactors x1 Jlean
              let A := factors.prod
              some ⟨n, hd.pair, hd.W, hd.beta, k, T, m, Dmax, P, e, primes, D', L2, Lw, hE, h, R0, ell0,
                firstDen ell0 h T, Jlean + 1, factors, A, (Lw - 1) * A / 2 + 1⟩
          else none
      else none
  else none

end NearCubicGates.Close.Counter

namespace NearCubicGates.Close.Counter

open NearCubicGates

/-- Every rule of `sec:finite`, as satisfied by a selected record. -/
structure Spec (cT : ℕ) (hd : Header) (p : Params) : Prop where
  n_eq : p.n = hd.n
  pair_eq : p.pair = hd.pair
  W_eq : p.W = hd.W
  beta_eq : p.beta = hd.beta
  k_eq : p.k = inner cT hd.n
  k_lt : p.k < hd.n
  beta_pos : 0 < hd.beta
  T_pass : TPass p.k (Jmax hd.n) hd.beta p.T
  T_least : ∀ t, t < p.T → ¬ TPass p.k (Jmax hd.n) hd.beta t
  m_eq : p.m = outer hd.n p.k
  zero_pass : DegreePass hd.n p.k p.m 0
  Dmax_eq : p.Dmax = greatestDegree hd.n p.k p.m
  P_eq : p.P = Nat.findGreatest (PrimeCandidate hd.n p.k (Jmax hd.n) p.Dmax) (min hd.n (p.Dmax + 1))
  e_eq : liftExp p.k p.P = some p.e
  primes_eq : p.primes = dyadicPrimes p.P
  window_eq : p.window = ScalarWindow.window p.primes
  L2_eq : p.L2 = pairSide p.window
  Lw_eq : p.Lw = windowInUse hd.pair p.L2 p.window
  hE_eq : p.hE = p.P / 4
  h_eq : p.h = Nat.sqrt (2 * p.hE ^ 2)
  R0_eq : p.R0 = Nat.sqrt (hd.n - p.k + 1)
  ell0_eq : p.ell0 = ((hd.W * p.k : ℕ) : ℚ) / (hd.beta * p.R0)
  P_three : 3 ≤ p.P
  primes_nonempty : p.primes.Nonempty
  P_large : 100 ≤ p.P
  height : 64 * p.T ≤ p.h
  moment_degree : 2 * p.k ≤ p.Dmax
  M1_eq : p.M1 = firstDen p.ell0 p.h p.T
  J_eq : stopIndex (firstRatio p.ell0 p.h p.T) hd.n = some (p.J - 1)
  J_pos : 1 ≤ p.J
  factors_eq : p.factors = chainFactors (firstRatio p.ell0 p.h p.T) (p.J - 1)
  A_eq : p.A = p.factors.prod
  Lambda_eq : p.Lambda = (p.Lw - 1) * p.A / 2 + 1

theorem selectParams_spec (cT : ℕ) (hd : Header) (p : Params) (hs : selectParams cT hd = some p) :
    Spec cT hd p := by
  unfold selectParams at hs
  simp only at hs
  split at hs
  swap
  · cases hs
  rename_i h1
  split at hs
  · cases hs
  rename_i T hT
  split at hs
  swap
  · cases hs
  rename_i h2
  split at hs
  · cases hs
  rename_i e he
  split at hs
  swap
  · cases hs
  rename_i h3
  split at hs
  · cases hs
  rename_i Jl hJ
  cases hs
  exact {
    n_eq := rfl
    pair_eq := rfl
    W_eq := rfl
    beta_eq := rfl
    k_eq := rfl
    k_lt := h1.1
    beta_pos := h1.2
    T_pass := (leastUpTo_spec _ _ _ hT).1
    T_least := (leastUpTo_spec _ _ _ hT).2.2
    m_eq := rfl
    zero_pass := h2
    Dmax_eq := rfl
    P_eq := rfl
    e_eq := he
    primes_eq := rfl
    window_eq := rfl
    L2_eq := rfl
    Lw_eq := rfl
    hE_eq := rfl
    h_eq := rfl
    R0_eq := rfl
    ell0_eq := rfl
    P_three := h3.1
    primes_nonempty := h3.2.1
    P_large := h3.2.2.1
    height := h3.2.2.2.1
    moment_degree := h3.2.2.2.2
    M1_eq := rfl
    J_eq := (by simpa using hJ)
    J_pos := Nat.le_add_left 1 _
    factors_eq := (by simp)
    A_eq := rfl
    Lambda_eq := rfl }

end NearCubicGates.Close.Counter

/-!
# Consequences of the parameter rules used by soundness and by the time count

From `Spec` alone (`sec:finite`): the prime set consists of primes in `(P/2, P]`
(`primes_prime`, `primes_le`, `primes_gt`), each exceeds the digit window `2h_E − 1` (proof of `prop:sound`: "fewer than any
prime in 𝒫"), lifts beyond `2^k` (`prime_pow_gt`; `sec:algorithm`: "every `p ∈ 𝒫` has `p^e > 2^k`"),
the chain ratios satisfy `a_j ≥ 4` so
`A > 0` (lem:chain (i)), the windows are at least one, and the window in use is one of the three injective cases
(lem:one-window, lem:two-window, singleton).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open NearCubicGates

variable {cT : ℕ} {hd : Header} {p : Params}

theorem mem_dyadicPrimes (P q : ℕ) : q ∈ dyadicPrimes P ↔ q ≤ P ∧ Nat.Prime q ∧ P < 2 * q := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨by omega, b, c⟩
  · rintro ⟨a, b, c⟩; exact ⟨by omega, b, c⟩

theorem primes_prime (hs : Spec cT hd p) : ∀ q ∈ p.primes, Nat.Prime q := by
  intro q hq
  rw [hs.primes_eq, mem_dyadicPrimes] at hq
  exact hq.2.1

theorem primes_le (hs : Spec cT hd p) : ∀ q ∈ p.primes, q ≤ p.P := by
  intro q hq
  rw [hs.primes_eq, mem_dyadicPrimes] at hq
  exact hq.1

theorem primes_gt (hs : Spec cT hd p) : ∀ q ∈ p.primes, p.P < 2 * q := by
  intro q hq
  rw [hs.primes_eq, mem_dyadicPrimes] at hq
  exact hq.2.2

/-- The digit window `2h_E − 1` is below every prime of the set (proof of `prop:sound`). -/
theorem digit_width (hs : Spec cT hd p) : ∀ q ∈ p.primes, 2 * (p.hE : ℤ) - 1 ≤ q := by
  intro q hq
  have h1 := primes_gt hs q hq
  have h2 : p.hE = p.P / 4 := hs.hE_eq
  have h3 : 4 * (p.P / 4) ≤ p.P := Nat.mul_div_le p.P 4
  omega

/-- `p^e > 2^k` for every prime of the set (`sec:algorithm`, "Witnesses and the tables to be computed"). -/
theorem prime_pow_gt (hs : Spec cT hd p) : ∀ q ∈ p.primes, 2 ^ p.k < q ^ p.e := by
  intro q hq
  have hlift := (leastUpTo_spec _ _ _ hs.e_eq).1
  obtain ⟨he, hpow⟩ := hlift
  have h2q : p.P < 2 * q := primes_gt hs q hq
  have hP : p.P ^ p.e < (2 * q) ^ p.e := Nat.pow_lt_pow_left h2q (by omega)
  rw [mul_pow] at hP
  have hsplit : 2 ^ (p.k + 1 + p.e) = 2 ^ (p.k + 1) * 2 ^ p.e := by rw [← pow_add]
  have hlt : 2 ^ (p.k + 1) * 2 ^ p.e < q ^ p.e * 2 ^ p.e := by
    calc 2 ^ (p.k + 1) * 2 ^ p.e = 2 ^ (p.k + 1 + p.e) := hsplit.symm
      _ ≤ p.P ^ p.e := hpow
      _ < 2 ^ p.e * q ^ p.e := hP
      _ = q ^ p.e * 2 ^ p.e := by ring
  have hlt' : 2 ^ (p.k + 1) < q ^ p.e := Nat.lt_of_mul_lt_mul_right hlt
  have : 2 ^ p.k < 2 ^ (p.k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-! ## The chain -/

theorem ratio_nonpos (x : ℚ) (hx : x ≤ 0) : ∀ j, RationalRateChain.ratio x j ≤ 0 := by
  intro j
  induction j with
  | zero => exact hx
  | succ j ih =>
    simp only [RationalRateChain.ratio]
    split_ifs
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) ih
    · exact ih

theorem ratio_pos (x : ℚ) (hx : 0 < x) (j : ℕ) : 0 < RationalRateChain.ratio x j := by
  have h := NestedRateChain.ratio_positive (x : ℝ) (by exact_mod_cast hx) j
  rw [← RationalRateChain.ratio_cast x hx j] at h
  exact_mod_cast h

theorem factorRat_ge_four (x : ℚ) (hx : 0 < x) (hsmall : x < 1 / 256) : 4 ≤ RationalRateChain.factorRat x := by
  rw [RationalRateChain.factorRat_eq x hx hsmall]
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have hsr : (x : ℝ) < 1 / 256 := by
    have hc : (x : ℝ) < ((1 / 256 : ℚ) : ℝ) := Rat.cast_lt.mpr hsmall
    norm_num at hc
    exact hc
  exact (NestedRateChain.step_bounds (x : ℝ) hxr hsr).1

/-- The first ratio is positive at a selected record. -/
theorem firstRatio_pos (hs : Spec cT hd p) : 0 < firstRatio p.ell0 p.h p.T := by
  by_contra hneg
  have hstop := (leastUpTo_spec _ _ _ hs.J_eq).1
  have h := ratio_nonpos _ (not_lt.mp hneg) (p.J - 1)
  have : (1 : ℚ) / 256 ≤ 0 := hstop.trans h
  norm_num at this

/-- The active ratios lie in `(0, 2^{-8})`. -/
theorem active_ratio (hs : Spec cT hd p) (i : ℕ) (hi : i < p.J - 1) :
    0 < RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i ∧
      RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i < 1 / 256 := by
  refine ⟨ratio_pos _ (firstRatio_pos hs) i, ?_⟩
  have hmin := (leastUpTo_spec _ _ _ hs.J_eq).2.2 i hi
  exact not_le.mp hmin

theorem factors_length (hs : Spec cT hd p) : p.factors.length = p.J - 1 := by
  rw [hs.factors_eq]
  simp [chainFactors]

/-- `a_j ≥ 4` (lem:chain (i)). -/
theorem factor_ge_four (hs : Spec cT hd p) (t : ℕ) (ht : t < p.J - 1) : 4 ≤ p.factors.getD t 0 := by
  have hlen := factors_length hs
  rw [List.getD_eq_getElem _ _ (by omega)]
  have hf : p.factors[t]'(by omega) =
      RationalRateChain.factorRat (RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) t) := by
    simp only [hs.factors_eq, chainFactors, List.getElem_map, List.getElem_range]
  rw [hf]
  obtain ⟨h1, h2⟩ := active_ratio hs t ht
  exact factorRat_ge_four _ h1 h2

theorem A_pos (hs : Spec cT hd p) : 0 < p.A := by
  rw [hs.A_eq]
  apply List.prod_pos
  intro a ha
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
  have hlen := factors_length hs
  have h := factor_ge_four hs t (by omega)
  rw [List.getD_eq_getElem _ _ ht] at h
  omega

/-! ## Windows -/

theorem window_pos (primes : Finset ℕ) : 1 ≤ ScalarWindow.window primes := by
  unfold ScalarWindow.window; omega

theorem pairSide_pos (D' : ℕ) : 1 ≤ pairSide D' := by
  unfold pairSide; split_ifs with h <;> omega

theorem Lw_pos (hs : Spec cT hd p) : 1 ≤ p.Lw := by
  rw [hs.Lw_eq]
  unfold windowInUse
  split_ifs
  · rw [hs.L2_eq]; exact pairSide_pos _
  · rw [hs.window_eq]; exact window_pos _

/-- `L₂` is either one or an admissible side (lem:window-size). -/
theorem pairSide_cases (D' : ℕ) :
    pairSide D' ≤ 1 ∨ (2 ≤ pairSide D' ∧
      pairSide D' ≤ TomographyDirections.degreeSum ((D' - 1) / (pairSide D' - 1))) := by
  unfold pairSide
  split_ifs with h
  · left; rfl
  · right
    exact Nat.findGreatest_of_ne_zero rfl h

/-- The window in use is one of the three injective cases (`d` = number of scores). -/
theorem window_cases (hs : Spec cT hd p) (d : ℕ) (hd1 : hd.pair = false → d = 1) (hd2 : hd.pair = true → d = 2) :
    (d = 1 ∧ p.Lw ≤ ScalarWindow.window p.primes) ∨
      (d = 2 ∧ 2 ≤ p.Lw ∧ p.Lw ≤ TomographyDirections.degreeSum ((ScalarWindow.window p.primes - 1) / (p.Lw - 1))) ∨
      p.Lw ≤ 1 := by
  rw [hs.Lw_eq]
  cases hpair : hd.pair
  · left
    refine ⟨hd1 hpair, ?_⟩
    simp [windowInUse, hs.window_eq]
  · have hc := pairSide_cases p.window
    simp only [windowInUse, if_true, hs.L2_eq]
    rcases hc with h | h
    · right; right; exact h
    · right; left
      rw [← hs.window_eq]
      exact ⟨hd2 hpair, h.1, h.2⟩

theorem Lambda_cast (hs : Spec cT hd p) : (p.Lambda : ℤ) = ((p.Lw : ℤ) - 1) * p.A / 2 + 1 := by
  rw [hs.Lambda_eq]
  have h1 := Lw_pos hs
  push_cast [Nat.cast_sub h1]
  rfl

theorem k_pos_of (hs : Spec cT hd p) (hn : 2 ≤ hd.n) : 1 ≤ p.k := by
  rw [hs.k_eq]
  unfold inner Jmax
  have hl : 1 ≤ Target.lambda hd.n := Nat.clog_pos (by norm_num) (by omega)
  nlinarith

/-! ## One statement per rule of `sec:finite` -/

/-- "The search for `L₂` is finite: admissible `L`'s are at most `D'`" (`sec:finite`, rule 3). -/
theorem admissible_le (D' L : ℕ) (hD : 1 ≤ D') (h : Admissible D' L) : L ≤ D' := by
  by_contra hlt
  have hq : (D' - 1) / (L - 1) = 0 := Nat.div_eq_of_lt (by omega)
  have h2 := h.2
  rw [hq] at h2
  simp [TomographyDirections.degreeSum] at h2
  omega

/-- `L₂` is the largest admissible side, or one if none exists (lem:window-size). -/
theorem pairSide_spec (D' : ℕ) (hD : 1 ≤ D') :
    (pairSide D' = 1 ∧ ∀ L, ¬ Admissible D' L) ∨
      (Admissible D' (pairSide D') ∧ ∀ L, Admissible D' L → L ≤ pairSide D') := by
  unfold pairSide
  split_ifs with h
  · left
    refine ⟨rfl, fun L hL => ?_⟩
    have hle := Nat.le_findGreatest (admissible_le D' L hD hL) hL
    have := hL.1
    omega
  · right
    exact ⟨Nat.findGreatest_of_ne_zero rfl h,
      fun L hL => Nat.le_findGreatest (admissible_le D' L hD hL) hL⟩

/-- Rule 1 of `sec:finite`: `T` is the least nonnegative integer with `2^T β ≥ 4J_max 2^k`, and `m` is `n − k`
rounded up to even. -/
theorem spec_rule1 (hs : Spec cT hd p) :
    TPass p.k (Jmax hd.n) hd.beta p.T ∧ (∀ t, t < p.T → ¬ TPass p.k (Jmax hd.n) hd.beta t) ∧
      p.m = outer hd.n p.k ∧ p.k = inner cT hd.n ∧ p.k < hd.n :=
  ⟨hs.T_pass, hs.T_least, hs.m_eq, hs.k_eq, hs.k_lt⟩

/-- Rule 2 (eq:degree-budget, constant 100): `D_max` is the largest passing degree, and degree zero
passes. -/
theorem spec_rule2 (hs : Spec cT hd p) (hn : 0 < hd.n) :
    DegreePass hd.n p.k p.m p.Dmax ∧ ∀ D, DegreePass hd.n p.k p.m D → D ≤ p.Dmax := by
  have hz := hs.zero_pass
  rw [hs.Dmax_eq]
  refine ⟨Nat.findGreatest_spec (Nat.zero_le _) hz, fun D hD => Nat.le_findGreatest ?_ hD⟩
  -- passing degrees are at most `m` since `U ≥ 2`
  have hU : 2 ≤ Ubase hd.n p.m := by
    unfold Ubase G0
    have h1 : 1 ≤ 2 * (2 * hd.n ^ 4) * mT hd.n p.m := Nat.one_le_iff_ne_zero.mpr (by unfold mT; positivity)
    omega
  have hpow : 2 ^ (100 * D) ≤ 2 ^ p.m := by
    calc 2 ^ (100 * D) ≤ Ubase hd.n p.m ^ (100 * D) := Nat.pow_le_pow_left hU _
      _ ≤ 2 ^ (100 * (p.k + 2)) * Ubase hd.n p.m ^ (100 * D) := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ 2 ^ p.m := hD
  have := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
  omega

/-- Rule 3 (eq:prime-budget; `sec:finite`, rule 3): `P` is the largest candidate, `e = e_P`, `𝒫` the primes in
`(P/2, P]` (nonempty), `D'`, `L₂`, `L_w`. -/
theorem spec_rule3 (hs : Spec cT hd p) :
    PrimeCandidate hd.n p.k (Jmax hd.n) p.Dmax p.P ∧
      (∀ P', PrimeCandidate hd.n p.k (Jmax hd.n) p.Dmax P' → P' ≤ p.P) ∧
      liftExp p.k p.P = some p.e ∧ p.primes = dyadicPrimes p.P ∧ p.primes.Nonempty ∧
      p.window = ScalarWindow.window p.primes ∧ p.L2 = pairSide p.window ∧
      p.Lw = windowInUse hd.pair p.L2 p.window := by
  have h3 := hs.P_three
  refine ⟨?_, ?_, hs.e_eq, hs.primes_eq, hs.primes_nonempty, hs.window_eq, hs.L2_eq, hs.Lw_eq⟩
  · rw [hs.P_eq] at h3 ⊢
    exact Nat.findGreatest_of_ne_zero rfl (by omega)
  · intro P' hP'
    rw [hs.P_eq]
    exact Nat.le_findGreatest (hP'.2.1.trans (le_refl _)) hP'

/-- Rule 4 of `sec:finite`: `h_E, h, R₀, ℓ₀`, the guards, the chain with `J ≤ J_max`, and `Λ`. -/
theorem spec_rule4 (hs : Spec cT hd p) :
    p.hE = p.P / 4 ∧ p.h = Nat.sqrt (2 * p.hE ^ 2) ∧ p.R0 = Nat.sqrt (hd.n - p.k + 1) ∧
      p.ell0 = ((hd.W * p.k : ℕ) : ℚ) / (hd.beta * p.R0) ∧ 100 ≤ p.P ∧ 64 * p.T ≤ p.h ∧ 2 * p.k ≤ p.Dmax ∧
      p.M1 = firstDen p.ell0 p.h p.T ∧ 1 ≤ p.J ∧ p.J ≤ Jmax hd.n ∧
      (1 : ℚ) / 256 ≤ RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) (p.J - 1) ∧
      (∀ i, i < p.J - 1 → RationalRateChain.ratio (firstRatio p.ell0 p.h p.T) i < 1 / 256) ∧
      p.factors = chainFactors (firstRatio p.ell0 p.h p.T) (p.J - 1) ∧ p.A = p.factors.prod ∧
      p.Lambda = (p.Lw - 1) * p.A / 2 + 1 := by
  have hst := leastUpTo_spec _ _ _ hs.J_eq
  refine ⟨hs.hE_eq, hs.h_eq, hs.R0_eq, hs.ell0_eq, hs.P_large, hs.height, hs.moment_degree, hs.M1_eq, hs.J_pos,
    ?_, hst.1, fun i hi => (active_ratio hs i hi).2, hs.factors_eq, hs.A_eq, hs.Lambda_eq⟩
  have := hs.J_pos
  have := hst.2.1
  unfold Jmax at *
  omega

end NearCubicGates.Close.Counter
