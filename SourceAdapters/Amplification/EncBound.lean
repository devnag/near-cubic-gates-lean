import SourceAdapters.Amplification.EncTable

/-!
# The encoder table machine runs in `2^{O(n+k)}` steps (X9's budget, `app:sources`, "Full-range amplification interface")

Every cost of the encoder is bounded by a power of `Q = 2^(ℓ+1)` (`ℓ = arityParam R n k = O(n+k)`,
`Layout.arity_le`), the compiled budget is polynomial in `Q` and the width, and `stvEncoderTable : STVEncoderTable`
follows.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

/-! ## The costs as powers of `Q` -/

section Costs

variable {Q t h m n : ℕ} (hQ : 1 ≤ Q) (ht : t ≤ Q) (hpt : 2 ^ t ≤ Q) (hph : 2 ^ h ≤ Q) (hm : m ≤ Q)
  (hpn : 2 ^ n ≤ Q)

include hQ ht in
theorem lfsrCost_le : lfsrCost t ≤ 75 * Q := by unfold lfsrCost; omega

include hQ ht in
theorem fmulCost_le : fmulCost t ≤ 200 * Q ^ 2 := by
  unfold fmulCost
  have : t * (50 * t + 120 + 2) ≤ Q * (50 * Q + 122) := Nat.mul_le_mul ht (by omega)
  nlinarith

include hQ ht hpt in
theorem finvCost_le : finvCost t ≤ 300 * Q ^ 3 := by
  unfold finvCost
  have h1 := fmulCost_le hQ ht
  have : (2 ^ t - 2) * (fmulCost t + 10 + 2) ≤ Q * (200 * Q ^ 2 + 12) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

include hQ ht in
theorem lagBodyCost_le : lagBodyCost t ≤ 600 * Q ^ 2 := by
  unfold lagBodyCost; have := fmulCost_le hQ ht; nlinarith

include hQ ht hpt hph in
theorem lagCost_le : lagCost t h ≤ 2000 * Q ^ 3 := by
  unfold lagCost
  have h1 := lagBodyCost_le hQ ht
  have h2 := finvCost_le hQ ht hpt
  have h3 := fmulCost_le hQ ht
  have : 2 ^ h * (lagBodyCost t + 2) ≤ Q * (600 * Q ^ 2 + 2) := Nat.mul_le_mul hph (by omega)
  nlinarith

include hQ ht hpt hph hm in
theorem prodCost_le : prodCost t h m ≤ 3000 * Q ^ 4 := by
  unfold prodCost prodBodyCost
  have h1 := lagCost_le hQ ht hpt hph
  have h3 := fmulCost_le hQ ht
  have : m * (lagCost t h + fmulCost t + 40 + 2) ≤ Q * (2200 * Q ^ 3 + 42) := Nat.mul_le_mul hm (by nlinarith)
  nlinarith

include hQ ht hpt hph hm hpn in
theorem valCost_le : valCost t h m n ≤ 4000 * Q ^ 5 := by
  unfold valCost valAddCost
  have h1 := prodCost_le hQ ht hpt hph hm
  have : 2 ^ n * (prodCost t h m + 25 * t + 60 + 10 + 2) ≤ Q * (3000 * Q ^ 4 + 25 * Q + 72) :=
    Nat.mul_le_mul hpn (by omega)
  have : 2 ^ n * (3 + 2) ≤ Q * 5 := Nat.mul_le_mul hpn le_rfl
  have e : Q * (3000 * Q ^ 4 + 25 * Q + 72) = 3000 * Q ^ 5 + 25 * Q ^ 2 + 72 * Q := by ring
  have q1 : Q ≤ Q ^ 5 := Nat.le_self_pow (by norm_num) Q
  have q2 : Q ^ 2 ≤ Q ^ 5 := Nat.pow_le_pow_right hQ (by norm_num)
  have q0 : 1 ≤ Q ^ 5 := Nat.one_le_pow _ _ hQ
  omega

include hQ ht hpt hph hm hpn in
theorem mainCost_le (L : ℕ) (hpL : 2 ^ L ≤ Q) : mainCost t h m n L ≤ 5000 * Q ^ 6 := by
  unfold mainCost mainBodyCost hadCost
  have h1 := valCost_le hQ ht hpt hph hm hpn
  have : 2 ^ L * (valCost t h m n + (t * (30 + 2) + 20) + 20 + 2) ≤ Q * (4000 * Q ^ 5 + 32 * Q + 42) :=
    Nat.mul_le_mul hpL (by nlinarith)
  have e : Q * (4000 * Q ^ 5 + 32 * Q + 42) = 4000 * Q ^ 6 + 32 * Q ^ 2 + 42 * Q := by ring
  have q1 : Q ≤ Q ^ 6 := Nat.le_self_pow (by norm_num) Q
  have q2 : Q ^ 2 ≤ Q ^ 6 := Nat.pow_le_pow_right hQ (by norm_num)
  have q0 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ
  omega

include hQ ht hpt in
theorem searchCost_le : searchCost t ≤ 500 * Q ^ 3 := by
  unfold searchCost certCost
  have h1 := lfsrCost_le hQ ht
  have h2 : (2 ^ t - 1) * (lfsrCost t + 10 + 2) ≤ Q * (75 * Q + 12) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : 2 ^ t * ((2 ^ t - 1) * (lfsrCost t + 10 + 2) + 30 + 10 + 2) ≤ Q * (Q * (75 * Q + 12) + 42) :=
    Nat.mul_le_mul hpt (by omega)
  have e : Q * (Q * (75 * Q + 12) + 42) = 75 * Q ^ 3 + 12 * Q ^ 2 + 42 * Q := by ring
  have e2 : Q * (75 * Q + 12) = 75 * Q ^ 2 + 12 * Q := by ring
  have q1 : Q ≤ Q ^ 3 := Nat.le_self_pow (by norm_num) Q
  have q2 : Q ^ 2 ≤ Q ^ 3 := Nat.pow_le_pow_right hQ (by norm_num)
  have q0 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ
  omega

end Costs

/-- The quantity `Q = 2^(ℓ+1)` dominates every loop count of the encoder. -/
def encQ (R n k : ℕ) : ℕ := 2 ^ (arityParam R n k + 1)

theorem encQ_facts (R n k : ℕ) :
    1 ≤ encQ R n k ∧ tParam R n k ≤ encQ R n k ∧ 2 ^ tParam R n k ≤ encQ R n k ∧ 2 ^ hParam n k ≤ encQ R n k ∧
      mParam n k ≤ encQ R n k ∧ 2 ^ n ≤ encQ R n k ∧ 2 ^ arityParam R n k ≤ encQ R n k ∧
      arityParam R n k ≤ encQ R n k ∧ n + k ≤ encQ R n k := by
  obtain ⟨hnk, htL, hht, hmL, -⟩ := prm0_le R n k
  have hp : ∀ x ≤ arityParam R n k, 2 ^ x ≤ encQ R n k := fun x hx =>
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hl := Nat.lt_two_pow_self (n := arityParam R n k)
  have hl2 := hp (arityParam R n k) le_rfl
  refine ⟨Nat.one_le_two_pow, by omega, hp _ htL, hp _ (by omega), by omega, hp _ (by omega), hl2, by omega,
    by omega⟩

theorem encCost_le (R n k L0 : ℕ) (hL0 : L0 ≤ encQ R n k) :
    encCost R n k L0 ≤ 10000 * encQ R n k ^ 6 + 2 * R.size := by
  obtain ⟨hQ, ht, hpt, hph, hm, hpn, hpL, hL, hnk⟩ := encQ_facts R n k
  set Q := encQ R n k
  have h1 := mainCost_le hQ ht hpt hph hm hpn (arityParam R n k) hpL
  have h2 := searchCost_le hQ ht hpt
  have hsz : (arityParam R n k).size ≤ Q := le_trans (size_le_self _) hL
  have hsk : k.size ≤ Q := le_trans (size_le_self _) (by omega)
  have hsn : n.size ≤ Q := le_trans (size_le_self _) (by omega)
  unfold encCost restCost paramsCost
  have q2 : Q ≤ Q ^ 6 := Nat.le_self_pow (by norm_num) Q
  have q3 : Q ^ 3 ≤ Q ^ 6 := Nat.pow_le_pow_right hQ (by norm_num)
  nlinarith

open NearCubicGates.Close.Cells

/-- A generic bound for the compiled budget: with `W ≤ A·Q`, `L ≤ Q`, `|inp| ≤ 8Q`, `N ≤ B`. -/
theorem langBudget_le (R : ℕ) (inp : List Bool) (N Q : ℕ) (hQ : 1 ≤ Q)
    (hL : leadOnes inp ≤ Q) (hW : 2 ^ leadOnes inp ≤ Q) (hinp : inp.length ≤ 8 * Q)
    (hN : N ≤ 10000 * Q ^ 6 + 2 * R.size) :
    langBudget Code.Parsing.copyCallee (encSz R) NV 0 inp N ≤
      10 ^ 8 * ((TSK Code.Parsing.copyCallee + 3) * (49 + R.size) * Q) ^ 11 := by
  set T := TSK Code.Parsing.copyCallee with hTd
  set A := 49 + R.size with hAd
  set L := leadOnes inp with hLd
  set Z := (T + 3) * A * Q with hZ
  have hA : 1 ≤ A := by omega
  have hZ1 : 1 ≤ Z := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hZQ : Q ≤ Z := by
    have : 1 ≤ (T + 3) * A := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc Q = 1 * Q := (one_mul Q).symm
      _ ≤ (T + 3) * A * Q := Nat.mul_le_mul_right Q this
  have hZA : A ≤ Z := by
    calc A = 1 * A * 1 := by ring
      _ ≤ (T + 3) * A * Q := Nat.mul_le_mul (Nat.mul_le_mul_right A (by omega)) hQ
  have hZT : T + 3 ≤ Z := by
    calc T + 3 = (T + 3) * 1 * 1 := by ring
      _ ≤ (T + 3) * A * Q := Nat.mul_le_mul (Nat.mul_le_mul_left _ hA) hQ
  have hpow : ∀ i j, i ≤ j → Z ^ i ≤ Z ^ j := fun i j hij => Nat.pow_le_pow_right hZ1 hij
  -- the width
  have hWd : (encSz R).W L = 2 ^ L * A := by simp [encSz, Sz.W, A]
  have hLk : (encSz R).Lk L = 0 := by simp [encSz, Sz.Lk]
  have hBk : (encSz R).Bk L = 0 := by simp [encSz, Sz.Bk]
  have hW1 : 2 ^ L * A ≤ Z ^ 2 := by
    calc 2 ^ L * A ≤ Q * A := Nat.mul_le_mul_right A hW
      _ ≤ Z * Z := Nat.mul_le_mul hZQ hZA
      _ = Z ^ 2 := by ring
  have hNZ : N ≤ 10002 * Z ^ 6 := by
    have h1 : Q ^ 6 ≤ Z ^ 6 := Nat.pow_le_pow_left hZQ 6
    have h2 : R.size ≤ Z ^ 6 := le_trans (by omega) (le_trans hZA (Nat.le_self_pow (by norm_num) Z))
    omega
  have hsq : (2 ^ L * A + 1) ^ 2 ≤ 4 * Z ^ 4 := by
    have : 2 ^ L * A + 1 ≤ 2 * Z ^ 2 := by have := hpow 0 2 (by norm_num); simp at this; omega
    calc (2 ^ L * A + 1) ^ 2 ≤ (2 * Z ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 * Z ^ 4 := by ring
  have hbig : N * (500 * (2 ^ L * A + 1) ^ 2 + 100 * (T + 3)) ≤ 10002 * Z ^ 6 * (2100 * Z ^ 4) := by
    apply Nat.mul_le_mul hNZ
    have := hpow 1 4 (by norm_num); simp at this; omega
  have e1 : 10002 * Z ^ 6 * (2100 * Z ^ 4) = 21004200 * Z ^ 10 := by ring
  unfold langBudget
  simp only
  rw [hWd, hLk, hBk]
  unfold costA costB costC
  rw [hWd, hLk, hBk]
  simp only [encSz, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.one_mul, zero_add, Nat.zero_add, Nat.mul_one,
    ← hLd, ← hTd, ← hAd]
  have eNV : (NV + 2) * (50 * (2 ^ L * A) + 10 + 1) = 98 * (50 * (2 ^ L * A)) + 98 * 11 := by
    simp only [NV]; ring
  have hLZ : L ≤ Z := le_trans hL hZQ
  have hLW : L * (60 * (2 ^ L * A) + 11 + 8) ≤ Z * (60 * Z ^ 2 + 19) := Nat.mul_le_mul hLZ (by omega)
  have e2 : Z * (60 * Z ^ 2 + 19) = 60 * Z ^ 3 + 19 * Z := by ring
  have hL8 : L * 8 ≤ Z * 8 := Nat.mul_le_mul_right 8 hLZ
  have hz : ∀ i ≤ 11, Z ^ i ≤ Z ^ 11 := fun i hi => hpow i 11 hi
  have h10 := hz 10 (by norm_num)
  have h3 := hz 3 (by norm_num)
  have h2 := hz 2 (by norm_num)
  have h6 := hz 6 (by norm_num)
  have h1 := hz 1 (by norm_num)
  have h0 := hz 0 (by norm_num)
  simp only [pow_one, pow_zero] at h1 h0
  have hinpZ : inp.length ≤ 8 * Z := le_trans hinp (by omega)
  have hAZ : 4 * A ≤ 4 * Z := by omega
  have hWZ : 2 ^ L * A ≤ Z ^ 11 := le_trans hW1 h2
  omega

theorem encoderInput_length (r : Joins.EncoderRequest) :
    (Joins.encoderInput r).length = 2 * r.k.size + 1 + (2 * r.n.size + 1) + 2 ^ r.n := by
  simp [Joins.encoderInput, NearCubicWires.RepairSource.amplifierInput, NearCubicWires.RepairOrdinary.frame_length,
    NearCubicWires.ExecutableInterfaces.boolFunctionTable, Nat.size_eq_bits_len]
  omega

/-- The raw budget of the encoder table machine, as a power of `Q`. -/
theorem rawBudget_le (R : ℕ) (r : Joins.EncoderRequest) :
    (2 * (2 * prepCost (Joins.encoderInput r).length + 2) + 2) + 1 +
        (2 * langBudget Code.Parsing.copyCallee (encSz R) NV 0 (middleWord r) (encCost R r.n r.k (prefixLen r)) + 2) ≤
      (3 * 10 ^ 8 * ((TSK Code.Parsing.copyCallee + 3) * (49 + R.size)) ^ 11 + 10000) *
        encQ R r.n r.k ^ 11 := by
  obtain ⟨hQ, -, -, -, -, hpn, hpL, hL, hnk⟩ := encQ_facts R r.n r.k
  set Q := encQ R r.n r.k with hQd
  have hsk := size_le_self r.k
  have hsn := size_le_self r.n
  have hpre : prefixLen r ≤ Q := by unfold prefixLen; omega
  have hpre2 : 2 ^ prefixLen r ≤ Q := by
    have : prefixLen r ≤ arityParam R r.n r.k := by
      unfold prefixLen; have := (prm0_le R r.n r.k).1; omega
    exact le_trans (Nat.pow_le_pow_right (by norm_num) this) hpL
  have hlead : leadOnes (middleWord r) = prefixLen r :=
    NearCubicGates.Close.CounterMachine.CellTablesProg.leadOnes_rep _ _
  have hwlen := encoderInput_length r
  have hmid : (middleWord r).length ≤ 8 * Q := by
    simp only [middleWord, List.length_append, List.length_replicate, List.length_cons, hwlen]
    unfold prefixLen at hpre ⊢; omega
  have hlang := langBudget_le R (middleWord r) (encCost R r.n r.k (prefixLen r)) Q hQ (by rw [hlead]; exact hpre)
    (by rw [hlead]; exact hpre2) hmid (encCost_le R r.n r.k (prefixLen r) hpre)
  set K := (TSK Code.Parsing.copyCallee + 3) * (49 + R.size) with hK
  have e : ((TSK Code.Parsing.copyCallee + 3) * (49 + R.size) * Q) ^ 11 = K ^ 11 * Q ^ 11 := by rw [hK]; ring
  rw [e] at hlang
  have hQ11 : Q ≤ Q ^ 11 := Nat.le_self_pow (by norm_num) Q
  have hQ1 : 1 ≤ Q ^ 11 := Nat.one_le_pow _ _ hQ
  unfold prepCost
  rw [hwlen]
  have : (3 * 10 ^ 8 * K ^ 11 + 10000) * Q ^ 11 = 3 * (10 ^ 8 * (K ^ 11 * Q ^ 11)) + 10000 * Q ^ 11 := by ring
  rw [this]
  omega

/-- **X9 is satisfied**: the truth table of the rounded STV code is written by an ordinary machine within
`2^{e(n+k+1)}` steps. -/
theorem stvEncoderTable : Joins.STVEncoderTable := by
  intro R
  set c := 3 * 10 ^ 8 * ((TSK Code.Parsing.copyCallee + 3) * (49 + R.size)) ^ 11 + 10000 with hc
  refine ⟨c + 11 * (45 + R.size), ⟨WordFunction.widen (encTableWF R) (fun r => ?_)⟩⟩
  refine le_trans (rawBudget_le R r) ?_
  have hc2 : c ≤ 2 ^ c := Nat.lt_two_pow_self.le
  have hcn : 2 ^ c ≤ 2 ^ (c * (r.n + r.k + 1)) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
  have hl := arity_le R r.n r.k
  have hQ : encQ R r.n r.k ^ 11 ≤ 2 ^ (11 * (45 + R.size) * (r.n + r.k + 1)) := by
    unfold encQ
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    unfold arityParam at hl ⊢
    nlinarith
  calc c * encQ R r.n r.k ^ 11 ≤ 2 ^ (c * (r.n + r.k + 1)) * 2 ^ (11 * (45 + R.size) * (r.n + r.k + 1)) :=
        Nat.mul_le_mul (le_trans hc2 hcn) hQ
    _ = 2 ^ ((c + 11 * (45 + R.size)) * (r.n + r.k + 1)) := by rw [← pow_add]; congr 1; ring

end NearCubicGates.Adapters.Amplification.Enc
