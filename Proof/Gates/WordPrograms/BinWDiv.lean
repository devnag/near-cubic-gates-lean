import Proof.Gates.WordPrograms.BinW

set_option autoImplicit false

namespace NearCubicGates.Close.WordPrograms.BinW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Round (binary_mod wloopE)

/-! ## The arithmetic of the rounds -/

/-- The top `k` bits of `a`. -/
def dp (W a k : ℕ) : ℕ := a / 2 ^ (W - k)

/-- The remaining bits of `a`, shifted up by `k`. -/
def dx (W a k : ℕ) : ℕ := a % 2 ^ (W - k) * 2 ^ k

/-- Bit `W − k − 1` of `a`. -/
def dbit (W a k : ℕ) : ℕ := a / 2 ^ (W - k - 1) % 2

theorem dp_succ (W a k : ℕ) (hk : k < W) : dp W a (k + 1) = 2 * dp W a k + dbit W a k := by
  obtain ⟨j, rfl⟩ : ∃ j, W = j + 1 + k := ⟨W - k - 1, by omega⟩
  unfold dp dbit
  rw [show j + 1 + k - k - 1 = j by omega, show j + 1 + k - k = j + 1 by omega, show j + 1 + k - (k + 1) = j by omega]
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (a / 2 ^ j) 2
  omega

theorem dx_succ (W a k : ℕ) (hk : k < W) : 2 * dx W a k = dx W a (k + 1) + 2 ^ W * dbit W a k := by
  obtain ⟨j, rfl⟩ : ∃ j, W = j + 1 + k := ⟨W - k - 1, by omega⟩
  unfold dx dbit
  rw [show j + 1 + k - k - 1 = j by omega, show j + 1 + k - k = j + 1 by omega, show j + 1 + k - (k + 1) = j by omega]
  rw [Nat.mod_pow_succ]
  simp only [pow_add, pow_succ]
  ring

theorem dx_lt (W a k : ℕ) (hk : k ≤ W) : dx W a k < 2 ^ W := by
  unfold dx
  have h1 : a % 2 ^ (W - k) < 2 ^ (W - k) := Nat.mod_lt _ (by positivity)
  have h2 : 2 ^ (W - k) * 2 ^ k = 2 ^ W := by rw [← pow_add]; congr 1; omega
  calc a % 2 ^ (W - k) * 2 ^ k < 2 ^ (W - k) * 2 ^ k := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    _ = 2 ^ W := h2

theorem dbit_le (W a k : ℕ) : dbit W a k ≤ 1 := by
  unfold dbit; have := Nat.mod_lt (a / 2 ^ (W - k - 1)) (show 0 < 2 by norm_num); omega

/-- The bit shifted out of `X` is `dbit`. -/
theorem carry_dx (W a k : ℕ) (hk : k < W) : (decide (2 ^ W ≤ 2 * dx W a k + (false).toNat)).toNat = dbit W a k := by
  have e := dx_succ W a k hk
  have hl := dx_lt W a (k + 1) (by omega)
  have hb := dbit_le W a k
  simp only [Bool.toNat_false, Nat.add_zero]
  rcases Nat.lt_or_ge (dbit W a k) 1 with h | h
  · have h0 : dbit W a k = 0 := by omega
    rw [h0] at e ⊢; simp only [Nat.mul_zero, Nat.add_zero] at e; simp; omega
  · have h1 : dbit W a k = 1 := by omega
    rw [h1] at e ⊢; simp only [Nat.mul_one] at e; simp; omega

theorem shift_dx (W a k : ℕ) (hk : k < W) : binary W (2 * dx W a k + (false).toNat) = binary W (dx W a (k + 1)) := by
  rw [Bool.toNat_false, Nat.add_zero, ← binary_mod W (2 * dx W a k), dx_succ W a k hk, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (dx_lt W a (k + 1) (by omega))]

theorem dp_zero (W a : ℕ) (ha : a < 2 ^ W) : dp W a 0 = 0 := by
  unfold dp; rw [Nat.sub_zero]; exact Nat.div_eq_of_lt ha

theorem dp_W (W a : ℕ) : dp W a W = a := by unfold dp; simp

theorem dx_zero (W a : ℕ) (ha : a < 2 ^ W) : dx W a 0 = a := by
  unfold dx; rw [Nat.sub_zero, Nat.mod_eq_of_lt ha]; simp

theorem dx_W (W a : ℕ) : dx W a W = 0 := by unfold dx; simp [Nat.mod_one]

theorem dp_le (W a k : ℕ) : dp W a k ≤ a := Nat.div_le_self _ _

/-- One round of long division on the partial value `p` (`p' = 2p + d`). -/
theorem div_round (b p d : ℕ) (hb : 0 < b) (hd : d ≤ 1) :
    (2 * (p % b) + d < b → (2 * p + d) / b = 2 * (p / b) ∧ (2 * p + d) % b = 2 * (p % b) + d) ∧
    (b ≤ 2 * (p % b) + d → (2 * p + d) / b = 2 * (p / b) + 1 ∧ (2 * p + d) % b = 2 * (p % b) + d - b) := by
  have hp := Nat.div_add_mod p b
  have hr := Nat.mod_lt p hb
  constructor
  · intro h
    have e : 2 * p + d = (2 * (p % b) + d) + b * (2 * (p / b)) := by
      calc 2 * p + d = 2 * (b * (p / b) + p % b) + d := by rw [hp]
        _ = _ := by ring
    rw [e, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    omega
  · intro h
    have e : 2 * p + d = (2 * (p % b) + d - b) + b * (2 * (p / b) + 1) := by
      have : 2 * p + d = 2 * (b * (p / b) + p % b) + d := by rw [hp]
      rw [this, Nat.mul_add b, Nat.mul_one]
      have : b * (2 * (p / b)) = 2 * (b * (p / b)) := by ring
      omega
    have hlt : 2 * (p % b) + d - b < b := by omega
    rw [e, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hlt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    omega

/-! ## One round -/

variable {ns nr : ℕ}

/-- One round: `X := 2x` (bit out to `F`), `M := 2m + F`, then compare with `b`: subtract and shift `1` into `Q`, or
shift `0` into `Q`. -/
def divBody (B Q M X : Fin (ns + 1)) (F R : Fin nr) : WM ns nr :=
  .seq (shlcW X B F R) (.seq (shlcW M B F R) (.seq (ltB M B F R)
    (.ifr F (.seq (.dec F) (shlcW Q B F R)) (.seq (subB M B F R) (.seq (.inc F) (shlcW Q B F R))))))

/-- The state with the three words `Q`, `M`, `X` set. -/
def bst (Q M X : Fin (ns + 1)) (W : ℕ) (σ : WState ns nr) (q m x : ℕ) : WState ns nr :=
  ((σ.sets Q (frame (binary W q))).sets M (frame (binary W m))).sets X (frame (binary W x))

section Round
variable (W : ℕ) {B Q M X : Fin (ns + 1)}

theorem bst_setv (σ : WState ns nr) (q m x : ℕ) (r : Fin nr) (v : ℕ) :
    (bst Q M X W σ q m x).setv r v = bst Q M X W (σ.setv r v) q m x := rfl

@[simp] theorem bst_val (σ : WState ns nr) (q m x : ℕ) : (bst Q M X W σ q m x).val = σ.val := rfl

theorem bst_sets_X (σ : WState ns nr) (q m x x' : ℕ) :
    (bst Q M X W σ q m x).sets X (frame (binary W x')) = bst Q M X W σ q m x' := by
  unfold bst; rw [sets_sets]

theorem bst_sets_M (hQM : Q ≠ M) (hMX : M ≠ X) (σ : WState ns nr) (q m x m' : ℕ) :
    (bst Q M X W σ q m x).sets M (frame (binary W m')) = bst Q M X W σ q m' x := by
  unfold bst
  refine WState.eq ?_ ?_ ?_ ?_
  · rfl
  · funext i; simp only [WState.sets_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl
  · rfl

theorem bst_sets_Q (hQM : Q ≠ M) (hQX : Q ≠ X) (σ : WState ns nr) (q m x q' : ℕ) :
    (bst Q M X W σ q m x).sets Q (frame (binary W q')) = bst Q M X W σ q' m x := by
  unfold bst
  refine WState.eq ?_ ?_ ?_ ?_
  · rfl
  · funext i; simp only [WState.sets_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl
  · rfl

theorem bst_numQ (hQM : Q ≠ M) (hQX : Q ≠ X) (σ : WState ns nr) (q m x : ℕ) (h : σ.sh Q = 0) :
    NumOn (bst Q M X W σ q m x) Q W q :=
  ⟨by simp [bst, Function.update_of_ne hQM, Function.update_of_ne hQX], by simpa [bst] using h⟩

theorem bst_numM (hMX : M ≠ X) (σ : WState ns nr) (q m x : ℕ) (h : σ.sh M = 0) : NumOn (bst Q M X W σ q m x) M W m :=
  ⟨by simp [bst, Function.update_of_ne hMX], by simpa [bst] using h⟩

theorem bst_numX (σ : WState ns nr) (q m x : ℕ) (h : σ.sh X = 0) : NumOn (bst Q M X W σ q m x) X W x :=
  ⟨by simp [bst], by simpa [bst] using h⟩

theorem bst_numB (hBQ : B ≠ Q) (hBM : B ≠ M) (hBX : B ≠ X) (σ : WState ns nr) (q m x b : ℕ) (h : NumOn σ B W b) :
    NumOn (bst Q M X W σ q m x) B W b :=
  ⟨by simp [bst, Function.update_of_ne hBQ, Function.update_of_ne hBM, Function.update_of_ne hBX, h.1],
    by simpa [bst] using h.2⟩

/-- The round's cost. -/
def bodyCost (W : ℕ) : ℕ := 205 * W + 30

/-- **One round**: from words `q, m, x` (with `m < b`), with `c` the top bit of `x` and `m' = 2m + c`: `X := 2x mod
2^W`, and `(Q, M) := (2q, m')` if `m' < b`, else `(2q + 1, m' − b)`. -/
theorem divBody_spec (cap : ℕ) {F R : Fin nr} (hBQ : B ≠ Q) (hBM : B ≠ M) (hBX : B ≠ X) (hQM : Q ≠ M) (hQX : Q ≠ X)
    (hMX : M ≠ X) (hFR : F ≠ R) (σ : WState ns nr) (b q m x : ℕ) (hB : NumOn σ B W b) (hQ0 : σ.sh Q = 0)
    (hM0 : σ.sh M = 0) (hX0 : σ.sh X = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hb : 0 < b) (h2b : 2 * b ≤ 2 ^ W)
    (hm : m < b) (hx : x < 2 ^ W) (c : ℕ) (hc : (decide (2 ^ W ≤ 2 * x + (false).toNat)).toNat = c)
    (hq0 : 2 * m + c < b → 2 * q < 2 ^ W) (hq1 : b ≤ 2 * m + c → 2 * q + 1 < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (divBody B Q M X F R) (bst Q M X W σ q m x)
      (bst Q M X W σ (if 2 * m + c < b then 2 * q else 2 * q + 1) (if 2 * m + c < b then 2 * m + c else 2 * m + c - b)
        ((2 * x) % 2 ^ W)) (bodyCost W) := by
  have hbW : b < 2 ^ W := by omega
  have hcle : c ≤ 1 := by rw [← hc]; exact Bool.toNat_le _
  set x' := (2 * x) % 2 ^ W with hx'
  set m' := 2 * m + c with hm'
  have hF' : ∀ v, (σ.setv F v).val R = 0 := fun v => by simp [Ne.symm hFR, hR]
  -- `X := 2x`, `F := c`
  have h1 := shlcW_spec cap W hBX.symm hFR (bst Q M X W σ q m x) x b false
    (bst_numX W σ q m x hX0) (bst_numB W hBQ hBM hBX σ q m x b hB) (by simp [hF]) (by simp [hR]) hx hcap
  have e1 : ((bst Q M X W σ q m x).sets X (frame (binary W (2 * x + (false).toNat)))).setv F
      (decide (2 ^ W ≤ 2 * x + (false).toNat)).toNat = bst Q M X W (σ.setv F c) q m x' := by
    rw [hc, Bool.toNat_false, Nat.add_zero, ← binary_mod W (2 * x), bst_sets_X W, bst_setv]
  rw [e1] at h1
  -- `M := 2m + c`, `F := 0`
  set cb : Bool := decide (c = 1) with hcb
  have hcbn : cb.toNat = c := by rw [hcb]; rcases (show c = 0 ∨ c = 1 by omega) with h | h <;> simp [h]
  have h2 := shlcW_spec cap W hBM.symm hFR (bst Q M X W (σ.setv F c) q m x') m b cb
    (bst_numM W hMX _ q m x' (by simpa using hM0)) (bst_numB W hBQ hBM hBX _ q m x' b (numOn_setv hB F c))
    (by rw [hcbn]; simp) (by simp [hF']) (by omega) hcap
  have e2 : ((bst Q M X W (σ.setv F c) q m x').sets M (frame (binary W (2 * m + cb.toNat)))).setv F
      (decide (2 ^ W ≤ 2 * m + cb.toNat)).toNat = bst Q M X W σ q m' x' := by
    have hno : decide (2 ^ W ≤ 2 * m + cb.toNat) = false := by rw [hcbn]; simp; omega
    rw [hno, hcbn, bst_sets_M W hQM hMX, bst_setv, wsetv_setv, Bool.toNat_false, setv_same (by simp [hF])]
  rw [e2] at h2
  set s2 := bst Q M X W σ q m' x' with hs2
  have hM2 : NumOn s2 M W m' := bst_numM W hMX σ q m' x' hM0
  have hB2 : NumOn s2 B W b := bst_numB W hBQ hBM hBX σ q m' x' b hB
  -- `F := [m' < b]`
  have h3 := ltB_spec cap W hBM.symm hFR s2 m' b hM2 hB2 (by simp [hs2, hF]) (by simp [hs2, hR]) (by omega) hbW hcap
  by_cases hlt : m' < b
  · rw [if_pos hlt, if_pos hlt]
    have e3 : s2.setv F (decide (m' < b)).toNat = s2.setv F 1 := by simp [hlt]
    rw [e3] at h3
    have h4 := WExec.dec (cap := cap) F (s2.setv F 1) (by simp; omega)
    have e4 : (s2.setv F 1).setv F ((s2.setv F 1).val F - 1) = s2 := by
      rw [wsetv_val_self, wsetv_setv]; exact setv_same (by simp [hs2, hF])
    rw [e4] at h4
    have h5 := shlcW_spec cap W hBQ.symm hFR s2 q b false (bst_numQ W hQM hQX σ q m' x' hQ0) hB2
      (by simp [hs2, hF]) (by simp [hs2, hR]) (by omega) hcap
    have e5 : (s2.sets Q (frame (binary W (2 * q + (false).toNat)))).setv F
        (decide (2 ^ W ≤ 2 * q + (false).toNat)).toNat = bst Q M X W σ (2 * q) m' x' := by
      have hno5 : decide (2 ^ W ≤ 2 * q + (false).toNat) = false := by simp; exact hq0 hlt
      rw [hno5, Bool.toNat_false, Nat.add_zero, hs2, bst_sets_Q W hQM hQX, bst_setv, setv_same (by simp [hF])]
    rw [e5] at h5
    have hbr := WExec.ifrT (r := F) (Q := .seq (subB M B F R) (.seq (.inc F) (shlcW Q B F R))) (by simp) (WExec.seq h4 h5)
    exact WExec.mono (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 hbr))) (by unfold bodyCost; omega)
  · rw [if_neg hlt, if_neg hlt]
    have hge : b ≤ m' := by omega
    have e3 : s2.setv F (decide (m' < b)).toNat = s2 := by
      rw [show decide (m' < b) = false by simp [hlt], Bool.toNat_false]; exact setv_same (by simp [hs2, hF])
    rw [e3] at h3
    have h4 := subB_spec cap W hBM.symm hFR s2 m' b hM2 hB2 (by simp [hs2, hF]) (by simp [hs2, hR]) hge (by omega)
      hcap
    rw [hs2, bst_sets_M W hQM hMX] at h4
    have h5 := WExec.inc (cap := cap) F (bst Q M X W σ q (m' - b) x') (by simp [hF]; omega)
    rw [bst_setv, bst_val, hF] at h5
    have h6 := shlcW_spec cap W hBQ.symm hFR (bst Q M X W (σ.setv F (0 + 1)) q (m' - b) x') q b true
      (bst_numQ W hQM hQX _ q _ x' (by simpa using hQ0)) (bst_numB W hBQ hBM hBX _ q _ x' b (numOn_setv hB F _))
      (by simp) (by simp [hF']) (by omega) hcap
    have e6 : ((bst Q M X W (σ.setv F (0 + 1)) q (m' - b) x').sets Q (frame (binary W (2 * q + (true).toNat)))).setv F
        (decide (2 ^ W ≤ 2 * q + (true).toNat)).toNat = bst Q M X W σ (2 * q + 1) (m' - b) x' := by
      have hno6 : decide (2 ^ W ≤ 2 * q + (true).toNat) = false := by simp; exact hq1 hge
      rw [hno6, Bool.toNat_false, Bool.toNat_true, bst_sets_Q W hQM hQX, bst_setv, wsetv_setv, setv_same (by simp [hF])]
    rw [e6] at h6
    have hbr := WExec.ifrF (r := F) (P := .seq (.dec F) (shlcW Q B F R)) (by simp [hF]) (WExec.seq h4 (WExec.seq h5 h6))
    exact WExec.mono (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 hbr))) (by unfold bodyCost; omega)

end Round

/-! ## The division -/

/-- **`Q := ⌊a / b⌋`, `M := a mod b`** (`X` scratch word, ends at `0`; registers `F R K T` scratch). -/
def divmodW (A B Q M X : Fin (ns + 1)) (F R K T : Fin nr) : WM ns nr :=
  .seq (zeroB Q B F R) (.seq (zeroB M B F R) (.seq (copyB X A F R) (.seq (widthW B K T)
    (.whr K (.seq (.dec K) (divBody B Q M X F R))))))

/-- The division's cost. -/
def divCost (W : ℕ) : ℕ := 205 * W * W + 177 * W + 17

theorem divCost_le (W : ℕ) : divCost W ≤ 400 * (W + 1) ^ 2 := by unfold divCost; nlinarith

theorem divmodW_spec (cap W : ℕ) {A B Q M X : Fin (ns + 1)} {F R K T : Fin nr} (hAQ : A ≠ Q)
    (hAM : A ≠ M) (hAX : A ≠ X) (hBQ : B ≠ Q) (hBM : B ≠ M) (hBX : B ≠ X) (hQM : Q ≠ M) (hQX : Q ≠ X) (hMX : M ≠ X)
    (hFR : F ≠ R) (hFK : F ≠ K) (hRK : R ≠ K) (hKT : K ≠ T) (σ : WState ns nr)
    (a b q0 m0 x0 : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hQ : NumOn σ Q W q0) (hM : NumOn σ M W m0)
    (hX : NumOn σ X W x0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (ha : a < 2 ^ W) (hb : 0 < b) (h2b : 2 * b ≤ 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (divmodW A B Q M X F R K T) σ (bst Q M X W σ (a / b) (a % b) 0) (divCost W) := by
  -- the set-up
  have z1 := zeroB_spec cap W hBQ.symm hFR σ q0 b hQ hB hF hR hcap
  set σ1 := σ.sets Q (frame (binary W 0)) with hσ1
  have z2 := zeroB_spec cap W hBM.symm hFR σ1 m0 b (numOn_sets_ne hM hQM.symm _) (numOn_sets_ne hB hBQ _)
    (by simp [hσ1, hF]) (by simp [hσ1, hR]) hcap
  set σ2 := σ1.sets M (frame (binary W 0)) with hσ2
  have c3 := copyB_spec cap W hAX.symm hFR σ2 x0 a (numOn_sets_ne (numOn_sets_ne hX hQX.symm _) hMX.symm _)
    (numOn_sets_ne (numOn_sets_ne hA hAQ _) hAM _) (by simp [hσ2, hσ1, hF]) (by simp [hσ2, hσ1, hR]) hcap
  have hσ3 : σ2.sets X (frame (binary W a)) = bst Q M X W σ 0 0 a := rfl
  rw [hσ3] at c3
  have w4 := widthW_spec cap hKT W b (bst Q M X W σ 0 0 a) (bst_numB W hBQ hBM hBX σ 0 0 a b hB) (by simp [hK])
    (by simp [hT]) (by omega)
  -- the loop
  let Inv : ℕ → WState ns nr → Prop := fun k τ =>
    τ = bst Q M X W (σ.setv K (W - k)) (dp W a k / b) (dp W a k % b) (dx W a k)
  have hstep : ∀ k < W, ∀ τ, Inv k τ → τ.val K = W - k →
      ∃ τ', WExec cap (divBody B Q M X F R) (τ.setv K (W - k - 1)) τ' (bodyCost W) ∧ Inv (k + 1) τ' ∧
        τ'.val K = W - k - 1 := by
    intro k hk τ hτ _
    rw [hτ, bst_setv, wsetv_setv]
    set p := dp W a k with hp
    have hd := dbit_le W a k
    have hpa : dp W a (k + 1) ≤ a := dp_le W a (k + 1)
    have hps := dp_succ W a k hk
    have hr := div_round b p (dbit W a k) hb hd
    have hpb := Nat.div_mul_le_self p b
    have hb1 : p / b ≤ p := Nat.div_le_self p b
    have body := divBody_spec W cap hBQ hBM hBX hQM hQX hMX hFR (σ.setv K (W - k - 1)) b (p / b) (p % b) (dx W a k)
      (numOn_setv hB K _) (by simpa using hQ.2) (by simpa using hM.2) (by simpa using hX.2) (by simp [hFK, hF])
      (by simp [hRK, hR]) hb h2b (Nat.mod_lt p hb) (dx_lt W a k (by omega)) (dbit W a k) (carry_dx W a k hk)
      (fun h => by have := (hr.1 h).1; have := Nat.div_le_self (2 * p + dbit W a k) b; omega)
      (fun h => by have := (hr.2 h).1; have := Nat.div_le_self (2 * p + dbit W a k) b; omega) hcap
    refine ⟨_, body, ?_, by simp⟩
    show _ = bst Q M X W (σ.setv K (W - (k + 1))) (dp W a (k + 1) / b) (dp W a (k + 1) % b) (dx W a (k + 1))
    have ex : (2 * dx W a k) % 2 ^ W = dx W a (k + 1) := by
      rw [dx_succ W a k hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (dx_lt W a (k + 1) (by omega))]
    rw [ex, hps, show W - (k + 1) = W - k - 1 by omega]
    by_cases hlt : 2 * (p % b) + dbit W a k < b
    · rw [if_pos hlt, if_pos hlt, (hr.1 hlt).1, (hr.1 hlt).2]
    · rw [if_neg hlt, if_neg hlt, (hr.2 (by omega)).1, (hr.2 (by omega)).2]
  have hI0 : Inv 0 ((bst Q M X W σ 0 0 a).setv K W) := by
    show _ = bst Q M X W (σ.setv K (W - 0)) (dp W a 0 / b) (dp W a 0 % b) (dx W a 0)
    rw [dp_zero W a ha, dx_zero W a ha, Nat.zero_div, Nat.zero_mod, Nat.sub_zero, bst_setv]
  obtain ⟨τ, hl, hIW, _⟩ := wloopE cap K (divBody B Q M X F R) (bodyCost W) W Inv (by omega) hstep _ hI0 (by simp)
  have hIW' : τ = bst Q M X W σ (a / b) (a % b) 0 := by
    rw [hIW, Nat.sub_self, dp_W, dx_W, ← bst_setv, setv_same (by simp [hK])]
  rw [hIW'] at hl
  exact WExec.mono (WExec.seq z1 (WExec.seq z2 (WExec.seq c3 (WExec.seq w4 hl)))) (by unfold divCost bodyCost; nlinarith)

/-- **`Q := ⌊a / b⌋`, `M := a mod b`** as a `WMX` instruction. -/
def divmod (A B Q M X : Fin (ns + 1)) (F R K T : Fin nr) : WMX ns nr := .wm (divmodW A B Q M X F R K T)

theorem divmod_spec (cap W : ℕ) {A B Q M X : Fin (ns + 1)} {F R K T : Fin nr} (hAQ : A ≠ Q)
    (hAM : A ≠ M) (hAX : A ≠ X) (hBQ : B ≠ Q) (hBM : B ≠ M) (hBX : B ≠ X) (hQM : Q ≠ M) (hQX : Q ≠ X) (hMX : M ≠ X)
    (hFR : F ≠ R) (hFK : F ≠ K) (hRK : R ≠ K) (hKT : K ≠ T) (σ : WState ns nr)
    (a b q0 m0 x0 : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hQ : NumOn σ Q W q0) (hM : NumOn σ M W m0)
    (hX : NumOn σ X W x0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (ha : a < 2 ^ W) (hb : 0 < b) (h2b : 2 * b ≤ 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (divmod A B Q M X F R K T) σ
      (((σ.sets Q (frame (binary W (a / b)))).sets M (frame (binary W (a % b)))).sets X (frame (binary W 0)))
      (divCost W) :=
  WXExec.wm (divmodW_spec cap W hAQ hAM hAX hBQ hBM hBX hQM hQX hMX hFR hFK hRK hKT σ a b q0 m0 x0 hA hB hQ
    hM hX hF hR hK hT ha hb h2b hcap)

/-! Programs are opaque to consumers: use the spec theorems. -/
attribute [irreducible] divBody divmodW divmod

end NearCubicGates.Close.WordPrograms.BinW
