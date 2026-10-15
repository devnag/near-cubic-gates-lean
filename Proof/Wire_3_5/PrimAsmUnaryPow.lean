import Proof.Wire_3_5.PrimAsmUnaryArith
import Proof.Wire_3_5.LedgerGrowth

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.UnaryPow
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith

variable {ns nr : ℕ} (cap : ℕ)

/-- The kit's unit cost: each primitive runs within `sq cap` steps when its values are at most `cap`. -/
def sq (c : ℕ) : ℕ := 200 * (c + 2) * (c + 2)

theorem sq_ge (c : ℕ) : 800 ≤ sq c := by unfold sq; nlinarith

theorem lin_le_sq (c : ℕ) : 40 * c + 40 ≤ sq c := by unfold sq; nlinarith

/-- A `whr` loop along a state sequence: `F ≠ 0` before each of the `m` rounds, `F = 0` after them. -/
theorem flagLoop (F : Fin nr) (body : WM ns nr) (c m : ℕ) (S : ℕ → WState ns nr)
    (hF : ∀ k < m, (S k).val F ≠ 0) (hstop : (S m).val F = 0)
    (hbody : ∀ k < m, WExec cap body (S k) (S (k + 1)) c) :
    WExec cap (.whr F body) (S 0) (S m) (m * (c + 2) + 1) := by
  have key : ∀ r j, j + r = m → WExec cap (.whr F body) (S j) (S m) (r * (c + 2) + 1) := by
    intro r
    induction r with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj; subst hj
      exact WExec.mono (WExec.whrF hstop) (by omega)
    | succ r ih =>
      intro j hj
      have h1 := hbody j (by omega)
      have h2 := ih (j + 1) (by omega)
      exact WExec.mono (WExec.whrT (hF j (by omega)) h1 h2) (by nlinarith)
  exact key m 0 (by omega)

theorem mulAddW_sq (R : Fin 5 ↪ Fin nr) (σ : WState ns nr) (ht : σ.val (R 3) = 0) (hw : σ.val (R 4) = 0)
    (hb : σ.val (R 1) ≤ cap) (hcap : σ.val (R 2) + σ.val (R 0) * σ.val (R 1) ≤ cap) (ha : σ.val (R 0) ≤ cap) :
    WExec cap (mulAddW R) σ (σ.setv (R 2) (σ.val (R 2) + σ.val (R 0) * σ.val (R 1))) (sq cap) := by
  refine WExec.mono (mulAddW_spec cap R σ ht hw hb hcap ha) ?_
  have h1 : σ.val (R 1) * (18 * σ.val (R 0) + 8) ≤ cap * (18 * cap + 8) := Nat.mul_le_mul hb (by omega)
  unfold sq; nlinarith

/-! ## Powers with a constant exponent -/

def eP : Fin 5 ↪ Fin 5 := ⟨![1, 0, 2, 3, 4], by decide⟩

/-- One multiplication: `R 1 := R 1 · R 0` (through `R 2`). -/
def powStep (R : Fin 5 ↪ Fin nr) : WM ns nr :=
  .seq (mulAddW (eP.trans R)) (.seq (WM.clear (R 1)) (WM.move (R 2) (R 1)))

theorem powStep_spec (R : Fin 5 ↪ Fin nr) (σ : WState ns nr) (v : ℕ) (hv : σ.val (R 1) = v)
    (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0)
    (hvb : v * σ.val (R 0) ≤ cap) (hvc : v ≤ cap) (hb : σ.val (R 0) ≤ cap) :
    WExec cap (powStep R) σ (σ.setv (R 1) (v * σ.val (R 0))) (3 * sq cap) := by
  have hne : ∀ {i j : Fin 5}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have f0 : (eP.trans R) 0 = R 1 := rfl
  have f1 : (eP.trans R) 1 = R 0 := rfl
  have f2 : (eP.trans R) 2 = R 2 := rfl
  have f3 : (eP.trans R) 3 = R 3 := rfl
  have f4 : (eP.trans R) 4 = R 4 := rfl
  have h1 := mulAddW_sq cap (eP.trans R) σ (by rw [f3, h3]) (by rw [f4, h4]) (by rw [f1]; exact hb)
    (by rw [f2, f0, f1, h2, hv]; omega) (by rw [f0, hv]; exact hvc)
  rw [f0, f1, f2, h2, hv, Nat.zero_add] at h1
  have g1 : (σ.setv (R 2) (v * σ.val (R 0))).val (R 1) = v := by
    simp [Function.update_apply, hne (show (1 : Fin 5) ≠ 2 by decide), hv]
  have h2' := wclear_spec cap (R 1) v _ g1 (by rw [g1]; exact hvc)
  have h3' := wmove_spec cap (R 2) (R 1) (hne (by decide)) (v * σ.val (R 0))
    ((σ.setv (R 2) (v * σ.val (R 0))).setv (R 1) 0)
    (by simp [Function.update_apply, hne (show (2 : Fin 5) ≠ 1 by decide)])
    (by simp [Function.update_apply, hne (show (2 : Fin 5) ≠ 1 by decide)]; omega)
    (by simp [Function.update_apply, hne (show (2 : Fin 5) ≠ 1 by decide)]; omega)
  have hs := lin_le_sq cap
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2' h3')) ?_ (by nlinarith)
  wgen_eq [h2]

/-- `R 1 := R 0 ^ e` (from `R 1 = 0`); `R = (b, p, t, u, w)`, scratch at `0`. -/
def powConstW (R : Fin 5 ↪ Fin nr) : ℕ → WM ns nr
  | 0 => .inc (R 1)
  | e + 1 => .seq (powConstW R e) (powStep R)

theorem pow_le_of {b e c : ℕ} (hc : 1 ≤ c) (h : b ^ e ≤ c) : ∀ k ≤ e, b ^ k ≤ c := by
  intro k hk
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa using hc
    · rw [Nat.zero_pow hk0]; exact Nat.zero_le _
  · exact le_trans (Nat.pow_le_pow_right hb hk) h

theorem powConstW_spec (R : Fin 5 ↪ Fin nr) :
    ∀ (e : ℕ) (σ : WState ns nr), σ.val (R 1) = 0 → σ.val (R 2) = 0 → σ.val (R 3) = 0 → σ.val (R 4) = 0 →
      1 ≤ cap → σ.val (R 0) ≤ cap → (∀ k ≤ e, σ.val (R 0) ^ k ≤ cap) →
      WExec cap (powConstW R e) σ (σ.setv (R 1) (σ.val (R 0) ^ e)) ((e + 1) * (4 * sq cap))
  | 0, σ, h1, _, _, _, hc, _, _ => by
    have h := WExec.inc (cap := cap) (R 1) σ (by omega)
    have hs := sq_ge cap
    refine WExec.cast cap h ?_ (by omega)
    rw [h1, pow_zero, Nat.zero_add]
  | e + 1, σ, h1, h2, h3, h4, hc, hb, hk => by
    have hne : ∀ {i j : Fin 5}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
    have ih := powConstW_spec R e σ h1 h2 h3 h4 hc hb (fun k hk' => hk k (by omega))
    have hv := hk e (by omega)
    have hv1 := hk (e + 1) le_rfl
    have g0 : (σ.setv (R 1) (σ.val (R 0) ^ e)).val (R 0) = σ.val (R 0) := by
      simp [Function.update_apply, hne (show (0 : Fin 5) ≠ 1 by decide)]
    have hst := powStep_spec cap R (σ.setv (R 1) (σ.val (R 0) ^ e)) (σ.val (R 0) ^ e) (by simp)
      (by simp [Function.update_apply, hne (show (2 : Fin 5) ≠ 1 by decide), h2])
      (by simp [Function.update_apply, hne (show (3 : Fin 5) ≠ 1 by decide), h3])
      (by simp [Function.update_apply, hne (show (4 : Fin 5) ≠ 1 by decide), h4])
      (by rw [g0, ← pow_succ]; exact hv1) hv (by rw [g0]; exact hb)
    rw [g0, ← pow_succ] at hst
    have hs := sq_ge cap
    refine WExec.cast cap (WExec.seq ih hst) (by rw [wsetv_setv]) (by nlinarith)

/-! ## Ceiling quotients -/

def eCD : Fin 9 ↪ Fin 12 := ⟨![3, 1, 2, 4, 5, 6, 7, 8, 9], by decide⟩

/-- `R 2 := ⌈R 0 / R 1⌉` (from `R 2 = 0`, `R 1 ≥ 1`), keeping `R 0, R 1`; through `T = R 3`; scratch `R 4 … R 11`. -/
def ceilDivW (R : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 0) (R 3) (R 4)) (.seq (addTo (R 1) (R 3) (R 4)) (.seq (.dec (R 3))
    (.seq (divW (eCD.trans R)) (WM.clear (R 3)))))

theorem ceilDivW_spec (R : Fin 12 ↪ Fin nr) (σ : WState ns nr) (hz : ∀ i : Fin 12, 2 ≤ i.val → σ.val (R i) = 0)
    (hd : 1 ≤ σ.val (R 1)) (hcap : σ.val (R 0) + σ.val (R 1) ≤ cap) :
    WExec cap (ceilDivW R) σ (σ.setv (R 2) ((σ.val (R 0) + σ.val (R 1) - 1) / σ.val (R 1))) (5 * sq cap) := by
  have hne : ∀ {i j : Fin 12}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  set a := σ.val (R 0) with ha
  set d := σ.val (R 1) with hd'
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 0) (R 3) (R 4) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (hz 3 (by decide)) (hz 4 (by decide)) (by omega)
  have h2 := addTo_spec cap (R 1) (R 3) (R 4) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (σ.setv (R 3) a) (by simp [Function.update_apply, hne (show (4 : Fin 12) ≠ 3 by decide), hz 4 (by decide)])
    (by simp [Function.update_apply, hne (show (1 : Fin 12) ≠ 3 by decide)]; omega)
    (by simp [Function.update_apply, hne (show (1 : Fin 12) ≠ 3 by decide)]; omega)
  have g1 : (σ.setv (R 3) a).val (R 3) + (σ.setv (R 3) a).val (R 1) = a + d := by
    simp [Function.update_apply, hne (show (1 : Fin 12) ≠ 3 by decide), hd']
  rw [g1] at h2
  have h3 := WExec.dec (cap := cap) (R 3) ((σ.setv (R 3) a).setv (R 3) (a + d)) (by simp; omega)
  have e3 : ((σ.setv (R 3) a).setv (R 3) (a + d)).setv (R 3) (((σ.setv (R 3) a).setv (R 3) (a + d)).val (R 3) - 1) =
      σ.setv (R 3) (a + d - 1) := by simp [wsetv_setv]
  rw [e3] at h3
  have k0 : (eCD.trans R) 0 = R 3 := rfl
  have k1 : (eCD.trans R) 1 = R 1 := rfl
  have k2 : (eCD.trans R) 2 = R 2 := rfl
  have k3 : (eCD.trans R) 3 = R 4 := rfl
  have k4 : (eCD.trans R) 4 = R 5 := rfl
  have k5 : (eCD.trans R) 5 = R 6 := rfl
  have k6 : (eCD.trans R) 6 = R 7 := rfl
  have k7 : (eCD.trans R) 7 = R 8 := rfl
  have v3 : (σ.setv (R 3) (a + d - 1)).val (R 3) = a + d - 1 := by simp
  have v1 : (σ.setv (R 3) (a + d - 1)).val (R 1) = d := by
    simp [Function.update_apply, hne (show (1 : Fin 12) ≠ 3 by decide), hd']
  have v2 : (σ.setv (R 3) (a + d - 1)).val (R 2) = 0 := by
    simp [Function.update_apply, hne (show (2 : Fin 12) ≠ 3 by decide), hz 2 (by decide)]
  have vz : ∀ i : Fin 12, 4 ≤ i.val → (σ.setv (R 3) (a + d - 1)).val (R i) = 0 := by
    intro i hi
    have hi3 : i ≠ 3 := by intro h; subst h; simp at hi
    simp [Function.update_apply, hne hi3, hz i (by omega)]
  have h4 := divW_spec cap (eCD.trans R) (σ.setv (R 3) (a + d - 1)) (by rw [k1, v1]; omega)
    (by rw [k3]; exact vz 4 (by decide)) (by rw [k4]; exact vz 5 (by decide)) (by rw [k5]; exact vz 6 (by decide))
    (by rw [k6]; exact vz 7 (by decide)) (by rw [k7]; exact vz 8 (by decide)) (by rw [k0, v3]; omega)
    (by rw [k1, v1]; omega) (by rw [k2, k0, v2, v3]; omega) (by omega)
  rw [k0, k1, k2, v1, v2, v3, Nat.zero_add] at h4
  have v5 : (((σ.setv (R 3) (a + d - 1)).setv (R 3) ((a + d - 1) % d)).setv (R 2) ((a + d - 1) / d)).val (R 3) =
      (a + d - 1) % d := by
    simp [Function.update_apply, hne (show (3 : Fin 12) ≠ 2 by decide)]
  have hmod : (a + d - 1) % d < d := Nat.mod_lt _ (by omega)
  have h5 := wclear_spec cap (R 3) ((a + d - 1) % d) _ v5 (by rw [v5]; omega)
  have hs := lin_le_sq cap
  have hdiv : (a + d - 1 + 2) * (90 * (a + d - 1) + 90 * d + 60) ≤ 2 * sq cap := by
    have e1 : a + d - 1 + 2 ≤ cap + 2 := by omega
    have e2 : 90 * (a + d - 1) + 90 * d + 60 ≤ 180 * (cap + 2) := by omega
    have := Nat.mul_le_mul e1 e2
    unfold sq; nlinarith
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 h5)))) ?_ (by omega)
  wgen_eq [hz 3 (by decide)]

/-! ## Exact upper roots, by search -/

def eW1 : Fin 5 ↪ Fin 7 := ⟨![1, 2, 4, 5, 6], by decide⟩
def eW2 : Fin 6 ↪ Fin 7 := ⟨![0, 2, 3, 4, 5, 6], by decide⟩

def rootTest (j : ℕ) (R : Fin 7 ↪ Fin nr) : WM ns nr :=
  .seq (powConstW (eW1.trans R) (j + 1)) (.seq (gtFlagW (eW2.trans R)) (WM.clear (R 2)))

/-- **`Y := ceilRoot j X`** (from `Y = P = F = 0`), keeping `X`; `R = (X, Y, P, F, t, u, w)`, scratch at `0`. -/
def ceilRootW (j : ℕ) (R : Fin 7 ↪ Fin nr) : WM ns nr :=
  .seq (rootTest j R) (.whr (R 3) (.seq (.dec (R 3)) (.seq (.inc (R 1)) (rootTest j R))))

theorem rootTest_spec (j : ℕ) (R : Fin 7 ↪ Fin nr) (σ : WState ns nr) (hz : ∀ i : Fin 7, 2 ≤ i.val → σ.val (R i) = 0)
    (hc1 : 1 ≤ cap) (hX : σ.val (R 0) ≤ cap) (hY : σ.val (R 1) ≤ cap) (hP : σ.val (R 1) ^ (j + 1) ≤ cap) :
    WExec cap (rootTest j R) σ (σ.setv (R 3) (if σ.val (R 1) ^ (j + 1) < σ.val (R 0) then 1 else 0))
      ((j + 4) * (4 * sq cap)) := by
  have hne : ∀ {i k : Fin 7}, i ≠ k → R i ≠ R k := fun h => R.injective.ne h
  set x := σ.val (R 0) with hx
  set y := σ.val (R 1) with hy
  have a0 : (eW1.trans R) 0 = R 1 := rfl
  have a1 : (eW1.trans R) 1 = R 2 := rfl
  have a2 : (eW1.trans R) 2 = R 4 := rfl
  have a3 : (eW1.trans R) 3 = R 5 := rfl
  have a4 : (eW1.trans R) 4 = R 6 := rfl
  have hc : 1 ≤ cap := hc1
  have h1 := powConstW_spec cap (eW1.trans R) (j + 1) σ (by rw [a1]; exact hz 2 (by decide))
    (by rw [a2]; exact hz 4 (by decide)) (by rw [a3]; exact hz 5 (by decide)) (by rw [a4]; exact hz 6 (by decide))
    hc (by rw [a0]; exact hY) (by rw [a0]; exact pow_le_of hc hP)
  rw [a0, a1] at h1
  have b0 : (eW2.trans R) 0 = R 0 := rfl
  have b1 : (eW2.trans R) 1 = R 2 := rfl
  have b2 : (eW2.trans R) 2 = R 3 := rfl
  have b3 : (eW2.trans R) 3 = R 4 := rfl
  have b4 : (eW2.trans R) 4 = R 5 := rfl
  have b5 : (eW2.trans R) 5 = R 6 := rfl
  have w0 : (σ.setv (R 2) (y ^ (j + 1))).val (R 0) = x := by
    simp [Function.update_apply, hne (show (0 : Fin 7) ≠ 2 by decide), hx]
  have w2 : (σ.setv (R 2) (y ^ (j + 1))).val (R 2) = y ^ (j + 1) := by simp
  have wz : ∀ i : Fin 7, 3 ≤ i.val → (σ.setv (R 2) (y ^ (j + 1))).val (R i) = 0 := by
    intro i hi
    have hi2 : i ≠ 2 := by intro h; subst h; simp at hi
    simp [Function.update_apply, hne hi2, hz i (by omega)]
  have h2 := gtFlagW_spec cap (eW2.trans R) (σ.setv (R 2) (y ^ (j + 1))) (by rw [b2]; exact wz 3 (by decide))
    (by rw [b3]; exact wz 4 (by decide)) (by rw [b4]; exact wz 5 (by decide)) (by rw [b5]; exact wz 6 (by decide))
    (by rw [b0, w0]; exact hX) (by rw [b1, w2]; exact hP) hc
  rw [b0, b1, b2, w0, w2] at h2
  have w3 : ((σ.setv (R 2) (y ^ (j + 1))).setv (R 3) (if y ^ (j + 1) < x then 1 else 0)).val (R 2) = y ^ (j + 1) := by
    simp [Function.update_apply, hne (show (2 : Fin 7) ≠ 3 by decide)]
  have h3 := wclear_spec cap (R 2) (y ^ (j + 1)) _ w3 (by rw [w3]; exact hP)
  have hs := lin_le_sq cap
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by nlinarith)
  wgen_eq [hz 2 (by decide)]

theorem ceilRoot_pow_le (j x : ℕ) : Ledger.ceilRoot j x ^ (j + 1) ≤ 2 ^ (j + 1) * x + 1 := by
  set m := Ledger.ceilRoot j x with hm
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m
    · simp
    · simp
  · have hmin := Ledger.ceilRoot_min j x (by omega)
    rw [← hm] at hmin
    have e1 : m ≤ 2 * (m - 1) := by omega
    have e2 : m ^ (j + 1) ≤ (2 * (m - 1)) ^ (j + 1) := Nat.pow_le_pow_left e1 _
    rw [mul_pow] at e2
    have e3 : 2 ^ (j + 1) * (m - 1) ^ (j + 1) ≤ 2 ^ (j + 1) * x := Nat.mul_le_mul_left _ hmin.le
    omega

theorem lt_of_lt_ceilRoot (j x k : ℕ) (hk : k < Ledger.ceilRoot j x) : k ^ (j + 1) < x := by
  have := Nat.find_min (Ledger.exists_root_ge j x) hk
  exact not_le.mp this

theorem ceilRootW_spec (j : ℕ) (R : Fin 7 ↪ Fin nr) (σ : WState ns nr) (hz : ∀ i : Fin 7, 1 ≤ i.val → σ.val (R i) = 0)
    (hcap : 2 ^ (j + 1) * σ.val (R 0) + 1 ≤ cap) :
    WExec cap (ceilRootW j R) σ (σ.setv (R 1) (Ledger.ceilRoot j (σ.val (R 0))))
      ((σ.val (R 0) + 2) * ((j + 6) * (4 * sq cap))) := by
  have hne : ∀ {i k : Fin 7}, i ≠ k → R i ≠ R k := fun h => R.injective.ne h
  set x := σ.val (R 0) with hx
  set m := Ledger.ceilRoot j x with hm
  have hpow1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have hxc : x ≤ cap := by nlinarith
  have hc1 : 1 ≤ cap := by omega
  have hmx : m ≤ x := Ledger.ceilRoot_le_self j x
  have hmp := ceilRoot_pow_le j x
  have hkp : ∀ k ≤ m, k ^ (j + 1) ≤ cap := fun k hk => le_trans (Nat.pow_le_pow_left hk _) (by rw [hm]; omega)
  let S : ℕ → WState ns nr := fun k => (σ.setv (R 1) k).setv (R 3) (if k ^ (j + 1) < x then 1 else 0)
  have hS : ∀ k ≤ m, WExec cap (rootTest j R) (σ.setv (R 1) k) (S k) ((j + 4) * (4 * sq cap)) := by
    intro k hk
    have h := rootTest_spec cap j R (σ.setv (R 1) k)
      (by intro i hi
          have hi1 : i ≠ 1 := by intro h; subst h; simp at hi
          simp [Function.update_apply, hne hi1, hz i (by omega)])
      hc1 (by simp [Function.update_apply, hne (show (0 : Fin 7) ≠ 1 by decide)]; omega)
      (by simp; omega) (by simp; exact hkp k hk)
    have e0 : (σ.setv (R 1) k).val (R 0) = x := by
      simp [Function.update_apply, hne (show (0 : Fin 7) ≠ 1 by decide), hx]
    simp only [wsetv_val_self, e0] at h
    exact h
  have h0 := hS 0 (Nat.zero_le _)
  have e0 : σ.setv (R 1) 0 = σ := by rw [← hz 1 (by decide), wsetv_same]
  rw [e0] at h0
  have hF : ∀ k < m, (S k).val (R 3) ≠ 0 := by
    intro k hk
    simp [S, lt_of_lt_ceilRoot j x k hk]
  have hstop : (S m).val (R 3) = 0 := by
    have := Ledger.le_ceilRoot_pow j x
    rw [← hm] at this
    simp [S, not_lt.mpr this]
  have hbody : ∀ k < m, WExec cap (.seq (.dec (R 3)) (.seq (.inc (R 1)) (rootTest j R))) (S k) (S (k + 1))
      ((j + 5) * (4 * sq cap)) := by
    intro k hk
    have hk1 : (S k).val (R 3) = 1 := by simp [S, lt_of_lt_ceilRoot j x k hk]
    have d1 := WExec.dec (cap := cap) (R 3) (S k) (by rw [hk1]; exact hc1)
    have g1 : ((S k).setv (R 3) ((S k).val (R 3) - 1)).val (R 1) = k := by
      simp [S, Function.update_apply, hne (show (1 : Fin 7) ≠ 3 by decide)]
    have i1 := WExec.inc (cap := cap) (R 1) ((S k).setv (R 3) ((S k).val (R 3) - 1)) (by rw [g1]; omega)
    have e1 : ((S k).setv (R 3) ((S k).val (R 3) - 1)).setv (R 1)
        (((S k).setv (R 3) ((S k).val (R 3) - 1)).val (R 1) + 1) = σ.setv (R 1) (k + 1) := by
      rw [g1, hk1]
      simp only [S]
      wgen_eq [hz 3 (by decide)]
    rw [e1] at i1
    have ht := hS (k + 1) (by omega)
    have hs := sq_ge cap
    exact WExec.mono (WExec.seq d1 (WExec.seq i1 ht)) (by nlinarith)
  have hloop := flagLoop cap (R 3) _ _ m S hF hstop hbody
  have hs := sq_ge cap
  refine WExec.cast cap (WExec.seq h0 hloop) ?_ ?_
  · simp only [S, hstop]
    have := Ledger.le_ceilRoot_pow j x
    rw [← hm] at this
    rw [if_neg (not_lt.mpr this)]
    wgen_eq [hz 3 (by decide)]
  · have e := Nat.mul_le_mul_right ((j + 5) * (4 * sq cap) + 2) hmx
    nlinarith

end NearCubicWires.WireExponent3_5.PrimAsm.UnaryPow
