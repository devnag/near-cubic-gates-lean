import Proof.Gates.Succinct.IntegerRoot

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

deriving instance Fintype for FReg
deriving instance Fintype for EReg

/-- The succinct verifier's registers (paper lem:succinct-verifier, stages (1)–(4)). -/
inductive VReg where
  | e (r : EReg)
  | nn | nu | p | x | x2 | y | t | g | h | z | f | c | nN | nu2 | i | top | ht | wop | wrp | k2 | hcx
  deriving DecidableEq, Fintype

/-- One test: `F := [(NU+1)^{G+2} ≤ NN]`. -/
def stepF (G : ℕ) (E : VReg → Fin nr) : WMX ns nr :=
  .seq (addR (E .nu) (E .p) (E .t)) (.seq (WMX.inc (E .p)) (.seq (powW (E .x) (E .x2) (E .p) (E .y) (E .t) (G + 2))
    (.seq (leW (E .x) (E .nn) (E .g) (E .h) (E .z) (E .f) (E .t)) (.seq (.wm (WM.clear (E .x))) (.wm (WM.clear (E .p)))))))

/-- The cost class of one test. -/
def stepCost (G n : ℕ) : ℕ := 300 * (G + 3) * (n + 2) ^ (G + 3)

/-- The test's scratch registers. -/
def stepScratch : List VReg := [.p, .x, .x2, .y, .t, .g, .h, .z, .f]

theorem stepF_spec (cap G : ℕ) (E : VReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr) (n k : ℕ)
    (hnn : σ.val (E .nn) = n) (hnu : σ.val (E .nu) = k) (hk : k ≤ n)
    (hz : ∀ q ∈ stepScratch, σ.val (E q) = 0) (hcap : 3 * (n + 2) ^ (G + 3) + 2 * n + 10 ≤ cap) :
    WXExec cap (stepF G E) σ (σ.setv (E .f) (if (k + 1) ^ (G + 2) ≤ n then 1 else 0)) (stepCost G n) := by
  have zp := hz .p (by simp [stepScratch]); have zx := hz .x (by simp [stepScratch])
  have zx2 := hz .x2 (by simp [stepScratch]); have zy := hz .y (by simp [stepScratch])
  have zt := hz .t (by simp [stepScratch]); have zg := hz .g (by simp [stepScratch])
  have zh := hz .h (by simp [stepScratch]); have zz := hz .z (by simp [stepScratch])
  have zf := hz .f (by simp [stepScratch])
  have hpow : (k + 2) ^ (G + 3) ≤ (n + 2) ^ (G + 3) := Nat.pow_le_pow_left (by omega) _
  have hpow2 : (k + 1) ^ (G + 2) ≤ (n + 2) ^ (G + 3) :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hpow3 : 1 ≤ (n + 2) ^ (G + 3) := Nat.one_le_pow _ _ (by omega)
  -- `P := ν + 1`
  have s1 := addR_spec cap (A := E .nu) (B := E .p) (T := E .t) (hE.ne (by decide)) (hE.ne (by decide))
    (hE.ne (by decide)) σ zt (by omega)
  rw [zp, hnu, Nat.zero_add] at s1
  have s2 := WXExec.inc cap (E .p) (σ.setv (E .p) k) (by simp; omega)
  rw [show (σ.setv (E .p) k).setv (E .p) ((σ.setv (E .p) k).val (E .p) + 1) = σ.setv (E .p) (k + 1) by
    simp [wsetv_setv]] at s2
  -- `X := (ν+1)^{G+2}`
  have s3 := powW_spec cap (E .x) (E .x2) (E .p) (E .y) (E .t) (by simp [List.nodup_cons, hE.eq_iff]) (k + 1) (G + 2)
    (σ.setv (E .p) (k + 1)) (by simp [Function.update_apply, hE.eq_iff, zx]) (by simp)
    (by simp [Function.update_apply, hE.eq_iff, zx2]) (by simp [Function.update_apply, hE.eq_iff, zy])
    (by simp [Function.update_apply, hE.eq_iff, zt])
    (by have : (k + 1 + 1) ^ (G + 2) ≤ (n + 2) ^ (G + 3) :=
          (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
        omega)
  -- `F := [X ≤ n]`
  have s4 := leW_spec cap (E .x) (E .nn) (E .g) (E .h) (E .z) (E .f) (E .t) (by simp [List.nodup_cons, hE.eq_iff])
    ((σ.setv (E .p) (k + 1)).setv (E .x) ((k + 1) ^ (G + 2)))
    (by simp [Function.update_apply, hE.eq_iff, zg]) (by simp [Function.update_apply, hE.eq_iff, zh])
    (by simp [Function.update_apply, hE.eq_iff, zz]) (by simp [Function.update_apply, hE.eq_iff, zf])
    (by simp [Function.update_apply, hE.eq_iff, zt])
    (by simp [Function.update_apply, hE.eq_iff, hnn]; omega)
  have hv : ((σ.setv (E .p) (k + 1)).setv (E .x) ((k + 1) ^ (G + 2))).val (E .x) = (k + 1) ^ (G + 2) := by simp
  have hv2 : ((σ.setv (E .p) (k + 1)).setv (E .x) ((k + 1) ^ (G + 2))).val (E .nn) = n := by
    simp [Function.update_apply, hE.eq_iff, hnn]
  rw [hv, hv2] at s4
  set σ4 := ((σ.setv (E .p) (k + 1)).setv (E .x) ((k + 1) ^ (G + 2))).setv (E .f)
    (if (k + 1) ^ (G + 2) ≤ n then 1 else 0) with hσ4
  have s5 := wclear_spec cap (E .x) ((k + 1) ^ (G + 2)) σ4 (by simp [σ4, Function.update_apply, hE.eq_iff])
    (by simp [σ4, Function.update_apply, hE.eq_iff]; omega)
  have s6 := wclear_spec cap (E .p) (k + 1) (σ4.setv (E .x) 0) (by simp [σ4, Function.update_apply, hE.eq_iff])
    (by simp [σ4, Function.update_apply, hE.eq_iff]; omega)
  refine WXExec.cast cap (WXExec.seq s1 (WXExec.seq s2 (WXExec.seq s3 (WXExec.seq s4 (WXExec.seq (WXExec.wm s5)
    (WXExec.wm s6)))))) ?_ ?_
  · refine WState.eq rfl rfl ?_ rfl
    funext q; simp only [σ4, WState.setv_val, Function.update_apply]
    by_cases hqp : q = E .p
    · subst hqp; simp [hE.eq_iff, zp]
    · by_cases hqx : q = E .x
      · subst hqx; simp [hE.eq_iff, zx]
      · simp [hqp, hqx]
  · unfold stepCost
    have hk1 : k + 1 ≤ n + 2 := by omega
    have e1 : (G + 2) * (61 * (k + 1 + 1) ^ (G + 2)) ≤ (G + 2) * (61 * (n + 2) ^ (G + 3)) := by
      have : (k + 1 + 1) ^ (G + 2) ≤ (n + 2) ^ (G + 3) :=
        (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
    have e2 : (G + 3) * (n + 2) ^ (G + 3) = (G + 2) * (n + 2) ^ (G + 3) + (n + 2) ^ (G + 3) := by ring
    have e3 : n + 2 ≤ (n + 2) ^ (G + 3) := Nat.le_self_pow (by omega) _
    nlinarith

def rootW (G : ℕ) (E : VReg → Fin nr) : WMX ns nr :=
  .seq (stepF G E) (.whr (E .f) (.seq (WMX.dec (E .f)) (.seq (WMX.inc (E .nu)) (stepF G E))))

theorem rootW_spec (cap G : ℕ) (E : VReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr) (n : ℕ)
    (hnn : σ.val (E .nn) = n) (hnu : σ.val (E .nu) = 0)
    (hz : ∀ q ∈ stepScratch, σ.val (E q) = 0) (hcap : 3 * (n + 2) ^ (G + 3) + 2 * n + 10 ≤ cap) :
    WXExec cap (rootW G E) σ (σ.setv (E .nu) (rootOf G n)) ((n + 2) * (stepCost G n + 10)) := by
  set R := rootOf G n with hR
  have hRn : R ≤ n := rootOf_le G n
  let st : ℕ → WState ns nr := fun k => (σ.setv (E .nu) k).setv (E .f) (if k < R then 1 else 0)
  have hst : ∀ k ≤ R, ∀ q ∈ stepScratch, (st k).val (E q) = 0 ∨ q = .f := by
    intro k _ q hq
    by_cases hqf : q = .f
    · right; exact hqf
    · left; simp [st, Function.update_apply, hE.eq_iff, hqf]
      have : q ≠ .nu := by intro h; subst h; simp [stepScratch] at hq
      simp [this]; exact hz q hq
  -- the first test
  have e0 := stepF_spec cap G E hE σ n 0 hnn hnu (by omega) hz hcap
  rw [show (if (0 + 1) ^ (G + 2) ≤ n then 1 else 0) = (if 0 < R then 1 else 0) by
    simp only [pow_le_iff_lt_root]; rfl] at e0
  have hs0 : σ.setv (E .f) (if 0 < R then 1 else 0) = st 0 := by
    simp only [st]; rw [← hnu, wsetv_same, hnu]
  rw [hs0] at e0
  -- the loop
  have hloop := Runs.whr (cap := cap) (r := E .f) (P := .seq (WMX.dec (E .f)) (.seq (WMX.inc (E .nu)) (stepF G E)))
    (fun m τ => m ≤ R ∧ τ = st (R - m)) (stepCost G n + 10) (fun τ => τ = st R)
    (by
      rintro τ ⟨_, rfl⟩
      refine ⟨by simp [st], by simp⟩)
    (by
      rintro m τ ⟨hm, rfl⟩
      refine ⟨by simp [st]; omega, ?_⟩
      set k := R - (m + 1) with hk
      have hkR : k < R := by omega
      have d1 := WXExec.dec cap (E .f) (st k) (by simp [st]; split_ifs <;> omega)
      have d2 := WXExec.inc cap (E .nu) ((st k).setv (E .f) ((st k).val (E .f) - 1))
        (by simp [st, Function.update_apply, hE.eq_iff]; omega)
      set τ2 := ((st k).setv (E .f) ((st k).val (E .f) - 1)).setv (E .nu)
        (((st k).setv (E .f) ((st k).val (E .f) - 1)).val (E .nu) + 1) with hτ2
      have d3 := stepF_spec cap G E hE τ2 n (k + 1) (by simp [τ2, st, Function.update_apply, hE.eq_iff, hnn])
        (by simp [τ2, st, Function.update_apply, hE.eq_iff]) (by omega)
        (by
          intro q hq
          have hqnu : q ≠ .nu := by intro h; subst h; simp [stepScratch] at hq
          by_cases hqf : q = .f
          · subst hqf; simp [τ2, st, Function.update_apply, hE.eq_iff, hkR]
          · simp [τ2, st, Function.update_apply, hE.eq_iff, hqf, hqnu]; exact hz q hq) hcap
      refine ⟨_, WXExec.mono (WXExec.seq d1 (WXExec.seq d2 d3)) (by omega), by omega, ?_⟩
      simp only [pow_le_iff_lt_root]
      rw [← hR, show R - m = k + 1 by omega]
      refine WState.eq rfl rfl ?_ rfl
      funext q; simp only [τ2, st, WState.setv_val, Function.update_apply]
      by_cases hqf : q = E .f
      · subst hqf; simp [hE.eq_iff]
      · by_cases hqn : q = E .nu
        · subst hqn; simp [hE.eq_iff]
        · simp [hqf, hqn])
    R (st 0) ⟨le_rfl, by simp⟩
  obtain ⟨τ, e1, hτ⟩ := hloop
  refine WXExec.cast cap (WXExec.seq e0 e1) ?_ ?_
  · rw [hτ]; simp only [st, lt_irrefl, if_false]
    refine WState.eq rfl rfl ?_ rfl
    funext q; simp only [WState.setv_val, Function.update_apply]
    by_cases hqf : q = E .f
    · subst hqf; simp [hE.eq_iff]; exact (hz .f (by simp [stepScratch])).symm
    · simp [hqf]
  · have hS : 2 * n ≤ stepCost G n := by
      unfold stepCost
      have : n + 2 ≤ (n + 2) ^ (G + 3) := Nat.le_self_pow (by omega) _
      nlinarith
    generalize stepCost G n = S at hS ⊢
    have h1 : R * (S + 10 + 2) ≤ n * (S + 10 + 2) := Nat.mul_le_mul_right _ hRn
    have h2 : (n + 2) * (S + 10) = n * S + 2 * S + 10 * n + 20 := by ring
    have h3 : n * (S + 10 + 2) = n * S + 12 * n := by ring
    rw [h2]
    rw [h3] at h1
    generalize n * S = M at h1 ⊢
    generalize R * (S + 10 + 2) = Q at h1 ⊢
    omega

end NearCubicGates.Close.Succinct
