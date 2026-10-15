import Proof.Gates.Expand.PolyTabTailCost
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.WordPrograms.Hoare

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

@[simp] theorem rY_ne_rB (i : Fin 112) (j : Fin 10) : rY i ≠ rB j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

@[simp] theorem rB_ne_rY (i : Fin 10) (j : Fin 112) : rB i ≠ rY j := fun h => rY_ne_rB j i h.symm

@[simp] theorem rY_inj (i j : Fin 112) : rY i = rY j ↔ i = j := rY.injective.eq_iff

@[simp] theorem rB_inj (i j : Fin 10) : rB i = rB j ↔ i = j := rB.injective.eq_iff

section Bregs
variable {te qa : ℕ}

/-- `rB 0 := 2 · rB 0` (scratch `rY 103`, `rY 100`, both `0`). -/
def dblB : WMX (NSx te qa) NRk := .seq (addR (rB 0) (rY 103) (rY 100)) (.wm (WM.move (rY 103) (rB 0)))

theorem dblB_spec (cap : ℕ) (σ : WState (NSx te qa) NRk) (h100 : σ.val (rY 100) = 0) (h103 : σ.val (rY 103) = 0)
    (hcap : 2 * σ.val (rB 0) ≤ cap) :
    WXExec cap (dblB (te := te) (qa := qa)) σ (σ.setv (rB 0) (2 * σ.val (rB 0))) (25 * σ.val (rB 0) + 5) := by
  have e1 := addR_spec cap (A := rB 0) (B := rY 103) (T := rY 100) (by simp) (by simp) (by simp) σ h100
    (by rw [h103]; omega)
  set σ1 := σ.setv (rY 103) (σ.val (rY 103) + σ.val (rB 0)) with hσ1
  have v103 : σ1.val (rY 103) = σ.val (rB 0) := by simp [hσ1, h103]
  have v0 : σ1.val (rB 0) = σ.val (rB 0) := by simp [hσ1]
  have e2 := wmove_spec (cap := cap) (rY 103) (rB 0) (by simp) (σ.val (rB 0)) σ1 v103 (by rw [v103]; omega)
    (by rw [v103, v0]; omega)
  refine (WXExec.seq e1 (WXExec.wm e2)).cast cap ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [WState.setv_val, Function.update_apply, hσ1]
  by_cases r0 : r = rB 0
  · subst r0; simp; omega
  · by_cases r3 : r = rY 103
    · subst r3; simp [h103]
    · simp [r0, r3]

structure BregsPost (σ τ : WState (NSx te qa) NRk) (d p : ℕ) (o : Bool) : Prop where
  st : τ.st = σ.st
  sh : τ.sh = σ.sh
  cell : τ.cell = σ.cell
  b0 : τ.val (rB 0) = 2 ^ (2 * d - o.toNat)
  b1 : τ.val (rB 1) = 0
  b2 : τ.val (rB 2) = d + 2 * p + 5
  b3 : τ.val (rB 3) = d + 2 * p + 5 - 1
  b4 : τ.val (rB 4) = 0
  b5 : τ.val (rB 5) = 0
  b6 : τ.val (rB 6) = 0
  b7 : τ.val (rB 7) = 0
  b8 : τ.val (rB 8) = 0
  b9 : τ.val (rB 9) = o.toNat
  y : ∀ i : Fin 112, i ≠ 101 → τ.val (rY i) = σ.val (rY i)

theorem nOf_pow (d : ℕ) (o : Bool) (hd : 1 ≤ d) :
    (if o then 2 ^ d * (2 ^ d / 2) else 2 ^ d * 2 ^ d) = 2 ^ (2 * d - o.toNat) := by
  cases o
  · simp [← pow_add, two_mul]
  · simp only [if_true, Bool.toNat_true]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have h2 : 2 ^ (e + 1) / 2 = 2 ^ e := by rw [pow_succ]; simp
    rw [h2, show 2 * (e + 1) - 1 = (e + 1) + e by omega, pow_add]
    ring

/-- The straight-line part of `bregs`. -/
def bregsA : WMX (NSx te qa) NRk :=
  .seq (addR (rY 105) (rB 2) (rY 100)) <|
  .seq (addR (rY 106) (rB 2) (rY 100)) <|
  .seq (addR (rY 106) (rB 2) (rY 100)) <|
  .seq (WMX.inc (rB 2)) <| .seq (WMX.inc (rB 2)) <| .seq (WMX.inc (rB 2)) <| .seq (WMX.inc (rB 2)) <|
  .seq (WMX.inc (rB 2)) <|
  .seq (addR (rB 2) (rB 3) (rY 100)) <|
  .seq (WMX.dec (rB 3)) <|
  .seq (addR (rY 107) (rB 9) (rY 100)) <|
  .seq (addR (rY 105) (rY 101) (rY 100)) <|
  .seq (addR (rY 105) (rY 101) (rY 100)) <|
  .seq (.ifr (rY 107) (WMX.dec (rY 101)) WMX.skip) <|
  (WMX.inc (rB 0))

/-- The state after the straight-line part. -/
def bregsSt (σ : WState (NSx te qa) NRk) (d p : ℕ) (o : Bool) : WState (NSx te qa) NRk :=
  ((((σ.setv (rB 2) (d + 2 * p + 5)).setv (rB 3) (d + 2 * p + 4)).setv (rB 9) o.toNat).setv (rY 101)
    (2 * d - o.toNat)).setv (rB 0) 1

/-- The register program of the tail. -/
def bregs : WMX (NSx te qa) NRk := .seq bregsA (.whr (rY 101) (.seq (WMX.dec (rY 101)) dblB))

/-- The straight-line part's cost bound. -/
def bregsACost (d p : ℕ) : ℕ := 72 * d + 72 * p + 250

section Spec
variable (cap d p : ℕ) (o : Bool) (σ : WState (NSx te qa) NRk)

theorem wx {P : WMX (NSx te qa) NRk} {X Y Y' : WState (NSx te qa) NRk} {c c' : ℕ} (h : WXExec cap P X Y c)
    (hY : Y = Y') (hc : c ≤ c') : WXExec cap P X Y' c' := h.cast cap hY hc

theorem bregsA_spec (h100 : σ.val (rY 100) = 0) (h101 : σ.val (rY 101) = 0) (h105 : σ.val (rY 105) = d)
    (h106 : σ.val (rY 106) = p) (h107 : σ.val (rY 107) = o.toNat) (hB : ∀ j : Fin 10, σ.val (rB j) = 0)
    (hcap : 2 * d + 2 * p + 10 ≤ cap) :
    WXExec cap (bregsA (te := te) (qa := qa)) σ (bregsSt σ d p o) (bregsACost d p) := by
  have ho : o.toNat ≤ 1 := by cases o <;> simp
  have hB0 := hB 0
  have hB2 := hB 2
  have hB3 := hB 3
  have hB9 := hB 9
  -- rB 2 := d + 2p + 5
  have e1 : WXExec cap (addR (rY 105) (rB 2) (rY 100)) σ (σ.setv (rB 2) d) (18 * d + 3) :=
    wx cap (addR_spec cap (A := rY 105) (B := rB 2) (T := rY 100) (by simp) (by simp) (by simp) σ h100
      (by rw [hB2, h105]; omega)) (by rw [hB2, h105, Nat.zero_add]) (by rw [h105])
  have e2 : WXExec cap (addR (rY 106) (rB 2) (rY 100)) (σ.setv (rB 2) d) (σ.setv (rB 2) (d + p)) (18 * p + 3) :=
    wx cap (addR_spec cap (A := rY 106) (B := rB 2) (T := rY 100) (by simp) (by simp) (by simp) _
      (by simp [h100]) (by simp [h106]; omega)) (by simp [h106, wsetv_setv]) (by simp [h106])
  have e3 : WXExec cap (addR (rY 106) (rB 2) (rY 100)) (σ.setv (rB 2) (d + p)) (σ.setv (rB 2) (d + 2 * p))
      (18 * p + 3) :=
    wx cap (addR_spec cap (A := rY 106) (B := rB 2) (T := rY 100) (by simp) (by simp) (by simp) _
      (by simp [h100]) (by simp [h106]; omega))
      (by rw [show d + 2 * p = d + p + p by omega]; simp [h106, wsetv_setv]) (by simp [h106])
  have inc2 : ∀ v, v + 1 ≤ cap → WXExec cap (WMX.inc (rB 2)) (σ.setv (rB 2) v) (σ.setv (rB 2) (v + 1)) 3 :=
    fun v hv => wx cap (WXExec.inc cap (rB 2) _ (by simp; omega)) (by simp [wsetv_setv]) le_rfl
  have i1 := inc2 (d + 2 * p) (by omega)
  have i2 := inc2 (d + 2 * p + 1) (by omega)
  have i3 := inc2 (d + 2 * p + 1 + 1) (by omega)
  have i4 := inc2 (d + 2 * p + 1 + 1 + 1) (by omega)
  have i5 := inc2 (d + 2 * p + 1 + 1 + 1 + 1) (by omega)
  set v5 := d + 2 * p + 1 + 1 + 1 + 1 + 1 with hv5
  -- rB 3 := v5 − 1
  have e4 : WXExec cap (addR (rB 2) (rB 3) (rY 100)) (σ.setv (rB 2) v5) ((σ.setv (rB 2) v5).setv (rB 3) v5)
      (18 * v5 + 3) :=
    wx cap (addR_spec cap (A := rB 2) (B := rB 3) (T := rY 100) (by simp) (by simp) (by simp) _
      (by simp [h100]) (by simp [hB3]; omega)) (by simp [hB3]) (by simp)
  have e5 : WXExec cap (WMX.dec (rB 3)) ((σ.setv (rB 2) v5).setv (rB 3) v5) ((σ.setv (rB 2) v5).setv (rB 3) (v5 - 1)) 1 :=
    wx cap (WXExec.dec cap (rB 3) _ (by simp; omega)) (by simp [wsetv_setv]) le_rfl
  set S10 := (σ.setv (rB 2) v5).setv (rB 3) (v5 - 1) with hS10
  -- rB 9 := odd
  have e6 : WXExec cap (addR (rY 107) (rB 9) (rY 100)) S10 (S10.setv (rB 9) o.toNat) (18 * 1 + 3) :=
    wx cap (addR_spec cap (A := rY 107) (B := rB 9) (T := rY 100) (by simp) (by simp) (by simp) _
      (by simp [hS10, h100]) (by simp [hS10, h107, hB9]; omega)) (by simp [hS10, h107, hB9])
      (by simp [hS10, h107]; omega)
  set S11 := S10.setv (rB 9) o.toNat with hS11
  -- rY 101 := 2d − odd
  have e7 : WXExec cap (addR (rY 105) (rY 101) (rY 100)) S11 (S11.setv (rY 101) d) (18 * d + 3) :=
    wx cap (addR_spec cap (A := rY 105) (B := rY 101) (T := rY 100) (by simp) (by simp) (by simp) _
      (by simp [hS11, hS10, h100]) (by simp [hS11, hS10, h101, h105]; omega)) (by simp [hS11, hS10, h101, h105])
      (by simp [hS11, hS10, h105])
  have e8 : WXExec cap (addR (rY 105) (rY 101) (rY 100)) (S11.setv (rY 101) d) (S11.setv (rY 101) (d + d))
      (18 * d + 3) :=
    wx cap (addR_spec cap (A := rY 105) (B := rY 101) (T := rY 100) (by simp) (by simp) (by simp) _
      (by simp [hS11, hS10, h100]) (by simp [hS11, hS10, h105]; omega)) (by simp [hS11, hS10, h105, wsetv_setv])
      (by simp [hS11, hS10, h105])
  have e9 : WXExec cap (.ifr (rY 107) (WMX.dec (rY 101)) WMX.skip) (S11.setv (rY 101) (d + d))
      (S11.setv (rY 101) (2 * d - o.toNat)) 2 := by
    cases o with
    | false =>
      have h0 : (S11.setv (rY 101) (d + d)).val (rY 107) = 0 := by simp [hS11, hS10, h107]
      exact wx cap (WXExec.ifrF (P := WMX.dec (rY 101)) h0 (WXExec.skip (cap := cap) _)) (by simp; ring_nf)
        (by omega)
    | true =>
      have h1 : (S11.setv (rY 101) (d + d)).val (rY 107) ≠ 0 := by simp [hS11, hS10, h107]
      exact wx cap (WXExec.ifrT (Q := WMX.skip) h1 (WXExec.dec cap (rY 101) _ (by simp; omega)))
        (by rw [show 2 * d - true.toNat = d + d - 1 by simp; omega]; simp [wsetv_setv]) le_rfl
  have e10 : WXExec cap (WMX.inc (rB 0)) (S11.setv (rY 101) (2 * d - o.toNat))
      ((S11.setv (rY 101) (2 * d - o.toNat)).setv (rB 0) 1) 3 :=
    wx cap (WXExec.inc cap (rB 0) _ (by simp [hS11, hS10, hB0]; omega)) (by simp [hS11, hS10, hB0]) le_rfl
  have hfin : (S11.setv (rY 101) (2 * d - o.toNat)).setv (rB 0) 1 = bregsSt σ d p o := by
    simp only [hS11, hS10, bregsSt, hv5]
    congr 3
  unfold bregsA
  refine wx cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq i1 (WXExec.seq i2 (WXExec.seq i3
    (WXExec.seq i4 (WXExec.seq i5 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq e7 (WXExec.seq e8
    (WXExec.seq e9 e10)))))))))))))) hfin ?_
  unfold bregsACost
  omega

/-- The doubling loop, from `rY 101 = k`, `rB 0 = 2^(m − k)`. -/
theorem loopB_spec (m : ℕ) (S : WState (NSx te qa) NRk) (h100 : S.val (rY 100) = 0) (h103 : S.val (rY 103) = 0)
    (hcap : 2 ^ m ≤ cap) :
    ∀ k, k ≤ m → Runs cap (.whr (rY 101) (.seq (WMX.dec (rY 101)) (dblB (te := te) (qa := qa))))
      ((S.setv (rY 101) k).setv (rB 0) (2 ^ (m - k))) (k * ((25 * 2 ^ m + 7) + 2) + 1)
      (fun τ => τ = (S.setv (rY 101) 0).setv (rB 0) (2 ^ m)) := by
  intro k hk
  refine Runs.whr (r := rY 101) (P := .seq (WMX.dec (rY 101)) (dblB (te := te) (qa := qa)))
    (fun k τ => k ≤ m ∧ τ = (S.setv (rY 101) k).setv (rB 0) (2 ^ (m - k))) (25 * 2 ^ m + 7) _
    (fun τ ⟨_, hτ⟩ => ⟨by rw [hτ]; simp, by rw [hτ]; simp⟩) (fun j τ ⟨hj, hτ⟩ => ⟨by rw [hτ]; simp, ?_⟩) k _
    ⟨hk, rfl⟩
  · have hp : 2 * 2 ^ (m - (j + 1)) = 2 ^ (m - j) := by
      rw [← pow_succ']; congr 1; omega
    have hpm : 2 ^ (m - j) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : WXExec cap (WMX.dec (rY 101)) τ (((S.setv (rY 101) j).setv (rB 0) (2 ^ (m - (j + 1))))) 1 := by
      refine wx cap (WXExec.dec cap (rY 101) τ ?_) ?_ le_rfl
      · have := Nat.lt_two_pow_self (n := m)
        rw [hτ]; simp; omega
      · rw [hτ]
        apply WState.eq <;> try rfl
        funext r
        simp only [WState.setv_val, Function.update_apply]
        by_cases r1 : r = rY 101
        · subst r1; simp
        · by_cases r0 : r = rB 0
          · subst r0; simp
          · simp [r1, r0]
    have e2 := dblB_spec (te := te) (qa := qa) cap ((S.setv (rY 101) j).setv (rB 0) (2 ^ (m - (j + 1))))
      (by simp [h100]) (by simp [h103]) (by simp; omega)
    refine ⟨_, WXExec.mono (WXExec.seq e1 e2) ?_, hj.trans' (by omega), ?_⟩
    · simp only [WState.setv_val, Function.update_self]
      have : 2 ^ (m - (j + 1)) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · rw [wsetv_setv]; simp only [WState.setv_val, Function.update_self, hp]

/-- **The tail's registers.** -/
theorem bregs_spec (h100 : σ.val (rY 100) = 0) (h101 : σ.val (rY 101) = 0) (h103 : σ.val (rY 103) = 0)
    (h105 : σ.val (rY 105) = d) (h106 : σ.val (rY 106) = p) (h107 : σ.val (rY 107) = o.toNat)
    (hB : ∀ j : Fin 10, σ.val (rB j) = 0) (hcap : 2 ^ (2 * d) + 2 * d + 2 * p + 10 ≤ cap) :
    Runs cap (bregs (te := te) (qa := qa)) σ (bregsCost d p) (BregsPost σ · d p o) := by
  have ho : o.toNat ≤ 1 := by cases o <;> simp
  set m := 2 * d - o.toNat with hm
  have hm2 : 2 ^ m ≤ 2 ^ (2 * d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 1 ≤ 2 ^ (2 * d) := Nat.one_le_two_pow
  have hc1 : 2 * d + 2 * p + 10 ≤ cap := by omega
  have eA := bregsA_spec cap d p o σ h100 h101 h105 h106 h107 hB hc1
  set S := bregsSt σ d p o with hSdef
  have hS : (S.setv (rY 101) m).setv (rB 0) (2 ^ (m - m)) = S := by
    rw [Nat.sub_self, pow_zero, hSdef]
    unfold bregsSt
    apply WState.eq <;> try rfl
    funext r
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all
  have hL := loopB_spec (te := te) (qa := qa) cap m S (by simp [hSdef, bregsSt, h100]) (by simp [hSdef, bregsSt, h103])
    (hm2.trans (by omega)) m le_rfl
  rw [hS] at hL
  have hm2' : m * ((25 * 2 ^ m + 7) + 2) ≤ (2 * d) * (25 * 2 ^ (2 * d) + 9) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hYZ : (2 * d) * (25 * 2 ^ (2 * d) + 9) ≤ (2 * d + 1) * (25 * 2 ^ (2 * d) + 20) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine ((Runs.seqE eA hL).cost ?_).post ?_
  · unfold bregsACost bregsCost
    have e1 : m * (25 * 2 ^ m + 7 + 2) = m * ((25 * 2 ^ m + 7) + 2) := rfl
    omega
  · intro τ hτ
    have hB1 := hB 1
    have hB4 := hB 4
    have hB5 := hB 5
    have hB6 := hB 6
    have hB7 := hB 7
    have hB8 := hB 8
    subst hτ
    have hne : ∀ j : Fin 10, j ≠ 0 → rB j ≠ rB 0 := fun j hj e => hj (rB.injective e)
    refine ⟨rfl, rfl, rfl, by simp [hm], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
    · simp [hSdef, bregsSt, hB1]
    · simp [hSdef, bregsSt]
    · simp [hSdef, bregsSt]
    · simp [hSdef, bregsSt, hB4]
    · simp [hSdef, bregsSt, hB5]
    · simp [hSdef, bregsSt, hB6]
    · simp [hSdef, bregsSt, hB7]
    · simp [hSdef, bregsSt, hB8]
    · simp [hSdef, bregsSt]
    · have : rY i ≠ rY 101 := fun e => hi (rY.injective e)
      simp [hSdef, bregsSt, this]

end Spec

end Bregs

end NearCubicGates.Close.Expand.PolyTab
