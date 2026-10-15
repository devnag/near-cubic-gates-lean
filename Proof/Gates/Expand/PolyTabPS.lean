import Proof.Gates.Expand.PolyTabStage1

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def RXL : List (Fin NRk) := List.ofFn rX

theorem rX_mem (j : Fin 64) : rX j ∈ RXL := List.mem_ofFn.mpr ⟨j, rfl⟩

theorem se_ext {σ0 σ τ : WSt} {S S' : List (Fin (NSx te qa + 1))} {R R' : List (Fin NRk)}
    (h1 : SameExcept σ0 σ S R) (h2 : SameExcept σ τ S' R') (hS : ∀ x ∈ S', x ∈ S) (hR : ∀ r ∈ R', r ∈ R) :
    SameExcept σ0 τ S R := SameExcept.trans h1 (h2.weaken hS hR)

structure PS (σ0 : WSt) (X : Fin (NSx te qa + 1)) (Sx : List (Fin (NSx te qa + 1))) (L : List ℕ) (rest : List Bool)
    (i : ℕ) (f : Fin 64 → ℕ) (σ : WSt) : Prop where
  pos : NatAt X L rest σ i
  x : ∀ j, σ.val (rX j) = f j
  fr : SameExcept σ0 σ (X :: Sx) RXL

section Steps
variable {σ0 : WState (NSx te qa) NRk} {X : Fin (NSx te qa + 1)} {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool}

theorem rX_ne {a b : Fin 64} (h : a ≠ b) : rX a ≠ rX b := rX.injective.ne h

theorem upd_x {σ τ : WSt} {f : Fin 64 → ℕ} (hx : ∀ j, σ.val (rX j) = f j) (j : Fin 64) (v : ℕ)
    (hτ : τ.val (rX j) = v) (hfr : ∀ k, k ≠ j → τ.val (rX k) = σ.val (rX k)) :
    ∀ k, τ.val (rX k) = Function.update f j v k := by
  intro k
  by_cases hk : k = j
  · subst hk; simp [hτ]
  · rw [Function.update_of_ne hk, hfr k hk, hx]

theorem ps_rd (cap : ℕ) (j : Fin 64) (hj : j.val ∉ [3, 4, 5, 6]) {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (hi : i < L.length) (h3 : f 3 = 0) (h4 : f 4 = 0) (h5 : f 5 = 0) (h6 : f 6 = 0)
    (hfj : f j = 0) (hcap : 2 ^ (natBitLength L[i] + 1) ≤ cap) :
    Runs cap (rdF X (rX j)) σ (rdCost L[i]) (PS σ0 X Sx L rest (i + 1) (Function.update f j L[i])) := by
  have hv : ∀ k : Fin 64, k.val ∈ [3, 4, 5, 6] → rX k ≠ rX j := fun k hk e => hj (by
    rw [← rX.injective e]; exact hk)
  refine (rdF_spec cap X (rX j) hv L rest σ i h.pos hi (by rw [h.x, h3]) (by rw [h.x, h4]) (by rw [h.x, h5])
    (by rw [h.x, h6]) (by rw [h.x, hfj]) hcap).post fun τ ⟨a, b, c⟩ => ⟨a, upd_x h.x j _ b fun k hk =>
      c.val (by simp only [List.mem_singleton]; exact rX_ne hk), se_ext h.fr c (by simp) (by simp [rX_mem])⟩

theorem ps_sk (cap : ℕ) (j : Fin 64) (hj : j.val ∉ [3, 4]) {i m : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (hm : i + m ≤ L.length) (h3 : f 3 = 0) (h4 : f 4 = 0) (hfj : f j = m)
    (hfit : ∀ x ∈ L, natBitLength x + 1 ≤ cap) (hcm : m ≤ cap) :
    Runs cap (skF X (rX j)) σ (skCost ((L.drop i).take m)) (PS σ0 X Sx L rest (i + m) (Function.update f j 0)) := by
  have hv : ∀ k : Fin 64, k.val ∈ [3, 4] → rX k ≠ rX j := fun k hk e => hj (by rw [← rX.injective e]; exact hk)
  refine (skF_spec cap X (rX j) hv L rest σ i m h.pos hm (by rw [h.x, h3]) (by rw [h.x, h4]) (by rw [h.x, hfj]) hfit
    hcm).post fun τ ⟨a, b, c⟩ => ⟨a, upd_x h.x j _ b fun k hk =>
      c.val (by simp only [List.mem_singleton]; exact rX_ne hk), se_ext h.fr c (by simp) (by simp [rX_mem])⟩

theorem ps_reg {i : ℕ} {f : Fin 64 → ℕ} {σ τ : WSt} (h : PS σ0 X Sx L rest i f σ) (j : Fin 64) (v : ℕ)
    (hτ : τ = σ.setv (rX j) v) : PS σ0 X Sx L rest i (Function.update f j v) τ := by
  subst hτ
  refine ⟨⟨h.pos.1, h.pos.2⟩, upd_x h.x j v (by simp) fun k hk => ?_, se_ext h.fr
    (sameExcept_setv (S := []) σ (List.mem_singleton_self _) v) (fun x hx => by simp at hx) (by simp [rX_mem])⟩
  show Function.update σ.val (rX j) v (rX k) = σ.val (rX k)
  rw [Function.update_of_ne (rX_ne hk)]

theorem ps_add (cap : ℕ) (a b : Fin 64) (hab : a ≠ b) (ha : a ≠ 7) (hb : b ≠ 7) {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (x y : ℕ) (hx : f a = x) (hy : f b = y) (h7 : f 7 = 0) (hcap : x + y ≤ cap) :
    Runs cap (addR (rX b) (rX a) (rX 7)) σ (18 * y + 3) (PS σ0 X Sx L rest i (Function.update f a (x + y))) := by
  have e := addR_spec cap (A := rX b) (B := rX a) (T := rX 7) (rX_ne (Ne.symm hab)) (rX_ne hb) (rX_ne ha) σ
    (by rw [h.x, h7]) (by rw [h.x, h.x]; omega)
  rw [h.x, h.x, hx, hy] at e
  exact ⟨_, e, ps_reg h a _ rfl⟩

theorem ps_inc (cap : ℕ) (j : Fin 64) {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (x : ℕ) (hx : f j = x) (hcap : x < cap) :
    Runs cap (WMX.inc (rX j)) σ 3 (PS σ0 X Sx L rest i (Function.update f j (x + 1))) := by
  have e := WXExec.inc cap (rX j) σ (by rw [h.x, hx]; exact hcap)
  rw [h.x, hx] at e
  exact ⟨_, e, ps_reg h j _ rfl⟩

theorem ps_clr (cap : ℕ) (j : Fin 64) {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (x : ℕ) (hx : f j = x) (hcap : x ≤ cap) :
    Runs cap (.wm (WM.clear (rX j))) σ (3 * x + 1) (PS σ0 X Sx L rest i (Function.update f j 0)) := by
  have e := wclear_spec (cap := cap) (rX j) x σ (by rw [h.x, hx]) (by rw [h.x, hx]; exact hcap)
  exact ⟨_, WXExec.wm e, ps_reg h j _ rfl⟩

theorem ps_mul (cap : ℕ) (a a2 b c : Fin 64) (hd : [a, a2, b, c, 7].Nodup) {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (x y z : ℕ) (hx : f a = x) (hy : f b = y) (hz : f c = z)
    (ha2 : f a2 = 0) (h7 : f 7 = 0) (hcap : z + x * y ≤ cap) (hcapA : 2 * x ≤ cap) :
    Runs cap (mulR (rX a) (rX a2) (rX b) (rX c) (rX 7)) σ (x * (18 * y + 3 + 8) + 7 * x + 3)
      (PS σ0 X Sx L rest i (Function.update f c (z + x * y))) := by
  have hR : [rX a, rX a2, rX b, rX c, rX 7].Nodup := by
    have := hd.map rX.injective; simpa using this
  have e := mulR_spec cap hR σ (by rw [h.x, ha2]) (by rw [h.x, h7]) (by rw [h.x, h.x, h.x, hx, hy, hz]; exact hcap)
    (by rw [h.x, hx]; exact hcapA)
  rw [h.x, h.x, h.x, hx, hy, hz] at e
  exact ⟨_, e, ps_reg h c _ rfl⟩

theorem PS.congr {i : ℕ} {f g : Fin 64 → ℕ} {σ : WSt} (h : PS σ0 X Sx L rest i f σ) (hfg : ∀ j, f j = g j) :
    PS σ0 X Sx L rest i g σ := ⟨h.pos, fun j => (h.x j).trans (hfg j), h.fr⟩

theorem PS.idx {i i' : ℕ} {f : Fin 64 → ℕ} {σ : WSt} (h : PS σ0 X Sx L rest i f σ) (e : i = i') :
    PS σ0 X Sx L rest i' f σ := e ▸ h

theorem ps_dec (cap : ℕ) (j : Fin 64) {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (x : ℕ) (hx : f j = x) (hcap : x ≤ cap) :
    Runs cap (WMX.dec (rX j)) σ 1 (PS σ0 X Sx L rest i (Function.update f j (x - 1))) := by
  have e := WXExec.dec cap (rX j) σ (by rw [h.x, hx]; exact hcap)
  rw [h.x, hx] at e
  exact ⟨_, e, ps_reg h j _ rfl⟩

end Steps

end NearCubicGates.Close.Expand.PolyTab
