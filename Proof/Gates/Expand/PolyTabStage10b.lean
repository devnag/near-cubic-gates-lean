import Proof.Gates.Expand.PolyTabStage10a

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- Registers as a function, streams as in `σ0`. -/
structure RS (σ0 : WSt) (g : Fin NRk → ℕ) (τ : WSt) : Prop where
  v : ∀ q, τ.val q = g q
  s : ∀ x, τ.st x = σ0.st x ∧ τ.sh x = σ0.sh x
  c : τ.cell = σ0.cell

section RSs
variable {σ0 : WState (NSx te qa) NRk}

theorem RS.setv {g : Fin NRk → ℕ} {τ : WSt} (h : RS σ0 g τ) (q : Fin NRk) (y : ℕ) :
    RS σ0 (Function.update g q y) (τ.setv q y) :=
  ⟨fun p => by by_cases e : p = q <;> simp [e, Function.update_apply, h.v], fun x => by simp [h.s x], by simp [h.c]⟩

theorem rs_add (cap : ℕ) {g : Fin NRk → ℕ} {τ : WSt} (h : RS σ0 g τ) (A B T : Fin NRk) (hAB : A ≠ B) (hAT : A ≠ T)
    (hBT : B ≠ T) (hT : g T = 0) (hcap : g B + g A ≤ cap) :
    Runs cap (addR A B T) τ (18 * g A + 3) (RS σ0 (Function.update g B (g B + g A))) := by
  have e := addR_spec cap hAB hAT hBT τ (by rw [h.v]; exact hT) (by rw [h.v, h.v]; exact hcap)
  rw [h.v, h.v] at e
  exact ⟨_, e, h.setv B _⟩

end RSs

theorem RS.congr {σ0 : WSt} {g g' : Fin NRk → ℕ} {τ : WSt} (h : RS σ0 g τ) (e : ∀ q, g q = g' q) : RS σ0 g' τ :=
  ⟨fun q => (h.v q).trans (e q), h.s, h.c⟩

def halfL (c : Fin NRk) : WX :=
  .whr c (.seq (WMX.dec c) (.ifr (rY 107) (WMX.dec (rY 107)) (.seq (WMX.inc (rY 107)) (WMX.inc (rY 105)))))

/-- The loop's register function after `k` steps. -/
def hG (g : Fin NRk → ℕ) (c : Fin NRk) (s k : ℕ) : Fin NRk → ℕ :=
  Function.update (Function.update (Function.update g c (s - k)) (rY 107) (k % 2)) (rY 105) ((k + 1) / 2)

theorem hG_T (g : Fin NRk → ℕ) (c : Fin NRk) (hc1 : c ≠ rY 107) (hc2 : c ≠ rY 105) (s k : ℕ) (hk : k % 2 = 1) :
    ∀ q, Function.update (Function.update (hG g c s k) c (s - k - 1)) (rY 107) (hG g c s k (rY 107) - 1) q =
      hG g c s (k + 1) q := by
  have n75 : rY 107 ≠ rY 105 := by polyTabNe
  intro q
  simp only [hG, Function.update_apply]
  split_ifs <;> simp_all <;> omega

theorem hG_F (g : Fin NRk → ℕ) (c : Fin NRk) (hc1 : c ≠ rY 107) (hc2 : c ≠ rY 105) (s k : ℕ) (hk : k % 2 = 0) :
    ∀ q, Function.update (Function.update (Function.update (hG g c s k) c (s - k - 1)) (rY 107)
      (hG g c s k (rY 107) + 1)) (rY 105) (hG g c s k (rY 105) + 1) q = hG g c s (k + 1) q := by
  have n75 : rY 107 ≠ rY 105 := by polyTabNe
  intro q
  simp only [hG, Function.update_apply]
  split_ifs <;> simp_all <;> omega

theorem halfL_spec (cap : ℕ) {σ0 : WSt} (c : Fin NRk) (hc1 : c ≠ rY 107) (hc2 : c ≠ rY 105) (g : Fin NRk → ℕ)
    (τ : WSt) (h : RS σ0 g τ) (s : ℕ) (hs : g c = s) (h107 : g (rY 107) = 0) (h105 : g (rY 105) = 0)
    (hcap : s + 2 ≤ cap) :
    Runs cap (halfL c) τ (s * (8 + 4) + 1) (RS σ0 (hG g c s s)) := by
  have n75 : rY 107 ≠ rY 105 := by polyTabNe
  have v107 : ∀ k, hG g c s k (rY 107) = k % 2 := fun k => by simp [hG, Function.update_apply, n75]
  have v105 : ∀ k, hG g c s k (rY 105) = (k + 1) / 2 := fun k => by simp [hG]
  obtain ⟨ρ, eρ, hρ, -⟩ := Runs.count (cap := cap) (K := c)
    (body := .ifr (rY 107) (WMX.dec (rY 107)) (.seq (WMX.inc (rY 107)) (WMX.inc (rY 105)))) 8 s
    (fun k ρ => RS σ0 (hG g c s k) ρ) (by omega) (fun k hk μ hμ _ => by
      have m0 := hμ.setv c (s - k - 1)
      have w107 : (μ.setv c (s - k - 1)).val (rY 107) = k % 2 := by
        rw [m0.v, Function.update_of_ne hc1.symm, v107]
      have w105 : (μ.setv c (s - k - 1)).val (rY 105) = (k + 1) / 2 := by
        rw [m0.v, Function.update_of_ne hc2.symm, v105]
      have wc : ∀ ρ : WSt, RS σ0 (hG g c s (k + 1)) ρ → ρ.val c = s - k - 1 := fun ρ hρ => by
        rw [hρ.v]; simp [hG, Function.update_apply, hc1, hc2]; omega
      refine Runs.ifr (fun hT => ?_) (fun hF => ?_)
      · have hk2 : k % 2 = 1 := by rw [w107] at hT; omega
        have e := WXExec.dec cap (rY 107) (μ.setv c (s - k - 1)) (by rw [w107]; omega)
        have m1 := (m0.setv (rY 107) ((μ.setv c (s - k - 1)).val (rY 107) - 1))
        have m2 : RS σ0 (hG g c s (k + 1)) _ := m1.congr (by
          intro q; rw [m0.v, Function.update_of_ne hc1.symm]; exact hG_T g c hc1 hc2 s k hk2 q)
        exact ⟨_, e.mono (by omega), m2, wc _ m2⟩
      · have hk2 : k % 2 = 0 := by rw [w107] at hF; omega
        have e1 := WXExec.inc cap (rY 107) (μ.setv c (s - k - 1)) (by rw [w107]; omega)
        have e2 := WXExec.inc cap (rY 105) ((μ.setv c (s - k - 1)).setv (rY 107) ((μ.setv c (s - k - 1)).val (rY 107) + 1))
          (by rw [WState.setv_val, Function.update_of_ne n75.symm, w105]; omega)
        have m1 := (m0.setv (rY 107) ((μ.setv c (s - k - 1)).val (rY 107) + 1)).setv (rY 105)
          (((μ.setv c (s - k - 1)).setv (rY 107) ((μ.setv c (s - k - 1)).val (rY 107) + 1)).val (rY 105) + 1)
        have a107 : (μ.setv c (s - k - 1)).val (rY 107) + 1 = hG g c s k (rY 107) + 1 := by rw [w107, v107]
        have a105 : ((μ.setv c (s - k - 1)).setv (rY 107) ((μ.setv c (s - k - 1)).val (rY 107) + 1)).val (rY 105) + 1 =
            hG g c s k (rY 105) + 1 := by rw [WState.setv_val, Function.update_of_ne n75.symm, w105, v105]
        have m2 : RS σ0 (hG g c s (k + 1)) _ := m1.congr (by
          intro q
          rw [a105, a107]
          exact hG_F g c hc1 hc2 s k hk2 q)
        exact ⟨_, (WXExec.seq e1 e2).mono (by omega), m2, wc _ m2⟩)
    τ (h.congr fun q => by
      simp only [hG, Function.update_apply, Nat.sub_zero, Nat.zero_mod, Nat.zero_add, Nat.reduceDiv]
      split_ifs <;> simp_all) (by rw [h.v, hs])
  exact ⟨ρ, eρ, hρ⟩

end NearCubicGates.Close.Expand.PolyTab
