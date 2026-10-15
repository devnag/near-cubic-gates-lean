import Proof.Gates.Solve.Ident3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open StablePartition.Workspace (overlay)
open NearCubicGates.Close.Interfaces.Formats (SysReq)

/-- The cost bound of the identity rows. -/
def identCost (n W : ℕ) : ℕ := (n + 2) * (idRowCost n W + 4) + 100 * (n + 2)

theorem ident_spec (cap : ℕ) {σ0 σ : MS} {W n : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (hvZ : v wZ = 0) (hvT : v wTWO = 2)
    (hNN : σ0.val rNN = n) (hz : ∀ r ∈ [rLV2, rBEF, rAFT, rK3], σ0.val r = 0) {out L0 : List Bool}
    (hout : OutOn σ0 sMAT rCM out L0) (hcap : out.length + (n + 1) * (n + 3) * (2 * (W + 1) + 1) + 4 * n + 8 ≤ cap) :
    Runs cap identP σ (identCost n W) (fun τ => ∃ σ1, At σ1 τ W v ∧
      OutOn σ1 sMAT rCM (out ++ recBits W ((List.range n).flatMap (idRow n))) L0 ∧
      (∀ r ∈ [rLV2, rBEF, rAFT, rK3], σ1.val r = 0) ∧ SameExcept σ0 σ1 [sMAT] [rCM, rLV2, rBEF, rAFT, rK3]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨hLV2, hBEF, hAFT, hK3⟩ := hz
  have hcost : 18 * n + 3 + 1 + (18 * n + 3 + 1 + ((n * (idRowCost n W + 4) + 1) + 1 + (3 * n + 1))) ≤ identCost n W := by
    unfold identCost
    have e : (n + 2) * (idRowCost n W + 4) = n * (idRowCost n W + 4) + 2 * (idRowCost n W + 4) := by ring
    omega
  refine Runs.cost ?_ hcost
  refine Runs.seq ((opAddR cap h (A := rNN) (B := rLV2) (by decide) (by decide) (by decide)
    (by rw [hLV2, hNN]; omega)).cost (show 18 * σ0.val rNN + 3 ≤ 18 * n + 3 by rw [hNN])) (fun τ1 h1 => ?_)
  set σ1 := σ0.setv rLV2 (σ0.val rLV2 + σ0.val rNN) with hσ1
  refine Runs.seq ((opAddR cap h1 (A := rNN) (B := rAFT) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ1, hAFT, hNN]; omega)).cost
    (show 18 * σ1.val rNN + 3 ≤ 18 * n + 3 by simp (config := {decide := true}) [hσ1, hNN])) (fun τ2 h2 => ?_)
  set σ2 := σ1.setv rAFT (σ1.val rAFT + σ1.val rNN) with hσ2
  have hI0 : IInv σ2 W n v out L0 0 τ2 := by
    refine ⟨σ2, h2, ?_, by simp (config := {decide := true}) [hσ2, hσ1, hBEF],
      by simp (config := {decide := true}) [hσ2, hσ1, hAFT, hNN], by simp (config := {decide := true}) [hσ2, hσ1, hK3],
      SameExcept.refl _ _ _⟩
    simpa [recBits] using OutOn.same hout (S := []) (Rg := [rLV2, rAFT])
      (SameExcept.trans (sameExcept_setv σ0 (by simp) _) (sameExcept_setv _ (by simp) _)) (by simp) (by decide)
  have hloop := Runs.count (cap := cap) (K := rLV2) (body := identRow) (idRowCost n W) n (IInv σ2 W n v out L0)
    (by omega) (fun k hk τ hτ _ => ident_step cap hvZ hvT hcap k hk τ hτ) τ2 hI0
    (by rw [h2.val (by decide)]; simp (config := {decide := true}) [hσ2, hσ1, hLV2, hNN])
  refine Runs.seq hloop (fun τ3 ⟨⟨σ3, h3, hout3, hBEF3, hAFT3, hK33, hfr3⟩, hK3'⟩ => ?_)
  refine ((opClearR cap h3 (r := rBEF) (by decide) (by rw [hBEF3]; omega)).cost (by rw [hBEF3])).post
    (fun τ4 h4 => ⟨_, h4, ⟨by simpa using hout3.1, by simpa using hout3.2.1, by
      simp (config := {decide := true}); rw [hout3.2.2, List.length_append]⟩, ?_, ?_⟩)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp (config := {decide := true}); rw [← h3.val (by decide)]; exact hK3'
    · simp
    · simp (config := {decide := true}); rw [hAFT3]; simp
    · simp (config := {decide := true}); exact hK33
  · exact SameExcept.trans (sameExcept_setv σ0 (by simp) _) (SameExcept.trans (sameExcept_setv _ (by simp) _)
      (SameExcept.trans (hfr3.weaken (by simp) (by simp)) (sameExcept_setv _ (by simp) _)))

end NearCubicGates.Close.Solve
