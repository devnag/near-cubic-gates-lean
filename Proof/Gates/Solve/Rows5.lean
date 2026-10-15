import Proof.Gates.Solve.Rows4

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
open NearCubicGates.Close.Interfaces.Formats (inClass)
open NearCubicWires.RepairRepresentation (natWord)

/-- The entry records of a row, points `j' < j`. -/
def entVals (q : ℕ) (σl : List ℕ) (pts : List (List ℤ)) (j : ℕ) : List ℕ :=
  (List.range j).map fun j' => encS (if inClass q σl (pts.getD j' []) then 1 else 0)

/-- The entry-loop invariant after `j` points. -/
def CellsInv (σB : MS) (W ℓ q : ℕ) (σl : List ℕ) (pts : List (List ℤ)) (out L0 : List Bool) (keep : Str → ℕ)
    (j : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ OutOn σ1 sMAT rCM (out ++ recBits W (entVals q σl pts j)) L0 ∧ σ1.val rPB = j * ℓ ∧
    (∀ r ∈ cellRegs, σ1.val r = 0) ∧ SameExcept σB σ1 [sMAT] (rCM :: rPB :: rLP2 :: cellRegs) ∧
    ∀ X ∈ keepW, v1 X = keep X

theorem cells_step (cap : ℕ) {σB : MS} {W ℓ : ℕ} {pts : List (List ℤ)} {σl : List ℕ} {jS jP : List Bool}
    (hc : CellCtx σB W ℓ pts σl jS jP) {q : ℕ} (hNZQ : σB.val rNZQ = (decide (q ≠ 0)).toNat) (keep : Str → ℕ)
    (hkq : keep wQ = q) (hkT : keep wTWO = 2) (hσl : σl.length ≤ ℓ) (hσb : ∀ x ∈ σl, x < 2 ^ ℓ)
    (hub : ∀ u ∈ pts, ∀ z ∈ u, z.natAbs < 2 ^ ℓ) (hq : q < 2 ^ ℓ) (hℓW : ℓ + 2 ≤ W)
    (hSLN : σB.val rSLN = σl.length) (hLL : σB.val rLL = ℓ) {out L0 : List Bool}
    (hcap : capC (pts.length * ℓ + ℓ) W ≤ cap) (hcapO : out.length + (pts.length + 1) * (2 * (W + 1) + 1) + 2 ≤ cap)
    (j : ℕ) (hj : j < pts.length) (τ : MS) (hI : CellsInv σB W ℓ q σl pts out L0 keep j τ) :
    Runs cap cellP (τ.setv rLP2 (pts.length - j - 1)) (cellCost ℓ (ucost W (pts.length * ℓ + ℓ)))
      (fun ρ => CellsInv σB W ℓ q σl pts out L0 keep (j + 1) ρ ∧ ρ.val rLP2 = pts.length - j - 1) := by
  obtain ⟨σ1, v1, h1, hout1, hPB1, hz1, hfr1, hkeep1⟩ := hI
  have h1' := h1.setv (r := rLP2) (by decide) (pts.length - j - 1)
  set σ2 := σ1.setv rLP2 (pts.length - j - 1) with hσ2
  have hfr2 : SameExcept σB σ2 [sMAT] (rCM :: rPB :: rLP2 :: cellRegs) :=
    SameExcept.trans hfr1 (sameExcept_setv σ1 (by simp) _)
  have hc2 : CellCtx σ2 W ℓ pts σl jS jP :=
    ⟨by rw [hfr2.st (by decide), hc.sg], by rw [hfr2.sh (by decide), hc.sgh], by rw [hfr2.st (by decide), hc.pt],
      by rw [hfr2.sh (by decide), hc.pth]⟩
  have hlen : (out ++ recBits W (entVals q σl pts j)).length + 2 * (W + 1) + 2 ≤ cap := by
    rw [List.length_append, recBits_length]; simp only [entVals, List.length_map, List.length_range]
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show j + 1 ≤ pts.length + 1 by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  have hce := cell_spec cap h1' hc2 hj (by rw [hfr2.val (by decide), hNZQ]) (by rw [hkeep1 wQ (by decide), hkq])
    (by rw [hkeep1 wTWO (by decide), hkT]) hσl hσb (hub _ (List.getElem_mem hj)) hq hℓW
    (fun r hr => by
      have : r ≠ rLP2 := by
        simp only [cellRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp [hσ2, Function.update_of_ne this, hz1 r hr])
    (by simp (config := {decide := true}) [hσ2, hPB1]) (by rw [hfr2.val (by decide), hSLN])
    (by rw [hfr2.val (by decide), hLL])
    (OutOn.same hout1 (sameExcept_setv σ1 (S := []) (Rg := [rLP2]) (by simp) _) (by simp) (by decide)) hcap hlen
  refine hce.post (fun ρ ⟨σ3, v3, h3, hout3, hPB3, hz3, hfr3, hkeep3⟩ =>
    ⟨⟨σ3, v3, h3, ?_, hPB3, hz3, ?_, fun X hX => by rw [hkeep3 X hX, hkeep1 X hX]⟩, ?_⟩)
  · have e : entVals q σl pts (j + 1) = entVals q σl pts j ++
        [encS (if inClass q σl pts[j] then 1 else 0)] := by
      simp [entVals, List.range_succ, List.getElem?_eq_getElem hj]
    rw [e, recBits_append, ← List.append_assoc]
    simpa [recBits] using hout3
  · exact SameExcept.trans hfr2 (hfr3.weaken (by simp) (by simp [cellRegs]))
  · rw [h3.val (by decide), hfr3.val (by simp only [cellRegs]; decide)]; simp [hσ2]

end NearCubicGates.Close.Solve
