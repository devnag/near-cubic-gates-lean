import Proof.Supplier.EquationRowCuts

/-! The exact typed row-to-matrix cut stream, with the selected one-time
row capacity. Header and cold physical driver production remain upstream. -/
namespace NearCubicWires.RepairOrdinary.EquationRowCuts
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def rowCapacity (r : EquationRow.Input) := 128*(2*r.d+1)*(r.p+1)
def rowWeightCount (r : EquationRow.Input) := 2*r.d-r.odd.toNat

theorem row_weight_count (r : EquationRow.Input) (c : Cut) (hc : c∈r.cuts) :
    (EquationCut.weights c).length=rowWeightCount r := by
  obtain ⟨hl,hr⟩ := r.lengths c hc
  simp only [EquationCut.weights,List.length_append,rowWeightCount]
  omega

theorem request_run (pre suffix out : List Bool) (r : EquationRow.Input) :
    ∃ actual,runFrom machine (budget r.cuts.length (rowCapacity r))
      (cfg 0 (pre++stream r.p r.cuts++suffix) out pre.length (rowCapacity r)
        (rowWeightCount r) r.p r.odd r.cuts.length 1)=some actual ∧
      actual.final=cfg 3 (pre++stream r.p r.cuts++suffix)
        (out++(EquationRow.request r).cuts.flatMap (cutWord (EquationRow.request r).p))
        (pre.length+(stream r.p r.cuts).length) (rowCapacity r)
        (rowWeightCount r) r.p r.odd r.cuts.length 1 ∧
      actual.steps ≤ budget r.cuts.length (rowCapacity r) := by
  have hC : 128*(rowWeightCount r+1)*(r.p+1) ≤ rowCapacity r := by
    unfold rowCapacity rowWeightCount
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sub_le _ _) 1))
  have h := loop_run pre r.cuts suffix out (rowCapacity r) (rowWeightCount r) r.p r.odd
    (row_weight_count r) r.fits hC
  simpa only [output_literal,EquationRow.request] using h

end
end NearCubicWires.RepairOrdinary.EquationRowCuts
