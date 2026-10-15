import Proof.Hierarchy.CompetitorResidueCell
import Proof.Hierarchy.CompetitorPlaneClear

/-! The residue cell on actually erased, reusable storage. Padding is only
local; the global result tape keeps its exact streaming representation. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (w : ℕ) := CompetitorReusableDecision.capacity w
def padding (w : ℕ) : Fin 9 → ℕ := fun i => if i=4 ∨ i=8 then 0 else capacity w
def paddedInput (w q a b : ℕ) (pre : List Bool) : Fin 9 → List Bool :=
  fun i => ZeroPadding.pad (padding w i) (CompetitorResidueCell.input w q a b pre i)

theorem padded_cell_run (w q a b : ℕ) (pre : List Bool)
    (ha : a<2^w) (hb : b<2^w) (hq : q≤w) :
    ∃ r out,runFrom CompetitorResidueCell.machine (CompetitorResidueCell.budget w q)
        (RecoveryCalls.restarted CompetitorResidueCell.machine (CompetitorResidueCell.heads pre)
          (paddedInput w q a b pre))=some r ∧
      r.steps≤CompetitorResidueCell.budget w q ∧
      r.final.heads=CompetitorResidueCell.heads
        (pre++binary q (CompetitorSignedResidue.residue w q a b)) ∧
      r.final.tapes=out ∧ out 8=pre++binary q (CompetitorSignedResidue.residue w q a b) ∧
      out 4=List.replicate q true ∧
      (∀ i : Fin 8,(out i.castSucc).length≤capacity w) := by
  obtain ⟨base,out,hr,hs,hh,ht,h8,_,_,h4,hbound⟩ :=
    CompetitorResidueCell.residue_cell_run w q a b pre ha hb hq
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ :=
    ZeroPadding.run_config CompetitorResidueCell.machine (padding w) _ _ base hr
  have hin : ZeroPadding.config (padding w)
      (RecoveryCalls.restarted CompetitorResidueCell.machine (CompetitorResidueCell.heads pre)
        (CompetitorResidueCell.input w q a b pre))=
      RecoveryCalls.restarted CompetitorResidueCell.machine (CompetitorResidueCell.heads pre)
        (paddedInput w q a b pre) := rfl
  rw [hin] at hrun
  refine ⟨r,(fun i => ZeroPadding.pad (padding w i) (out i)),hrun,hsteps.trans_le hs,?_,?_,?_,?_,?_⟩
  · rw [hfinal]
    exact hh
  · rw [hfinal]
    simp only [ZeroPadding.config,ht]
  · simp [padding,h8]
  · simp [padding,h4]
  · intro i
    rw [ZeroPadding.pad_length]
    apply max_le
    · unfold padding
      split_ifs <;> omega
    · exact (hbound i).trans (by unfold capacity CompetitorReusableDecision.capacity; nlinarith)

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
