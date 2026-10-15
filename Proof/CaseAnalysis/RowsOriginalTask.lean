import Proof.CaseAnalysis.RowsOriginalBranches

/-! The finite source-test schedule uses six penalty slots, one left
second-moment slot, and three signed-clause slots. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTask
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsOriginalTemplates CloseoutRowsOriginalBranches
open CloseoutRowsOriginalMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

inductive Task where
  | penalty (side : Fin 2) (slot : Fin 3)
  | moment
  | clause (slot : Fin 3)

def row : Task→(Fin 4→Bool)→Row
  | .penalty side j,bits=>penaltySlot (bits (Fin.natAdd 2 side)) side j
  | .moment,_=>plain 1 [0,0]
  | .clause j,bits=>clauseSlot (bits 0) (bits 1) j
noncomputable def program : Task→Σ s,Machine 22 s
  | .penalty side j=>⟨_,CloseoutRowsOriginalBranches.penalty side j⟩
  | .moment=>⟨_,body (plain 1 [0,0])⟩
  | .clause j=>⟨_,CloseoutRowsOriginalBranches.clause j⟩
noncomputable def machine (t : Task):=(program t).2

theorem legal (t : Task) (bits : Fin 4→Bool) : Legal (row t bits) := by
  cases t with
  | penalty side j=>exact penalty_slot_legal _ side j
  | clause j=>exact clause_slot_legal _ _ j
  | moment=>simp [row,Legal,plain,CloseoutRowsScalarFits.RationalBound]

theorem run (t : Task) (cs : List (List (List ℕ))) (indices : Fin 2→ℕ) (bits : Fin 4→Bool)
    (B W : ℕ) (hB : 1≤B) (count : ∀ p∈cs,p.length≤B) (width : ∀ p∈cs,(ExtIncidence.stream p).length≤W)
    (hi : ∀ side,indices side<cs.length) :
    Step (machine t) (cost cs B W+4) (fun _=>0) (input (rowC cs B W) cs indices bits)
      (outHeads (row t bits) indices) (output (row t bits) (rowC cs B W) cs indices hi bits) := by
  cases t with
  | penalty side j=>
    exact (penalty_run side j _ cs indices bits B W hB count width hi rfl).enlarge (by omega)
  | moment=>exact (body_run (plain 1 [0,0]) cs indices bits B W hB count width hi (by decide)).enlarge (by omega)
  | clause j=>exact clause_run j _ _ cs indices bits B W hB count width hi rfl rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTask
