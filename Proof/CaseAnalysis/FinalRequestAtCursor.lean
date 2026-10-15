import Proof.PCP.PCPPQueryIndexPadding
import Proof.CaseAnalysis.RowsEstimatorParityCounter
import Proof.MachineModel.Layout

/-! A short physical request segment for the existing same-source PCPP cache.
Advance its already allocated unary address, preserving all other cache tapes,
then apply the actual cached clause reader. No PCPP request word or fresh source
call is supplied to the hot path. Cache construction and admission remain in
the existing cold source pipeline and must be connected by the enclosing pre.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RequestAtCursor

open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The legacy and constructed accessor request codecs are different at
every payload; an extra inner frame cannot be removed by a value equality. -/
theorem query_frame_mismatch (payload index : List Bool) :
    frame (payload ++ index) ≠ frame (frame payload ++ index) := by
  intro h
  have hlen := congrArg List.length h
  simp only [frame_length, List.length_append] at hlen
  omega

def indexSlot : Fin 1 → Fin 19 := fun _ => 14
noncomputable def advance := RecoveryFocus.machine indexSlot CloseoutRowsEstimatorParity.Counter.machine

/-- The already selected cache capacity covers the next unary address. -/
theorem next_index_fits (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (i : Fin (2 ^ (a.output rq).clauseBits)) :
    i.val + 3 ≤ PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) := by
  have hc := PCPPQueryCachedBounds.clause_capacity a rq i
  have hlen : ((PCPPQueryClause.clausePairs rq (a.output rq)).take i.val).length = i.val := by
    rw [List.length_take]
    simp only [PCPPQueryClause.clausePairs, List.length_ofFn]
    exact min_eq_left (Nat.le_of_lt i.isLt)
  unfold PCPPQueryClause.queryBudget PCPPQueryClause.budget PCPPQueryClauseLookup.budget
    PCPPQueryClauseRows.budget at hc
  rw [hlen] at hc
  omega

/-- A paid one-tape address increment on the literal 19-tape cache state. -/
theorem advance_step (source : List Bool) (arity index C : ℕ) (hC : index + 3 ≤ C) :
    Step advance (2 * index + 2) PCPPQueryClauseReuse.heads
      (PCPPQueryIndexPadding.clauseData source arity index C [])
      PCPPQueryClauseReuse.heads
      (PCPPQueryIndexPadding.clauseData source arity (index + 1) C []) := by
  have hinj : Function.Injective indexSlot := fun a b _ => Subsingleton.elim a b
  have hhead : ∀ j, PCPPQueryClauseReuse.heads (indexSlot j) = (1 : ℕ) := by
    intro j
    simp [indexSlot, PCPPQueryClauseReuse.heads]
  have hinput : PCPPQueryIndexPadding.clauseData source arity index C [] 14
      = ZeroPadding.pad C (CompareMachine.word index) := by
    simp only [PCPPQueryIndexPadding.clauseData]
    exact (pad_template C index (by omega)).symm
  have houtput : PCPPQueryIndexPadding.clauseData source arity (index + 1) C [] 14
      = ZeroPadding.pad C (CompareMachine.word (index + 1)) := by
    simp only [PCPPQueryIndexPadding.clauseData]
    exact (pad_template C (index + 1) (by omega)).symm
  have hp := (CloseoutRowsEstimatorParity.Counter.increment_run index).pad (fun _ => C)
  have hdock := hp.dock indexSlot hinj PCPPQueryClauseReuse.heads
    (PCPPQueryIndexPadding.clauseData source arity index C []) hhead (fun _ => hinput)
  have ht : install indexSlot (PCPPQueryIndexPadding.clauseData source arity index C [])
      (fun _ : Fin 1 => ZeroPadding.pad C (CompareMachine.word (index + 1)))
      = PCPPQueryIndexPadding.clauseData source arity (index + 1) C [] := by
    funext i
    by_cases hi : i = 14
    · subst i
      change install indexSlot _ _ (indexSlot 0) = _
      rw [install_slot indexSlot hinj]
      exact houtput.symm
    · rw [install_other indexSlot _ _ i (by intro j; exact Ne.symm hi)]
      fin_cases i <;> simp [PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data] at hi ⊢
  rw [ht, dockH_existing indexSlot _ _ hhead] at hdock
  exact hdock

/-- Immediate consumer check: the incremented actual state enters the existing
cached clause reader at the next address, with the same source and capacity. -/
theorem advance_then_clause (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (i : Fin (2 ^ (a.output rq).clauseBits)) (hnext : i.val + 1 < 2 ^ (a.output rq).clauseBits) :
    let C := PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)
    let j : Fin (2 ^ (a.output rq).clauseBits) := ⟨i.val + 1, hnext⟩
    Step (Composition.machine advance PCPPQueryClauseReuse.machine)
      ((2 * i.val + 2) + 1 + PCPPQueryCachedBounds.callBudget a (rq.circuit.size + rq.arity))
      PCPPQueryClauseReuse.heads
      (PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity i.val C [])
      PCPPQueryClauseReuse.heads
      (PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity j.val C
        (natListWord [literalIndex ((a.output rq).clauses j).left,
          literalIndex ((a.output rq).clauses j).right])) := by
  dsimp only
  obtain ⟨rc, hr, ht, hh, hs⟩ := PCPPQueryIndexPadding.clause_run a rq ⟨i.val + 1, hnext⟩
  rw [PCPPQueryIndexPadding.clause_entry] at hr
  exact (advance_step _ _ _ _ (next_index_fits a rq i)).seq ⟨rc, hr, hh, ht, hs⟩

end NearCubicWires.RepairOrdinary.CloseoutFinalC10RequestAtCursor
