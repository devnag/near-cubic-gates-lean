import Proof.PCP.PCPPQueryCachedBounds

/-! Same-cache support and clause reads at one source-derived capacity.
The native emitter supplies arity and size; physical capacity production is
composed separately and is charged once before the repeated row loop. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryCachedBounds
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem support_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (a.output r).systematicBits) :
    let C := capacity a (r.circuit.size+r.arity)
    ∃ receipt,runFrom PCPPQuerySupportReuse.machine (callBudget a (r.circuit.size+r.arity))
      (PCPPQuerySupportReuse.entry (pcppOutput r (a.output r)) r.arity i.val C)=some receipt ∧
      receipt.final.tapes=PCPPQuerySupportReuse.data (pcppOutput r (a.output r)) r.arity i.val C
        (PCPPQuerySupport.mask r (a.output r) i) ∧
      receipt.final.heads=PCPPQuerySupportReuse.heads ∧
      receipt.steps≤callBudget a (r.circuit.size+r.arity) := by
  dsimp only
  let C := capacity a (r.circuit.size+r.arity)
  have hc := support_capacity a r i
  obtain ⟨out,hr,ht,hh,hs⟩ := PCPPQuerySupportReuse.lookup_run r (a.output r) i C hc
  have hb : 2*PCPPQuerySupportReset.cost r (a.output r) i+2*C+7≤
      callBudget a (r.circuit.size+r.arity) := by unfold callBudget; dsimp [C] at *; omega
  have hm := runFrom_moreFuel PCPPQuerySupportReuse.machine _
    (callBudget a (r.circuit.size+r.arity)-(2*PCPPQuerySupportReset.cost r (a.output r) i+2*C+7)) _ out hr
  simp only [PCPPQuerySupportReuse.budget] at hm
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨out,hm,ht,hh,hs.le.trans hb⟩

theorem clause_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) :
    let C := capacity a (r.circuit.size+r.arity)
    ∃ receipt,runFrom PCPPQueryClauseReuse.machine (callBudget a (r.circuit.size+r.arity))
      (PCPPQueryClauseReuse.entry (pcppOutput r (a.output r)) r.arity i.val C)=some receipt ∧
      receipt.final.tapes=PCPPQueryClauseReuse.data (pcppOutput r (a.output r)) r.arity i.val C
        (natListWord [literalIndex ((a.output r).clauses i).left,literalIndex ((a.output r).clauses i).right]) ∧
      receipt.final.heads=PCPPQueryClauseReuse.heads ∧
      receipt.steps≤callBudget a (r.circuit.size+r.arity) := by
  dsimp only
  let C := capacity a (r.circuit.size+r.arity)
  have hc := clause_capacity a r i
  obtain ⟨out,hr,ht,hh,hs⟩ := PCPPQueryClauseReuse.lookup_run r (a.output r) i C hc
  have hb : PCPPQueryClauseReuse.budget r (a.output r) i C≤
      callBudget a (r.circuit.size+r.arity) := by
    unfold callBudget PCPPQueryClauseReuse.budget
    dsimp [C] at *
    omega
  have hm := runFrom_moreFuel PCPPQueryClauseReuse.machine _
    (callBudget a (r.circuit.size+r.arity)-PCPPQueryClauseReuse.budget r (a.output r) i C) _ out hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨out,hm,ht,hh,hs.trans hb⟩

end NearCubicWires.RepairOrdinary.PCPPQueryCachedBounds
