import Proof.CaseAnalysis.RowsOriginalClassify

/-! An actual cached clause request yields all runtime template flags and
original coordinates from that same source, with the original cache retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSource
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation SourceInterfaces CloseoutRowsOriginalClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine (TapeEmbedding.machine 45 CloseoutRowsOriginalClause.machine)
  CloseoutRowsOriginalClassify.machine

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) (C : ℕ)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses i).left)
      (index ((a.output r).clauses i).right) (negative ((a.output r).clauses i).left)
      (negative ((a.output r).clauses i).right)+1≤C) :
    let Q:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
    let p:=((a.output r).clauses i)
    let S:=(a.output r).systematicBits
    let A:=PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity i.val Q
      (natListWord [literalIndex p.left,literalIndex p.right])
    ∃ out,Step machine (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+1+
      CloseoutRowsOriginalPair.cleanBudget (index p.left) (index p.right) C (negative p.left) (negative p.right)+1+
      (CloseoutCaseTwo.Metadata.budget r (a.output r)+1+
        CloseoutCaseTwo.VariablePrep.budget (index p.left) S+1+CloseoutCaseTwo.VariablePrep.budget (index p.right) S))
      CloseoutRowsOriginalClassify.heads
      (CloseoutRowsOriginalClassify.data C (CloseoutRowsOriginalClause.data C
        (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity i.val Q [])))
      CloseoutRowsOriginalClassify.heads out ∧
      (∀ j : Fin 19,out (j.castAdd 72)=A j) ∧
      out 29=ZeroPadding.pad C (List.replicate (index p.left) true) ∧ out 30=ZeroPadding.pad C [negative p.left] ∧
      out 41=ZeroPadding.pad C (List.replicate (index p.right) true) ∧ out 42=ZeroPadding.pad C [negative p.right] ∧
      out 55=UnaryTemplate.tape S ∧ out 83=ZeroPadding.pad C (UnaryTemplate.tape (index p.left)) ∧
      out 85=ZeroPadding.pad C [decide (S ≤ index p.left)] ∧
      out 87=ZeroPadding.pad C (UnaryTemplate.tape (index p.right)) ∧ out 89=ZeroPadding.pad C [decide (S ≤ index p.right)] ∧
      out 44=List.replicate C true := by
  dsimp only
  obtain ⟨pair,hpair,cache,left,lsign,right,rsign,driver⟩:=CloseoutRowsOriginalClause.run a r i C hc
  have first:=hpair.embed (fun _ : Fin 45=>0) (CloseoutRowsOriginalClassify.extra C)
  obtain ⟨result,last,keep,sys,li,la,ri,ra⟩:=CloseoutRowsOriginalClassify.run r (a.output r) C
    (index ((a.output r).clauses i).left) (index ((a.output r).clauses i).right) pair
    ((cache 0).trans rfl) ((cache 13).trans rfl) left right
  refine ⟨result,first.seq last,?_,(keep 29).trans left,(keep 30).trans lsign,
    (keep 41).trans right,(keep 42).trans rsign,sys,li,la,ri,ra,(keep 44).trans driver⟩
  intro j
  exact (keep (j.castAdd 27)).trans (cache j)

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSource
