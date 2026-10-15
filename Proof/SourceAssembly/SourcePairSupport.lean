import Proof.SourceAssembly.SourceLiteralGuard

/- The actual queried clause produces both systematic-support bitmaps using one
fixed program. Auxiliary references are guarded; repeated references and empty
systematic supports are included. The original clause cache stays retained. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyPairSupport
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
open CloseoutRowsOriginalClause (index negative)
open SourceAssemblyLiteralSupport
noncomputable section
attribute [local irreducible] PCPPQuerySupportReuse.machine

theorem projections (side : Bool) (source pair : List Bool) (q ci Q k C : Nat)
    (A : Fin 91→List Bool)
    (cache : ∀ j : Fin 19,A (j.castAdd 72)=PCPPQueryIndexPadding.clauseData source q ci Q pair j)
    (index : A (refPort side)=ZeroPadding.pad C (UnaryTemplate.tape k)) :
    ∀ i,A (slots side i)=words source q k Q C [] i := by
  intro i;fin_cases i
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 0
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 1
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 2
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 13
  · cases side
    · simpa [slots,outPort,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
        PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data,ZeroPadding.pad] using cache 3
    · simpa [slots,outPort,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
        PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data,ZeroPadding.pad] using cache 4
  · exact index
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 16
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 17
  · simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero,
      PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data] using cache 18

def finish := DecompositionCountPosition.move (fun i : Fin 91=>if i=13 ∨ i=14 then .left else .stay)
def machine := Composition.machine SourceAssemblyLiteralRefs.machine
  (Composition.machine (SourceAssemblyLiteralSupport.machine false)
    (Composition.machine (SourceAssemblyLiteralSupport.machine true) finish))
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) :=
  SourceAssemblyLiteralRefs.budget a r ci C+1+
    (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+6+1+
      (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+6+1+1))

theorem finish_run (A : Fin 91→List Bool) : Step finish 1 H A (fun _=>0) A := by
  obtain ⟨s,hs,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 91=>if i=13 ∨ i=14 then .left else .stay) H A
  apply Step.of_run hs
  · rw [hf];funext i;fin_cases i <;>rfl
  · rw [hf]

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0)
      (SourceAssemblyLiteralRefs.input a r ci C) (fun _=>0) A ∧
      A 3=ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (value a r (index ((a.output r).clauses ci).left)) ∧
      A 4=ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (value a r (index ((a.output r).clauses ci).right)) ∧
      (∀ j : Fin 19,j≠3→j≠4→A (j.castAdd 72)=PCPPQueryIndexPadding.clauseData
        (pcppOutput r (a.output r)) r.arity ci.val (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (natListWord [literalIndex ((a.output r).clauses ci).left,literalIndex ((a.output r).clauses ci).right]) j) := by
  obtain ⟨A,first,cache,li,lf,ri,rf⟩:=SourceAssemblyLiteralRefs.run a r ci C hc
  let Q:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
  let p:=(a.output r).clauses ci
  let B:=result false Q (value a r (index p.left)) A
  let D:=result true Q (value a r (index p.right)) B
  have left:=SourceAssemblyLiteralSupport.run false a r (index p.left) C A
    (projections false _ _ _ _ _ _ _ A cache li) lf
  have rightInput : ∀ i,B (slots true i)=words (pcppOutput r (a.output r)) r.arity (index p.right) Q C [] i := by
    intro i
    have ne : slots true i≠outPort false := by fin_cases i <;>decide
    simpa only [B,result,ne,if_false] using projections true _ _ _ _ _ _ _ A cache ri i
  have rightFlag : B (flagPort true)=ZeroPadding.pad C [decide ((a.output r).systematicBits ≤ index p.right)] := rf
  have right:=SourceAssemblyLiteralSupport.run true a r (index p.right) C B rightInput rightFlag
  refine ⟨D,first.seq (left.seq (right.seq (finish_run D))),?_,?_,?_⟩
  · simp [D,B,result,outPort]
    rfl
  · simp [D,result,outPort]
    rfl
  · intro j h3 h4
    have ne3 : j.castAdd 72≠outPort false := by intro he;apply h3;apply Fin.ext;exact congrArg (fun i : Fin 91=>i.val) he
    have ne4 : j.castAdd 72≠outPort true := by intro he;apply h4;apply Fin.ext;exact congrArg (fun i : Fin 91=>i.val) he
    simpa only [D,B,result,ne3,ne4,if_false] using cache j

end
end SourceAssemblyPairSupport
