import Proof.SourceAssembly.SourceBundle
import Proof.CaseAnalysis.RowsOriginalSource

/- Read the actual queried literal pair, retaining its clause cursor and native cache.
The extra parser templates remain explicit paid-preprocessing inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyLiteralRefs
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
open CloseoutRowsOriginalClause
noncomputable section

def extra (C : Nat) : Fin 72→List Bool :=
  Fin.addCases (m:=27) (n:=45) (CloseoutRowsOriginalClause.extra C) (CloseoutRowsOriginalClassify.extra C)
def bank (C : Nat) (cache : Fin 19→List Bool) : Fin 91→List Bool := Fin.addCases (m:=19) (n:=72) (motive:=fun _=>List Bool) cache (extra C)
theorem bank_eq (C : Nat) (cache : Fin 19→List Bool) : bank C cache=
    CloseoutRowsOriginalClassify.data C (CloseoutRowsOriginalClause.data C cache) := by
  funext i;fin_cases i <;>rfl

def heads := CloseoutRowsOriginalClassify.heads
def bump := DecompositionCountPosition.move (fun i : Fin 91=>if i=13 ∨ i=14 then .right else .stay)
def clear := TapeEmbedding.machine 72 PCPPQueryClauseReuse.clearResult
def machine := Composition.machine bump (Composition.machine clear CloseoutRowsOriginalSource.machine)
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) :=
  bank C (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
    (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
    (natListWord [literalIndex ((a.output r).clauses ci).left,literalIndex ((a.output r).clauses ci).right]))
def sourceCost (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) :=
  let p:=(a.output r).clauses ci
  PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+1+
    CloseoutRowsOriginalPair.cleanBudget (index p.left) (index p.right) C (negative p.left) (negative p.right)+1+
    (CloseoutCaseTwo.Metadata.budget r (a.output r)+1+
      CloseoutCaseTwo.VariablePrep.budget (index p.left) (a.output r).systematicBits+1+
      CloseoutCaseTwo.VariablePrep.budget (index p.right) (a.output r).systematicBits)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) :=
  1+1+(2*PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)+4+1+sourceCost a r ci C)

theorem bump_run (A : Fin 91→List Bool) : Step bump 1 (fun _=>0) A heads A := by
  obtain ⟨s,hs,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 91=>if i=13 ∨ i=14 then .right else .stay) (fun _=>0) A
  apply Step.of_run hs
  · rw [hf];funext i;fin_cases i <;>rfl
  · rw [hf]

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C) :
    ∃ A,Step machine (budget a r ci C) (fun _=>0) (input a r ci C) heads A ∧
      (∀ j : Fin 19,A (j.castAdd 72)=PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r))
        r.arity ci.val (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (natListWord [literalIndex ((a.output r).clauses ci).left,literalIndex ((a.output r).clauses ci).right]) j) ∧
      A 83=ZeroPadding.pad C (UnaryTemplate.tape (index ((a.output r).clauses ci).left)) ∧
      A 85=ZeroPadding.pad C [decide ((a.output r).systematicBits ≤ index ((a.output r).clauses ci).left)] ∧
      A 87=ZeroPadding.pad C (UnaryTemplate.tape (index ((a.output r).clauses ci).right)) ∧
      A 89=ZeroPadding.pad C [decide ((a.output r).systematicBits ≤ index ((a.output r).clauses ci).right)] := by
  let Q:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
  let p:=(a.output r).clauses ci
  let pair:=natListWord [literalIndex p.left,literalIndex p.right]
  have fit : pair.length ≤ Q := by
    obtain ⟨rr,_run,_steps,_source,_arity,_idx,result,_heads,bounded⟩:=
      PCPPQueryClauseReset.lookup_run r (a.output r) ci Q (PCPPQueryCachedBounds.clause_capacity a r ci)
    have hb:=bounded 15 (Or.inr (Or.inl rfl))
    rw [result,ZeroPadding.pad_length] at hb
    exact (le_max_right _ _).trans hb
  obtain ⟨c,cr,ch,ct,_⟩:=PCPPQueryIndexPadding.clause_clear
    (pcppOutput r (a.output r)) r.arity ci.val Q pair fit
  have clearRun:Step clear (2*Q+4) heads (input a r ci C) heads
      (bank C (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val Q [])) := by
    have h:=(Step.of_run cr ch ct).embed (fun _ : Fin 72=>0) (extra C)
    exact (h.congr_in (by funext i;fin_cases i <;>rfl) rfl).congr (by funext i;fin_cases i <;>rfl) rfl
  obtain ⟨A,hr,cache,_left,_lsign,_right,_rsign,_sys,li,la,ri,ra,_driver⟩:=
    CloseoutRowsOriginalSource.run a r ci C hc
  rw [←bank_eq] at hr
  exact ⟨A,(bump_run _).seq (clearRun.seq hr),cache,li,la,ri,ra⟩

end
end SourceAssemblyLiteralRefs
