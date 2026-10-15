import Proof.CaseAnalysis.CaseTwoLiteralIndices
import Proof.PCP.PCPPQueryCachedReaders

/-! The actual cached clause call, original literal decoding, and paid result
clear. Its unsigned variable index is retained while the same source cache is
restored for the systematic branch's support read. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ClauseVariable
open LocalBitMultitape RepairRepresentation SourceInterfaces RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def querySlots (i : Fin 19) : Fin 59:=i.castAdd 40
def literalSlots (i : Fin 41) : Fin 59:=if i=0 then 15 else ⟨i.val+18,by omega⟩
def query:=RecoveryFocus.machine querySlots PCPPQueryClauseReuse.machine
def literals:=RecoveryFocus.machine literalSlots LiteralIndices.machine
def clear:=RecoveryFocus.machine querySlots PCPPQueryClauseReuse.clearResult
def machine:=Composition.machine (Composition.machine query literals) clear
def heads : Fin 59→ℕ:=Fin.addCases (m:=19) (n:=40) PCPPQueryClauseReuse.heads (fun _=>0)
def extra (position : Bool) (i : Fin 40) : List Bool:=if i=37 then [position] else []
def data (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (index : ℕ) (position : Bool) : Fin 59→List Bool:=
  Fin.addCases (m:=19) (n:=40)
    (PCPPQueryClauseReuse.data (pcppOutput r (a.output r)) r.arity index
      (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) []) (extra position)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (index : Fin (2^(a.output r).clauseBits)) (position : Bool):=
  PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+1+
    LiteralIndices.budget ((a.output r).clauses index).left ((a.output r).clauses index).right position+1+
    (2*PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)+4)
theorem query_injective : Function.Injective querySlots:=by
  intro i j he;apply Fin.ext;exact congrArg (fun x : Fin 59=>x.val) he
theorem literal_injective : Function.Injective literalSlots:=by
  intro i j he
  have hv:=congrArg Fin.val he
  by_cases hi : i=0 <;>by_cases hj : j=0
  · exact hi.trans hj.symm
  · simp only [literalSlots,hi,hj,if_true,if_false,Fin.val_mk] at hv
    omega
  · simp only [literalSlots,hi,hj,if_true,if_false,Fin.val_mk] at hv
    omega
  · apply Fin.ext
    simp only [literalSlots,hi,hj,if_false,Fin.val_mk] at hv
    omega
theorem above_query (i : Fin 59) (hi : 19 ≤ i.val) : ∀ j,querySlots j≠i:=by
  intro j he
  have h:=congrArg Fin.val he
  have hj:=j.isLt
  simp only [querySlots,Fin.val_castAdd] at h
  omega
theorem literal_other_query (i : Fin 19) (hi : i≠15) : ∀ j,literalSlots j≠querySlots i:=by
  intro j he
  by_cases hj : j=0
  · subst j
    have h:=congrArg Fin.val he
    apply hi
    apply Fin.ext
    change 15=i.val at h
    exact h.symm
  · have h:=congrArg Fin.val he
    have hj0 : j.val≠0:=fun hz=>hj (Fin.ext hz)
    have hb:=i.isLt
    simp only [literalSlots,hj,if_false,querySlots,Fin.val_castAdd,Fin.val_mk] at h
    omega

theorem variable_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (index : Fin (2^(a.output r).clauseBits)) (position : Bool) : ∃ out,
    runFrom machine (budget a r index position) ⟨machine.start,heads,data a r index.val position⟩=some out ∧
      out.steps≤budget a r index position ∧ out.final.heads=heads ∧
      (∀ j,out.final.tapes (querySlots j)=PCPPQueryClauseReuse.data
        (pcppOutput r (a.output r)) r.arity index.val
        (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
      out.final.tapes 57=List.replicate (LiteralIndices.selected
        ((a.output r).clauses index).left ((a.output r).clauses index).right position) true:=by
  let C:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
  let pair:=natListWord [literalIndex ((a.output r).clauses index).left,
    literalIndex ((a.output r).clauses index).right]
  let bank:=PCPPQueryClauseReuse.data (pcppOutput r (a.output r)) r.arity index.val C pair
  obtain ⟨q,hq,qt,qh,qs⟩:=PCPPQueryCachedBounds.clause_run a r index
  rw [PCPPQueryClauseReuse.entry_literal] at hq
  obtain ⟨first,hfirst,_,fs,fh,ft,fkeep⟩:=RecoveryFocus.dock querySlots query_injective
    PCPPQueryClauseReuse.machine _ heads (data a r index.val position) _
    (by intro j;exact Fin.addCases_left j) (by intro j;exact Fin.addCases_left j) q hq
  have firstHeads:first.final.heads=heads:=by
    funext j
    refine Fin.addCases (m:=19) (n:=40) (fun k=>?_) (fun k=>?_) j
    · simp only [heads,Fin.addCases_left]
      exact (fh k).trans (congrFun qh k)
    · exact (fkeep _ (above_query _ (by simp))).1
  obtain ⟨decoded,hd,di,dp⟩:=LiteralIndices.indices_run C
    ((a.output r).clauses index).left ((a.output r).clauses index).right position
  obtain ⟨parsed,hparsed,ph,pt,ps⟩:=hd.focus_at literalSlots literal_injective
    first.final.heads first.final.tapes
    (by intro j
        by_cases hj : j=0
        · subst j;exact (ft 15).trans (congrFun qt 15)
        · rw [(fkeep _ (above_query _ (by simp only [literalSlots,hj,if_false,Fin.val_mk];have hz : j.val≠0:=fun he=>hj (Fin.ext he);omega))).2]
          simp only [literalSlots,hj,if_false]
          have he : (⟨j.val+18,by omega⟩ : Fin 59)=Fin.natAdd 19 (⟨j.val-1,by omega⟩ : Fin 40):=by apply Fin.ext;dsimp;omega
          rw [he]
          simp only [data,Fin.addCases_right,extra,LiteralIndices.input,hj,if_false]
          by_cases hp : j=38
          · subst j;rfl
          · have hm : (⟨j.val-1,by omega⟩ : Fin 40)≠37:=by intro h;apply hp;apply Fin.ext;have hv:=congrArg Fin.val h;dsimp at hv;omega
            simp only [hp,hm,if_false])
    (by intro j;rw [firstHeads];by_cases hj : j=0
        · subst j;rfl
        · have h:=above_query (literalSlots j) (by simp only [literalSlots,hj,if_false,Fin.val_mk];have hz : j.val≠0:=fun he=>hj (Fin.ext he);omega)
          have h13:=h 13
          have h14:=h 14
          simp [heads,Fin.addCases,literalSlots,hj,PCPPQueryClauseReuse.heads] at *
          omega)
  have parsedBank (j : Fin 19) : parsed.final.tapes (querySlots j)=bank j:=by
    rw [pt]
    by_cases hj : j=15
    · subst j
      exact (install_slot literalSlots literal_injective _ decoded 0).trans dp
    · rw [install_other literalSlots _ _ _ (literal_other_query j hj)]
      exact (ft j).trans (congrFun qt j)
  obtain ⟨c,hc,ch,ct,cs⟩:=PCPPQueryClauseReuse.clear_result_run
    (pcppOutput r (a.output r)) r.arity index.val C pair
    (PCPPQueryClauseReuse.query_pair_fits r (a.output r) index C
      (PCPPQueryCachedBounds.clause_capacity a r index))
  obtain ⟨last,hlast,_,ls,lh,lt,lkeep⟩:=RecoveryFocus.dock querySlots query_injective
    PCPPQueryClauseReuse.clearResult _ parsed.final.heads parsed.final.tapes _
    (by intro j;rw [ph,firstHeads];exact Fin.addCases_left j) parsedBank c hc
  have joined:=Composition.run_join query literals _ _ _ first parsed hfirst hparsed
  have whole:=Composition.run_join (Composition.machine query literals) clear _ _ _ _ last joined hlast
  refine ⟨_,whole,?_,?_,?_,?_⟩
  · change first.steps+1+parsed.steps+1+last.steps≤_
    rw [fs,ls,cs]
    unfold budget
    dsimp only [C] at *
    omega
  · change last.final.heads=heads
    funext j
    refine Fin.addCases (m:=19) (n:=40) (fun k=>?_) (fun k=>?_) j
    · simp only [heads,Fin.addCases_left]
      exact (lh k).trans (congrFun ch k)
    · rw [(lkeep _ (above_query _ (by simp))).1,ph,firstHeads]
  · intro j;exact (lt j).trans (congrFun ct j)
  · change last.final.tapes 57=_
    rw [(lkeep 57 (above_query _ (by decide))).2,pt]
    exact (install_slot literalSlots literal_injective _ decoded 39).trans di

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ClauseVariable
