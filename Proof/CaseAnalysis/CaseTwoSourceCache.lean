import Proof.CaseAnalysis.CaseTwoSourceCacheLayout

/-! One physically copied faithful request produces the shared PCPP cache.
Its exact retained frame stays available for honest auxiliary evaluation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceCache
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_run (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) : ∃ A,
    ClockJoin.ReadyRun (sourceMachine a) (SourceCall.budget a request)
      (input a (pcppInput request) request.circuit.size request.arity) A ∧
      (∀ j,A (coldSlots a j)=PCPPQueryCold.input (degree a)
        (pcppOutput request (a.output request)) request.circuit.size request.arity j) ∧
      A (requestSlot a)=frame (pcppInput request):=by
  obtain ⟨out,hr,ho,keep⟩:=SourceCall.source_run a request
  have f:=hr.focus (sourceSlots a) (source_injective a)
    (input a (pcppInput request) request.circuit.size request.arity)
    (source_input a _ _ _)
  refine ⟨_,f,?_,?_⟩
  · intro j
    by_cases hj : j.val=0
    · have he : j=⟨0,by have h:=cold_lower a;omega⟩:=Fin.ext hj
      rw [he,←source_output,install_slot (sourceSlots a) (source_injective a)]
      exact ho
    · rw [install_other (sourceSlots a) _ _ _ (source_other a j hj)]
      have hc:=cold_lower a
      have hn : j.val≠coldTapes a:=by omega
      simp [input,coldSlots,PCPPQueryCold.input,hj,hn]
      rfl
  · exact (install_slot (sourceSlots a) (source_injective a) _ _ _).trans keep

theorem cache_run (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    ∃ r,run (machine a) (budget a request)
      (input a (pcppInput request) request.circuit.size request.arity)=some r ∧
      r.steps≤budget a request ∧
      (∀ j,r.final.tapes (cacheSlots a j)=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j,r.final.heads (cacheSlots a j)=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes (sizeSlot a)=List.replicate request.circuit.size true ∧ r.final.heads (sizeSlot a)=0 ∧
      r.final.tapes (requestSlot a)=frame (pcppInput request) ∧ r.final.heads (requestSlot a)=0:=by
  obtain ⟨A,firstReady,ft,fkeep⟩:=source_run a request
  obtain ⟨first,hf,firstTapes,fh,fs⟩:=firstReady
  obtain ⟨base,hb,bt,bh,bs,bsh,bc⟩:=PCPPQueryCold.source_cold_run a
    (pcppOutput request (a.output request)) request.circuit.size request.arity
  obtain ⟨last,hl,_,ls,lh,lt,keep⟩:=RecoveryFocus.dock (coldSlots a) (cold_injective a)
    (PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a)) _
    first.final.heads first.final.tapes
    (initialConfiguration (PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a))
      (PCPPQueryCold.input (degree a) (pcppOutput request (a.output request)) request.circuit.size request.arity))
    (by intro j;exact fh _) (by intro j;rw [firstTapes];exact ft j) base hb
  have he : (⟨(PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a)).start,
      first.final.heads,first.final.tapes⟩ : Configuration (tapes a) _)=
      Composition.restart first.final (setupMachine a).start:=rfl
  simp only [initialConfiguration] at hl
  rw [he] at hl
  have whole:=Composition.run_join (sourceMachine a) (setupMachine a) _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤_
    rw [ls]
    change base.steps≤PCPPSourceCache.setupBudget a request at bc
    unfold budget
    omega
  · intro j
    exact (lt _).trans (bt j)
  · intro j
    exact (lh _).trans (bh j)
  · exact (lt _).trans bs
  · exact (lh _).trans bsh
  · exact ((keep _ (cold_away a)).2).trans ((congrFun firstTapes _).trans fkeep)
  · exact ((keep _ (cold_away a)).1).trans (fh _)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceCache
