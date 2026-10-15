import Proof.CaseAnalysis.CaseTwoSourceBlockLayout

/-! One complete original source/cache block from the retained hierarchy,
converted circuit and final address frames. Every source call uses a newly
copied compound request; the three inputs survive for the fixed next block. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceBlock
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RecoveryRootRound
  RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def budget {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)):=
  CompoundInput.budget (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)+1+
    OriginalSource.budget source a H Cpad hpad r oracle

theorem block_run {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (address : List Bool) :
    let request:=PCPPRequestBoundary.request a
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    ∃ result,run (machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source a H Cpad hpad r oracle)
      (input source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address)=some result ∧
      result.steps≤budget source a H Cpad hpad r oracle ∧
      (∀ j,result.final.tapes (cacheSlots source a k j)=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j,result.final.heads (cacheSlots source a k j)=PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (requestSlot source a k)=frame (pcppInput request) ∧
      result.final.heads (requestSlot source a k)=0 ∧
      (∀ i : Fin 3,result.final.tapes (old source a k (i.castAdd 5))=
        ![frame (HierarchySourceInput.hierarchyInput H r),frame (PCPPNative.descriptor oracle),frame address] i) ∧
      (∀ i : Fin 3,result.final.heads (old source a k (i.castAdd 5))=0):=by
  obtain ⟨paired,pairReady,hword,hH,hD⟩:=CompoundInput.pair_ready
    (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)
  have firstReady:=pairReady.focus (pairSlots source a k) (pair_injective source a k)
    (input source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address)
    (pair_input source a k _ _ _)
  obtain ⟨firstReceipt,hfirst,ft,fh,fs⟩:=firstReady
  obtain ⟨base,hb,bs,bt,bh,hrq,hrqh⟩:=OriginalSource.source_run source a H Cpad hcoeff hpad r oracle
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,keep⟩:=RecoveryFocus.dock (t:=OriginalSource.tapes source a k)
    (sourceSlots source a k) (source_injective source a k)
    (OriginalSource.machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _
    firstReceipt.final.heads firstReceipt.final.tapes
    (initialConfiguration (OriginalSource.machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (OriginalSource.input source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle)))
    (by intro j;exact fh _) (by intro j;rw [ft];exact source_input source a k _ _ address paired hword j) base hb
  have he : (⟨(OriginalSource.machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)).start,
      firstReceipt.final.heads,firstReceipt.final.tapes⟩ : Configuration (tapes source a k) _)=
      Composition.restart firstReceipt.final (sourceProgram source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)).start:=rfl
  simp only [initialConfiguration] at hl
  rw [he] at hl
  have whole:=Composition.run_join (pair source a k) (sourceProgram source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    _ _ _ firstReceipt lastReceipt hfirst hl
  refine ⟨Composition.joinedReceipt firstReceipt lastReceipt,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · change firstReceipt.steps+1+lastReceipt.steps≤_
    rw [ls]
    unfold budget
    omega
  · intro j
    change lastReceipt.final.tapes (sourceSlots source a k
      (OriginalSource.slots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j))))=_
    exact (lt _).trans (bt j)
  · intro j
    change lastReceipt.final.heads (sourceSlots source a k
      (OriginalSource.slots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j))))=_
    exact (lh _).trans (bh j)
  · change lastReceipt.final.tapes (sourceSlots source a k
      (OriginalSource.slots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a))))=_
    exact (lt _).trans hrq
  · change lastReceipt.final.heads (sourceSlots source a k
      (OriginalSource.slots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a))))=_
    exact (lh _).trans hrqh
  · intro i
    change lastReceipt.final.tapes (old source a k (i.castAdd 5))=_
    rw [(keep _ (source_away source a k i)).2,ft]
    fin_cases i
    · exact (install_slot (pairSlots source a k) (pair_injective source a k) _ _ 0).trans hH
    · exact (install_slot (pairSlots source a k) (pair_injective source a k) _ _ 1).trans hD
    · rw [install_other (pairSlots source a k) _ _ _ (by
        intro j he
        have hv:=congrArg Fin.val he
        fin_cases j <;>simp [pairSlots,old] at hv)]
      rfl
  · intro i
    change lastReceipt.final.heads (old source a k (i.castAdd 5))=0
    exact ((keep _ (source_away source a k i)).1).trans (fh _)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceBlock
