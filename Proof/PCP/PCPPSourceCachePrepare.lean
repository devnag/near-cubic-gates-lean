import Proof.PCP.PCPPSourceCacheSource

/-! One original native descriptor, one source call, then the physically
allocated shared query bank. No source work tape is rewound or assumed blank. -/
namespace NearCubicWires.RepairOrdinary.PCPPSourceCache
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setupBudget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  PCPPQueryCold.coefficient (degree a) (PCPPQueryCachedBounds.coefficient a)*
    (r.circuit.size+r.arity+1)^(degree a+1)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  PCPPRequestSource.budget a r+1+setupBudget a r
def cacheSlots (a : PointwisePCPPAlgorithm) (j : Fin 19) :=
  coldSlots a (PCPPQueryCold.cacheSlots (degree a) j)
def sizeSlot (a : PointwisePCPPAlgorithm) := coldSlots a (PCPPQueryCold.sizeSlot (degree a))

theorem prepare_run (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    ∃ r,run (machine a) (budget a request) (input a request)=some r ∧
      (∀ j : Fin 19,r.final.tapes (cacheSlots a j)=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j : Fin 19,r.final.heads (cacheSlots a j)=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes (sizeSlot a)=List.replicate request.circuit.size true ∧
      r.final.heads (sizeSlot a)=0 ∧
      r.steps≤PCPPRequestRuntime.sourceCoefficient a*
        (PCPPRequestRuntime.sourceParameter request.circuit)^(PCPPRequestRuntime.sourceDegree a)+1+
        setupBudget a request := by
  obtain ⟨first,hf,ft,fh,fs⟩:=source_run a request
  obtain ⟨base,hb,bt,bh,bs,bsh,bc⟩:=PCPPQueryCold.source_cold_run a
    (pcppOutput request (a.output request)) request.circuit.size request.arity
  obtain ⟨last,hl,_,ls,lh,lt,_⟩:=RecoveryFocus.dock (coldSlots a) (cold_injective a)
    (PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a)) _
    first.final.heads first.final.tapes
    (initialConfiguration (PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a))
      (PCPPQueryCold.input (degree a) (pcppOutput request (a.output request)) request.circuit.size request.arity))
    fh ft base hb
  have he : (⟨(PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a)).start,
      first.final.heads,first.final.tapes⟩ : Configuration (tapes a) _)=
      Composition.restart first.final (setupMachine a).start := rfl
  simp only [initialConfiguration] at hl
  rw [he] at hl
  have whole:=Composition.run_join (sourceMachine a) (setupMachine a) _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,whole,?_,?_,?_,?_,?_⟩
  · intro j
    change last.final.tapes (coldSlots a (PCPPQueryCold.cacheSlots (degree a) j))=_
    exact (lt _).trans (bt j)
  · intro j
    change last.final.heads (coldSlots a (PCPPQueryCold.cacheSlots (degree a) j))=_
    exact (lh _).trans (bh j)
  · change last.final.tapes (coldSlots a (PCPPQueryCold.sizeSlot (degree a)))=_
    exact (lt _).trans bs
  · change last.final.heads (coldSlots a (PCPPQueryCold.sizeSlot (degree a)))=0
    exact (lh _).trans bsh
  · change first.steps+1+last.steps≤_
    rw [ls]
    change base.steps ≤ setupBudget a request at bc
    omega

end NearCubicWires.RepairOrdinary.PCPPSourceCache
