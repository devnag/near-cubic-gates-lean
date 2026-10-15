import Proof.CaseAnalysis.CaseTwoSourceCache
import Proof.CaseAnalysis.CaseTwoRequestInput

/-! Exact native request descriptor plus its actual size/arity runs through
serialization, paid input retention, one faithful source call and cache
allocation. The retained honest request belongs to the same constructor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RequestSource
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (a : PointwisePCPPAlgorithm):=SourceCache.tapes a+RequestInput.tapes
def slots (a : PointwisePCPPAlgorithm) (j : Fin RequestInput.tapes) : Fin (tapes a):=
  if j=RequestInput.outputSlot then ⟨SourceCache.coldTapes a,by
    have h : 0<SourceCall.tapes a:=by dsimp [SourceCall.tapes];omega
    dsimp [tapes,SourceCache.tapes];omega⟩
  else j.natAdd (SourceCache.tapes a)
def cacheSlots (a : PointwisePCPPAlgorithm) (j : Fin (SourceCache.tapes a)) : Fin (tapes a):=j.castAdd RequestInput.tapes
theorem slots_injective (a : PointwisePCPPAlgorithm) : Function.Injective (slots a):=by
  intro i j he
  have hv:=congrArg Fin.val he
  have ht : SourceCache.coldTapes a<SourceCache.tapes a:=by dsimp [SourceCache.tapes,SourceCall.tapes];omega
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;>simp only [Fin.val_natAdd] at hv <;>simp_all only [Fin.ext_iff] <;>omega
theorem cache_injective (a : PointwisePCPPAlgorithm) : Function.Injective (cacheSlots a):=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes a)=>k.val) h)
def input (a : PointwisePCPPAlgorithm) (descriptor : List Bool) (size arity : ℕ) : Fin (tapes a)→List Bool:=fun j=>
  if j.val=SourceCache.tapes a then frame descriptor
  else if j.val=21 then List.replicate size true else if j.val=19 then List.replicate arity true else []
noncomputable def first (a : PointwisePCPPAlgorithm):=RecoveryFocus.machine (slots a) RequestInput.machine
noncomputable def last (a : PointwisePCPPAlgorithm):=RecoveryFocus.machine (cacheSlots a) (SourceCache.machine a)
noncomputable def machine (a : PointwisePCPPAlgorithm):=Composition.machine (first a) (last a)
def budget (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity):=
  RequestInput.budget request.circuit+1+SourceCache.budget a request

theorem serial_input (a : PointwisePCPPAlgorithm) (descriptor : List Bool) (size arity : ℕ)
    (j : Fin RequestInput.tapes) :
    input a descriptor size arity (slots a j)=RequestInput.input descriptor j:=by
  have hc:=SourceCache.cold_lower a
  have ht : SourceCache.coldTapes a<SourceCache.tapes a:=by dsimp [SourceCache.tapes,SourceCall.tapes];omega
  have ho : 0<RequestInput.outputSlot.val:=by decide
  unfold input slots RequestInput.input SourceHandoff.sourceTapes
  split_ifs <;>simp_all only [Fin.val_natAdd,Fin.ext_iff]
  all_goals omega

theorem serial_ready (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) : ∃ A,
    ClockJoin.ReadyRun (first a) (RequestInput.budget request.circuit)
      (input a (PCPPNative.descriptor request.circuit) request.circuit.size request.arity) A ∧
      ∀ j,A (cacheSlots a j)=SourceCache.input a (pcppInput request) request.circuit.size request.arity j:=by
  obtain ⟨out,hr,ht⟩:=RequestInput.request_run request
  have h:=ClockJoin.ReadyRun.focus (t:=RequestInput.tapes) (p:=RequestInput.machine) hr (slots a) (slots_injective a)
    (input a (PCPPNative.descriptor request.circuit) request.circuit.size request.arity) (serial_input a _ _ _)
  refine ⟨_,h,?_⟩
  intro j
  by_cases hj : j.val=SourceCache.coldTapes a
  · have he : cacheSlots a j=slots a RequestInput.outputSlot:=by apply Fin.ext;simp [cacheSlots,slots,hj]
    rw [he,install_slot (slots a) (slots_injective a),ht]
    simp only [SourceCache.input,hj,if_true]
  · have away : ∀ i,slots a i≠cacheSlots a j:=by
      intro i he
      have hv:=congrArg Fin.val he
      have hb:=j.isLt
      dsimp only [slots,cacheSlots] at hv
      split_ifs at hv <;>simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;>omega
    rw [install_other (slots a) _ _ _ away]
    have hn : j.val≠SourceCache.tapes a:=by omega
    simp only [input,cacheSlots,Fin.val_castAdd,hn,if_false,SourceCache.input,hj]
    rfl

theorem source_run (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    ∃ r,run (machine a) (budget a request)
      (input a (PCPPNative.descriptor request.circuit) request.circuit.size request.arity)=some r ∧
      r.steps≤budget a request ∧
      (∀ j,r.final.tapes (cacheSlots a (SourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j,r.final.heads (cacheSlots a (SourceCache.cacheSlots a j))=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes (cacheSlots a (SourceCache.requestSlot a))=frame (pcppInput request) ∧
      r.final.heads (cacheSlots a (SourceCache.requestSlot a))=0:=by
  obtain ⟨A,ready,hA⟩:=serial_ready a request
  obtain ⟨firstReceipt,hf,ft,fh,fs⟩:=ready
  obtain ⟨base,hb,bs,bt,bh,_size,_sizeh,keep,keeph⟩:=SourceCache.cache_run a request
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,_⟩:=RecoveryFocus.dock (cacheSlots a) (cache_injective a)
    (SourceCache.machine a) _ firstReceipt.final.heads firstReceipt.final.tapes
    (initialConfiguration (SourceCache.machine a)
      (SourceCache.input a (pcppInput request) request.circuit.size request.arity))
    (by intro j;exact fh _) (by intro j;rw [ft];exact hA j) base hb
  have he : (⟨(SourceCache.machine a).start,firstReceipt.final.heads,firstReceipt.final.tapes⟩ : Configuration (tapes a) _)=
      Composition.restart firstReceipt.final (last a).start:=rfl
  simp only [initialConfiguration] at hl
  rw [he] at hl
  have whole:=Composition.run_join (first a) (last a) _ _ _ firstReceipt lastReceipt hf hl
  refine ⟨Composition.joinedReceipt firstReceipt lastReceipt,whole,?_,?_,?_,?_,?_⟩
  · change firstReceipt.steps+1+lastReceipt.steps≤_
    rw [ls]
    unfold budget
    omega
  · intro j
    change lastReceipt.final.tapes (cacheSlots a (SourceCache.cacheSlots a j))=_
    exact (lt _).trans (bt j)
  · intro j
    change lastReceipt.final.heads (cacheSlots a (SourceCache.cacheSlots a j))=_
    exact (lh _).trans (bh j)
  · change lastReceipt.final.tapes (cacheSlots a (SourceCache.requestSlot a))=_
    exact (lt _).trans keep
  · change lastReceipt.final.heads (cacheSlots a (SourceCache.requestSlot a))=_
    exact (lh _).trans keeph

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RequestSource
