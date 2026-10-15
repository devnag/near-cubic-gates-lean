import Proof.CaseAnalysis.CaseTwoRequestSource

/-! A physical producer supplies the three exact request fields to the
checked retained source worker. The generic producer state type stays opaque;
all new source/cache scratch belongs to one initially empty fixed bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.NativeSourceDock
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (a : PointwisePCPPAlgorithm) (t : ℕ):=t+RequestSource.tapes a
def oldSlots (a : PointwisePCPPAlgorithm) {t : ℕ} (i : Fin t) : Fin (tapes a t):=i.castAdd (RequestSource.tapes a)
def slots (a : PointwisePCPPAlgorithm) {t : ℕ} (field size arity : Fin t)
    (j : Fin (RequestSource.tapes a)) : Fin (tapes a t):=
  if j.val=SourceCache.tapes a then oldSlots a field else if j.val=21 then oldSlots a size
  else if j.val=19 then oldSlots a arity else j.natAdd t
theorem old_injective (a : PointwisePCPPAlgorithm) (t : ℕ) : Function.Injective (@oldSlots a t):=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes a t)=>k.val) h)
theorem slots_injective (a : PointwisePCPPAlgorithm) {t : ℕ} (field size arity : Fin t)
    (hfs : field≠size) (hfa : field≠arity) (hsa : size≠arity) : Function.Injective (slots a field size arity):=by
  intro i j he
  have hv:=congrArg Fin.val he
  have hf:=field.isLt
  have hs:=size.isLt
  have ha:=arity.isLt
  have hfs' : field.val≠size.val:=fun h=>hfs (Fin.ext h)
  have hfa' : field.val≠arity.val:=fun h=>hfa (Fin.ext h)
  have hsa' : size.val≠arity.val:=fun h=>hsa (Fin.ext h)
  apply Fin.ext
  dsimp only [slots,oldSlots] at hv
  split_ifs at hv <;>simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;>omega
def input (a : PointwisePCPPAlgorithm) {t : ℕ} (native : Fin t→List Bool) : Fin (tapes a t)→List Bool:=
  Fin.addCases native (fun _ : Fin (RequestSource.tapes a)=>[])
noncomputable def first (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s):=
  RecoveryFocus.machine (oldSlots a) p
noncomputable def last (a : PointwisePCPPAlgorithm) {t : ℕ} (field size arity : Fin t):=
  RecoveryFocus.machine (slots a field size arity) (RequestSource.machine a)
noncomputable def machine (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s) (field size arity : Fin t):=
  Composition.machine (first a p) (last a field size arity)

theorem field_input (a : PointwisePCPPAlgorithm) {t : ℕ} (field size arity : Fin t)
    (native : Fin t→List Bool) (out : Fin t→List Bool) (descriptor : List Bool) (sz ar : ℕ)
    (hf : out field=frame descriptor) (hs : out size=List.replicate sz true)
    (ha : out arity=List.replicate ar true) (j : Fin (RequestSource.tapes a)) :
    install (oldSlots a) (input a native) out (slots a field size arity j)=RequestSource.input a descriptor sz ar j:=by
  unfold slots RequestSource.input
  split_ifs with h0 h21 h19
  · exact (install_slot (oldSlots a) (old_injective a t) _ _ field).trans hf
  · exact (install_slot (oldSlots a) (old_injective a t) _ _ size).trans hs
  · exact (install_slot (oldSlots a) (old_injective a t) _ _ arity).trans ha
  · rw [install_other (oldSlots a) _ _ (j.natAdd t) (by
      intro i he
      have hv:=congrArg Fin.val he
      dsimp [oldSlots] at hv
      omega)]
    simp only [input,Fin.addCases_right]

theorem source_run (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (field size arity : Fin t) (hfs : field≠size) (hfa : field≠arity) (hsa : size≠arity)
    (request : PCPPRequest a.minimumArity) (fuel : ℕ) (native out : Fin t→List Bool)
    (hp : ClockJoin.ReadyRun p fuel native out)
    (hf : out field=frame (PCPPNative.descriptor request.circuit))
    (hs : out size=List.replicate request.circuit.size true) (ha : out arity=List.replicate request.arity true) :
    ∃ r,run (machine a p field size arity) (fuel+1+RequestSource.budget a request) (input a native)=some r ∧
      r.steps≤fuel+1+RequestSource.budget a request ∧
      (∀ j,r.final.tapes (slots a field size arity (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j,r.final.heads (slots a field size arity (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes (slots a field size arity (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=frame (pcppInput request) ∧
      r.final.heads (slots a field size arity (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=0:=by
  have prep:=hp.focus (oldSlots a) (old_injective a t) (input a native) (by
    intro i
    simp only [input,oldSlots,Fin.addCases_left])
  obtain ⟨firstReceipt,hfirst,ft,fh,fs⟩:=prep
  obtain ⟨base,hb,bs,bt,bh,keep,keeph⟩:=RequestSource.source_run a request
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,_⟩:=RecoveryFocus.dock (slots a field size arity)
    (slots_injective a field size arity hfs hfa hsa) (RequestSource.machine a) _ firstReceipt.final.heads firstReceipt.final.tapes
    (initialConfiguration (RequestSource.machine a) (RequestSource.input a (PCPPNative.descriptor request.circuit) request.circuit.size request.arity))
    (by intro j;exact fh _) (by intro j;rw [ft];exact field_input a field size arity native out _ _ _ hf hs ha j) base hb
  have he : (⟨(RequestSource.machine a).start,firstReceipt.final.heads,firstReceipt.final.tapes⟩ : Configuration (tapes a t) _)=
      Composition.restart firstReceipt.final (last a field size arity).start:=rfl
  simp only [initialConfiguration] at hl
  rw [he] at hl
  have whole:=Composition.run_join (first a p) (last a field size arity) _ _ _ firstReceipt lastReceipt hfirst hl
  refine ⟨Composition.joinedReceipt firstReceipt lastReceipt,whole,?_,?_,?_,?_,?_⟩
  · change firstReceipt.steps+1+lastReceipt.steps≤_
    rw [ls]
    omega
  · intro j
    change lastReceipt.final.tapes (slots a field size arity (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=_
    exact (lt _).trans (bt j)
  · intro j
    change lastReceipt.final.heads (slots a field size arity (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=_
    exact (lh _).trans (bh j)
  · change lastReceipt.final.tapes (slots a field size arity (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=_
    exact (lt _).trans keep
  · change lastReceipt.final.heads (slots a field size arity (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=_
    exact (lh _).trans keeph

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.NativeSourceDock
