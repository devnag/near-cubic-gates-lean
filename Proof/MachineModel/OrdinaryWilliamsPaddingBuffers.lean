import Proof.MachineModel.OrdinaryWilliamsPaddingEntry

/-! Complete cold-template to both padded source buffers. All cursor
positioning, duplicate allocation, boot moves and the pad/serialize pass
are real transitions; the crop's U and width-U drivers are retained. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPaddingBuffers
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation SourceInterfaces ExecutableInterfaces WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def marked (i : Fin 14) : Bool := decide (i=0 ∨ i=3 ∨ i=12 ∨ i=6 ∨ i=7)
def boot : Machine 14 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if marked i then .right else .stay⟩ else none
def heads (r : RectangularProductRequest) : Fin 14 → ℕ :=
  ![1,2*natBitLength r.dimension+1,2*natBitLength (WilliamsPaddedRequest.dimension r.dimension)+1,
    1,0,0,1,1,1,1,0,0,1,0]

theorem boot_run (r : RectangularProductRequest) (a : Fin 14 → List Bool) :
    ∃ actual : ExecutionReceipt 14 2,
      runFrom boot 1 ⟨0,WilliamsPaddingEntry.heads r,a⟩=some actual ∧
      actual.final=⟨1,heads r,a⟩ ∧ actual.steps=1 := by
  have hs : step boot ⟨0,WilliamsPaddingEntry.heads r,a⟩=some ⟨1,heads r,a⟩ := by
    simp [step,boot]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,marked,WilliamsPaddingEntry.heads,heads]
    · funext i; simp [applyAction]
  exact (Timed.single (by rfl) hs).run (by rfl)

def slots : Fin 8 → Fin 14 := ![0,1,2,3,12,5,6,7]
noncomputable def first := Composition.machine WilliamsPaddingEntry.machine boot
noncomputable def padCore : Machine 8 25 := WilliamsPadding.joinedMachine
noncomputable def pad := RecoveryFocus.machine slots padCore
noncomputable def machine := Composition.machine first pad
def budget (r : RectangularProductRequest) :=
  4*r.dimension+3*natBitLength r.dimension+3*natBitLength (WilliamsPaddedRequest.dimension r.dimension)+
    4*WilliamsPaddedRequest.dimension r.dimension*rectangularInnerDimension r.dimension+
    12*rectangularInnerDimension r.dimension+40

theorem buffers_run (r : RectangularProductRequest) :
    ∃ actual : ExecutionReceipt 14 49,
      run machine (budget r) (WilliamsPaddingEntry.input r)=some actual ∧
      actual.final.tapes 2=natWord (WilliamsPaddedRequest.dimension r.dimension)++rowMajorBitMatrix (WilliamsPaddedRequest.left r) ∧
      actual.final.tapes 5=rowMajorBitMatrix (WilliamsPaddedRequest.right r) ∧
      actual.final.tapes 4=UnaryTemplate.tape r.dimension ∧
      actual.final.tapes 8=UnaryTemplate.tape (natBitLength r.dimension) ∧ actual.steps ≤ budget r := by
  let u := r.dimension
  let v := WilliamsPaddedRequest.dimension u
  let c := rectangularInnerDimension u
  obtain ⟨base,hb,hgood,hh,hs⟩ := WilliamsPaddingEntry.entry_run r
  obtain ⟨booted,hboot,hbf,hbs⟩ := boot_run r base.final.tapes
  have hmid : Composition.restart base.final boot.start=⟨0,WilliamsPaddingEntry.heads r,base.final.tapes⟩ := by
    apply configuration_ext
    · rfl
    · exact hh
    · rfl
  rw [←hmid] at hboot
  have hfirst := Composition.run_join WilliamsPaddingEntry.machine boot
    (4*u+3*natBitLength u+3*natBitLength v+24) 1 _ base booted hb hboot
  let prep := Composition.joinedReceipt base booted
  have pheads : prep.final.heads=heads r := by change booted.final.heads=_; rw [hbf]
  have ptapes : prep.final.tapes=base.final.tapes := by change booted.final.tapes=_; rw [hbf]
  obtain ⟨last,hl,hl2,hl5,hls⟩ := WilliamsPadding.sentinel_run r (natWord u) []
  have hlen (n : ℕ) : (natWord n).length=2*natBitLength n+1 := WilliamsLoader.nat_frame_length n
  have hpin : RecoveryFocus.config slots prep.final.heads prep.final.tapes
      (WilliamsPadding.sentinelInput r (natWord u) [])=Composition.restart prep.final pad.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [pheads]
      fin_cases i <;> simp [slots,heads,WilliamsPadding.sentinelInput,hlen,u]
    · intro i
      rw [ptapes]
      fin_cases i
      · exact hgood.1 0 (by decide)
      · have h := hgood.1 1 (by decide)
        simpa [WilliamsPaddingEntry.input,WilliamsPadding.sentinelInput,slots,WilliamsMetadata.word,
          WilliamsPayloadCount.payload,List.append_assoc,u] using h
      · exact hgood.1 2 (by decide)
      · exact hgood.1 3 (by decide)
      · exact hgood.2
      · exact hgood.1 5 (by decide)
      · exact hgood.1 6 (by decide)
      · exact hgood.1 7 (by decide)
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) padCore
    prep.final.heads prep.final.tapes _ _ last hl
  rw [hpin] at hfocus
  have hj := Composition.run_join first pad
    ((4*u+3*natBitLength u+3*natBitLength v+24)+1+1) (4*v*c+12*c+13) _ prep focused hfirst hfocus
  have htime : ((4*u+3*natBitLength u+3*natBitLength v+24)+1+1)+1+(4*v*c+12*c+13)=budget r := by
    unfold budget
    dsimp only [u,v,c]
    omega
  rw [htime] at hj
  have hpick (i : Fin 8) : RecoveryFocus.pick slots (slots i)=some i := RecoveryFocus.pick_slot slots (by decide) i
  have other (i : Fin 14) (hi : RecoveryFocus.pick slots i=none) : focused.final.tapes i=base.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,hi]
    rw [ptapes]
  refine ⟨Composition.joinedReceipt prep focused,hj,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes (slots 2)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl2
  · change focused.final.tapes (slots 5)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl5
  · exact (other 4 (by decide)).trans (hgood.1 4 (by decide))
  · exact (other 8 (by decide)).trans (hgood.1 8 (by decide))
  · change base.steps+1+booted.steps+1+focused.steps ≤ _
    rw [hs,hbs,hfs]
    unfold budget
    dsimp only [u,v,c] at *
    omega

end NearCubicWires.RepairOrdinary.WilliamsPaddingBuffers
