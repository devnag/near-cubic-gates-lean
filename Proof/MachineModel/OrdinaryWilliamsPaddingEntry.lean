import Proof.MachineModel.OrdinaryWilliamsPaddingCursors

/-! Cold entry for padding: preserve the crop's U driver, produce a
separate padding copy, and physically position both raw-header cursors. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPaddingEntry
open LocalBitMultitape RecoveryRootRound RepairRepresentation SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 5 → Fin 14 := ![4,10,11,12,13]
def cursorSlots : Fin 4 → Fin 14 := ![1,8,2,9]
noncomputable def copy := RecoveryFocus.machine copySlots MatrixTemplateCopy.resetMachine
noncomputable def cursors := RecoveryFocus.machine cursorSlots WilliamsPaddingCursors.machine
noncomputable def machine := Composition.machine copy cursors
def input (r : RectangularProductRequest) : Fin 14 → List Bool :=
  let u := r.dimension
  let c := rectangularInnerDimension u
  let v := WilliamsPaddedRequest.dimension u
  ![UnaryTemplate.tape (u*c),WilliamsMetadata.word r,natWord v,UnaryTemplate.tape ((v-u)*c),
    UnaryTemplate.tape u,[],UnaryTemplate.tape (v-u),UnaryTemplate.tape c,
    UnaryTemplate.tape (natBitLength u),UnaryTemplate.tape (natBitLength v),[],[],[],[]]
def heads (r : RectangularProductRequest) : Fin 14 → ℕ :=
  ![0,2*natBitLength r.dimension+1,2*natBitLength (WilliamsPaddedRequest.dimension r.dimension)+1,
    0,0,0,0,0,1,1,0,0,0,0]
def Good (r : RectangularProductRequest) (a : Fin 14 → List Bool) : Prop :=
  (∀ i, i.val<10 → a i=input r i) ∧ a 12=UnaryTemplate.tape r.dimension

theorem entry_run (r : RectangularProductRequest) :
    ∃ actual : ExecutionReceipt 14 22,
      run machine (4*r.dimension+3*natBitLength r.dimension+
        3*natBitLength (WilliamsPaddedRequest.dimension r.dimension)+24) (input r)=some actual ∧
      Good r actual.final.tapes ∧ actual.final.heads=heads r ∧
      actual.steps=4*r.dimension+3*natBitLength r.dimension+
        3*natBitLength (WilliamsPaddedRequest.dimension r.dimension)+24 := by
  let u := r.dimension
  let v := WilliamsPaddedRequest.dimension u
  obtain ⟨base,hb,h0,_,_,h3,hh,hs⟩ := MatrixTemplateCopy.reset_run u
  have bready : ReadyRun MatrixTemplateCopy.resetMachine (4*u+12)
      (MatrixTemplateCopy.resetInput u) base.final.tapes := ⟨base,hb,rfl,hh,hs⟩
  have hcin : ∀ i, input r (copySlots i)=MatrixTemplateCopy.resetInput u i := by
    intro i; fin_cases i <;> rfl
  let store := install copySlots (input r) base.final.tapes
  obtain ⟨copied,hcopy,hct,hch,hcs⟩ := bready.focus copySlots (by decide) (input r) hcin
  have cPick (i : Fin 14) : RecoveryFocus.pick copySlots i=
      (![none,none,none,none,some 0,none,none,none,none,none,some 1,some 2,some 3,some 4] : Fin 14 → Option (Fin 5)) i := by
    fin_cases i <;> first
    | exact RecoveryFocus.pick_slot copySlots (by decide) 0
    | exact RecoveryFocus.pick_slot copySlots (by decide) 1
    | exact RecoveryFocus.pick_slot copySlots (by decide) 2
    | exact RecoveryFocus.pick_slot copySlots (by decide) 3
    | exact RecoveryFocus.pick_slot copySlots (by decide) 4
    | decide
  have good : Good r store := by
    constructor
    · intro i hi
      fin_cases i <;> simp at hi
      all_goals simp [store,install,cPick,input,h0,u]
    · exact (install_slot copySlots (by decide) (input r) base.final.tapes 3).trans h3
  obtain ⟨last,hl,hlt,hlh,hls⟩ := WilliamsPaddingCursors.cursors_run
    (WilliamsMetadata.word r) (natWord v) (natBitLength u) (natBitLength v)
  have hcinput : ∀ i, copied.final.tapes (cursorSlots i)=
      WilliamsPaddingCursors.input (WilliamsMetadata.word r) (natWord v) (natBitLength u) (natBitLength v) i := by
    intro i; rw [hct]
    fin_cases i
    · exact good.1 1 (by decide)
    · exact good.1 8 (by decide)
    · exact good.1 2 (by decide)
    · exact good.1 9 (by decide)
  have hi : RecoveryFocus.config cursorSlots copied.final.heads copied.final.tapes
      (initialConfiguration WilliamsPaddingCursors.machine
        (WilliamsPaddingCursors.input (WilliamsMetadata.word r) (natWord v) (natBitLength u) (natBitLength v))) =
      Composition.restart copied.final cursors.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact hch _
    · exact hcinput
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config cursorSlots (by decide) WilliamsPaddingCursors.machine
    copied.final.heads copied.final.tapes _ _ last hl
  rw [hi] at hfocus
  have hj := Composition.run_join copy cursors (4*u+12) (3*natBitLength u+3*natBitLength v+11)
    _ copied focused hcopy hfocus
  have htime : (4*u+12)+1+(3*natBitLength u+3*natBitLength v+11)=4*u+3*natBitLength u+3*natBitLength v+24 := by omega
  rw [htime] at hj
  have tfinal : focused.final.tapes=store := by
    rw [hff]
    change install cursorSlots copied.final.tapes last.final.tapes=store
    rw [hlt,install_existing cursorSlots copied.final.tapes _ hcinput]
    exact hct
  have pick (i : Fin 14) : RecoveryFocus.pick cursorSlots i=
      (![none,some 0,some 2,none,none,none,none,none,some 1,some 3,none,none,none,none] : Fin 14 → Option (Fin 4)) i := by
    fin_cases i <;> first
    | exact RecoveryFocus.pick_slot cursorSlots (by decide) 0
    | exact RecoveryFocus.pick_slot cursorSlots (by decide) 1
    | exact RecoveryFocus.pick_slot cursorSlots (by decide) 2
    | exact RecoveryFocus.pick_slot cursorSlots (by decide) 3
    | decide
  refine ⟨Composition.joinedReceipt copied focused,hj,?_,?_,?_⟩
  · change Good r focused.final.tapes
    rw [tfinal]
    exact good
  · change focused.final.heads=heads r
    rw [hff]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick,hlh,hch,heads,u,v]
  · change copied.steps+1+focused.steps=_
    rw [hcs,hfs,hls]
    exact htime

end NearCubicWires.RepairOrdinary.WilliamsPaddingEntry
