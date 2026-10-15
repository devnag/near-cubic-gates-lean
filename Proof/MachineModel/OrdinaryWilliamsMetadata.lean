import Proof.MachineModel.OrdinaryWilliamsInputHeader

/-! External-input metadata production for the exact-power wrapper. The
canonical payload is traversed to compute c, using U produced by the same
external request. Subsequent metadata use receives the actual tape words. -/
namespace NearCubicWires.RepairOrdinary.WilliamsMetadata
open LocalBitMultitape RecoveryRootRound SourceInterfaces ExecutableInterfaces RepairRepresentation SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev headerStates := 5+WilliamsInputHeader.dimensionStates
abbrev countStates := 2+Fintype.card (RecoveryCalls.Control MatrixPayloadCount.sizes)
def cursorSlots : Fin 2 → Fin 14 := ![5,0]
def countSlots : Fin 3 → Fin 14 := ![12,0,13]
noncomputable def header : Machine 14 headerStates := TapeEmbedding.machine 1 WilliamsInputHeader.machine
noncomputable def cursor : Machine 14 15 := RecoveryFocus.machine cursorSlots MatrixHeaderCursor.machine
noncomputable def first : Machine 14 (headerStates+15) := Composition.machine header cursor
noncomputable def count : Machine 14 countStates := RecoveryFocus.machine countSlots WilliamsPayloadCount.machine
noncomputable def machine := Composition.machine first count
def word (r : RectangularProductRequest) := natWord r.dimension ++ WilliamsPayloadCount.payload r
def input (r : RectangularProductRequest) : Fin 14 → List Bool := fun i => if i=0 then frame (word r) else []
def budget (r : RectangularProductRequest) :=
  WilliamsInputHeader.budget r.dimension (WilliamsPayloadCount.payload r) + 6*natBitLength r.dimension +
    rectangularInnerDimension r.dimension*(6*r.dimension+15)+23
def Data {s : ℕ} (r : RectangularProductRequest) (c : Configuration 14 s) : Prop :=
  c.tapes 0=frame (word r) ∧ c.tapes 1=word r ∧
  c.tapes 3=List.replicate (natBitLength r.dimension) true ∧
  c.tapes 5=UnaryTemplate.tape (natBitLength r.dimension) ∧
  c.tapes 6=frame (binary (natBitLength r.dimension) r.dimension) ∧
  c.tapes 12=UnaryTemplate.tape r.dimension ∧
  c.tapes 13=UnaryTemplate.tape (rectangularInnerDimension r.dimension)

theorem metadata_run (r : RectangularProductRequest) (hr : 1≤r.dimension) :
    ∃ actual : ExecutionReceipt 14 (headerStates+15+countStates),
      run machine (budget r) (input r)=some actual ∧ Data r actual.final ∧ actual.steps≤budget r := by
  let u := r.dimension
  let w := natBitLength u
  let c := rectangularInnerDimension u
  obtain ⟨h,hh,h0,hh0,h1,_,h3,_,h5,hh5,h6,_,h12,hh12,hs⟩ :=
    WilliamsInputHeader.header_run u (WilliamsPayloadCount.payload r)
  have hrun := TapeEmbedding.run_embed WilliamsInputHeader.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => []) _ _ h hh
  let ambient := TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) h.final
  obtain ⟨cr,hcr,hcrf,hcrs⟩ := MatrixHeaderCursor.cursor_run w (frame (word r)) 0
  let cursorEntry := MatrixFramedBlock.config (s:=15) 0 w 1 (frame (word r)) 0
  have hcinput : RecoveryFocus.config cursorSlots ambient.heads ambient.tapes cursorEntry =
      Composition.restart ambient cursor.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact hh5
      · exact hh0
    · intro i; fin_cases i
      · exact h5
      · exact h0
  obtain ⟨crf,hcf,hcff,hcfs⟩ := RecoveryFocus.run_config cursorSlots (by decide) MatrixHeaderCursor.machine
    ambient.heads ambient.tapes (6*w+12) cursorEntry cr hcr
  rw [hcinput] at hcf
  have hfirst := Composition.run_join header cursor (WilliamsInputHeader.budget u (WilliamsPayloadCount.payload r))
    (6*w+12) _ (TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) h) crf hrun hcf
  let prep := Composition.joinedReceipt (TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) h) crf
  have hctape : prep.final.tapes=ambient.tapes := by
    change crf.final.tapes=ambient.tapes
    rw [hcff,hcrf]
    apply install_existing
    intro i; fin_cases i
    · exact h5
    · exact h0
  have hc0 : prep.final.heads 0=2*(2*w+1) := by
    change crf.final.heads (cursorSlots 1)=_
    rw [hcff,hcrf]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot cursorSlots (by decide) 1,MatrixFramedBlock.config]
  have hc12 : prep.final.heads 12=1 := by
    change crf.final.heads 12=1
    rw [hcff]
    have hn : RecoveryFocus.pick cursorSlots (12 : Fin 14)=none := by decide
    simp only [RecoveryFocus.config,hn]
    change h.final.heads 12=1
    exact hh12
  have hc13 : prep.final.heads 13=0 := by
    change crf.final.heads 13=0
    rw [hcff]
    have hn : RecoveryFocus.pick cursorSlots (13 : Fin 14)=none := by decide
    simp only [RecoveryFocus.config,hn]
    rfl
  let pre := Streaming.marks (natWord u)
  have hsource : pre++frame (WilliamsPayloadCount.payload r)=frame (word r) := by
    exact (Streaming.frame_append _ _).symm
  have hpre : pre.length=2*(2*w+1) := by
    simp [pre,WilliamsInputHeader.natWord_eq,Streaming.marks_length,w]
    omega
  obtain ⟨last,hl,hl0,_,hl1,_,hl2,_,hls⟩ := WilliamsPayloadCount.request_run r hr pre
  rw [hsource,hpre] at hl
  rw [hsource] at hl1
  let countEntry : Configuration 3 countStates :=
    Composition.leftConfig _ (WilliamsPayloadCount.input u (frame (word r)) (2*(2*w+1)))
  have hdinput : RecoveryFocus.config countSlots prep.final.heads prep.final.tapes countEntry =
      Composition.restart prep.final count.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact hc12
      · exact hc0
      · exact hc13
    · intro i
      rw [hctape]
      fin_cases i
      · exact h12
      · exact h0
      · rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config countSlots (by decide) WilliamsPayloadCount.machine
    prep.final.heads prep.final.tapes _ countEntry last hl
  rw [hdinput] at hfocus
  have hj := Composition.run_join first count
    (WilliamsInputHeader.budget u (WilliamsPayloadCount.payload r)+1+(6*w+12))
    (c*(6*u+15)+9) _ prep focused hfirst hfocus
  have htime : WilliamsInputHeader.budget u (WilliamsPayloadCount.payload r)+1+(6*w+12)+1+(c*(6*u+15)+9)=budget r := by
    unfold budget
    dsimp only [u,w,c]
    omega
  rw [htime] at hj
  have hin : Composition.leftConfig countStates (Composition.leftConfig 15
      (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
        (initialConfiguration WilliamsInputHeader.machine
          (WilliamsInputHeader.input (natWord u++WilliamsPayloadCount.payload r))))) =
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have hpick (i : Fin 3) : RecoveryFocus.pick countSlots (countSlots i)=some i :=
    RecoveryFocus.pick_slot countSlots (by decide) i
  have other (i : Fin 14) (hi : RecoveryFocus.pick countSlots i=none) :
      focused.final.tapes i=ambient.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,hi]
    rw [hctape]
  refine ⟨Composition.joinedReceipt prep focused,hj,?_,?_⟩
  · change Data r (Composition.rightConfig (headerStates+15) focused.final)
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · change focused.final.tapes (countSlots 1)=_
      rw [hff]
      simpa only [RecoveryFocus.config,hpick] using hl1
    · exact (other 1 (by decide)).trans h1
    · exact (other 3 (by decide)).trans h3
    · exact (other 5 (by decide)).trans h5
    · exact (other 6 (by decide)).trans h6
    · change focused.final.tapes (countSlots 0)=_
      rw [hff]
      simpa only [RecoveryFocus.config,hpick] using hl0
    · change focused.final.tapes (countSlots 2)=_
      rw [hff]
      simpa only [RecoveryFocus.config,hpick] using hl2
  · change h.steps+1+crf.steps+1+focused.steps≤_
    rw [hcfs,hfs,hcrs]
    rw [← htime]
    dsimp only [u,w,c] at *
    omega

end NearCubicWires.RepairOrdinary.WilliamsMetadata
