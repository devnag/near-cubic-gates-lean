import Proof.MachineModel.OrdinaryMatrixBatchGateEntry

namespace NearCubicWires.RepairOrdinary.MatrixBatchAllRanks
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open MatrixBatchGateLayout (slots slots_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last := RecoveryFocus.machine slots MatrixBatchGateLoop.machine
noncomputable def machine := Composition.machine MatrixBatchGateColdEntry.machine last
def budget (r : Request) := MatrixBatchGateColdEntry.budget r+1+MatrixBatchGateNativeLoop.budget r

theorem all_run (r : Request) :
    ∃ final : MatrixBatchGateStore.Store r,∃ actual,
      run machine (budget r) (MatrixBatchGateColdEntry.input r)=some actual ∧
      (∀ i,actual.final.heads (slots i)=
        (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) final).heads i) ∧
      (∀ i,actual.final.tapes (slots i)=
        (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) final).tapes i) ∧
      actual.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧
      actual.final.heads 162=(MatrixBatchGateNativeLoop.output r).length ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 40=List.replicate r.p true ∧ actual.final.heads 40=0 ∧
      actual.final.tapes 80=List.replicate (natBitLength r.Gates) true ∧ actual.final.heads 80=0 ∧
      actual.final.tapes 83=frame (SignedSortKey.binary (natBitLength r.Gates) r.Gates) ∧ actual.final.heads 83=0 ∧
      actual.steps≤budget r := by
  obtain ⟨prepared,hp,s,ph,pt,p0,h0,p40,h40,p80,h80,p83,h83,ps⟩ := MatrixBatchGateColdEntry.entry_run r
  obtain ⟨final,base,hb,hbf,bs⟩ := MatrixBatchGateNativeLoop.all_run r s []
  let entry := MatrixBatchGateNativeLoop.cfg r 0 (word r) (header r).length [] s
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · exact ph
    · exact pt
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBatchGateLoop.machine
    prepared.final.heads prepared.final.tapes _ entry base hb
  rw [hi] at hf
  have joined := Composition.run_join MatrixBatchGateColdEntry.machine last _ _ _ prepared focused hp hf
  have localT (i : Fin 49) : focused.final.tapes (slots i)=
      (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) final).tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,hbf,List.nil_append]
  have localH (i : Fin 49) : focused.final.heads (slots i)=
      (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) final).heads i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,hbf,List.nil_append]
  have otherT (i : Fin 166) (hn : RecoveryFocus.pick slots i=none) : focused.final.tapes i=prepared.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,hn]
  have otherH (i : Fin 166) (hn : RecoveryFocus.pick slots i=none) : focused.final.heads i=prepared.final.heads i := by
    rw [hff]
    simp only [RecoveryFocus.config,hn]
  refine ⟨final,Composition.joinedReceipt prepared focused,joined,localH,localT,?_,?_,
    (otherT 0 (by decide)).trans p0,(otherH 0 (by decide)).trans h0,
    (otherT 40 (by decide)).trans p40,(otherH 40 (by decide)).trans h40,
    (otherT 80 (by decide)).trans p80,(otherH 80 (by decide)).trans h80,
    (otherT 83 (by decide)).trans p83,(otherH 83 (by decide)).trans h83,?_⟩
  · change focused.final.tapes (slots 41)=_
    rw [localT,MatrixBatchGateNativeLoop.cfg_tapes]
    simp [Fin.addCases,MatrixBatchGateClear.tapes,install,MatrixBatchGateClear.pick_scratch,
      MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable]
  · exact localH 41
  · change prepared.steps+1+focused.steps≤_
    rw [hfs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchAllRanks
