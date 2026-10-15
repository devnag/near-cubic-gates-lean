import Proof.MachineModel.OrdinaryMatrixSignedMaskBounds

/-! A whole original-request execution produces its first exact signed
Williams left plane. The positive p guard is explicit; the all-plane
scheduler owns the zero-p branch and subsequent signed/bit iterations. -/
namespace NearCubicWires.RepairOrdinary.MatrixFirstSignedPlane
open LocalBitMultitape MatrixScoreBatch MatrixSignedEntry
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last := RecoveryFocus.machine slots (MatrixSignedMaskPass.machine false)
noncomputable def machine := Composition.machine MatrixSignedEntry.machine last
noncomputable def budget (r : Request) := MatrixSignedEntry.budget r+1+MatrixSignedMaskPass.budget r

theorem plane_run (r : Request) (hp : 0<r.p) (base : ExecutionReceipt 409 _)
    (hb : run MatrixSignedEntry.machine (MatrixSignedEntry.budget r) (MatrixSignedEntry.input r)=some base)
    (bt : ∀ j,base.final.tapes (slots j)=(entry r).tapes j)
    (bh : ∀ j,base.final.heads (slots j)=(entry r).heads j)
    (bs : base.steps≤MatrixSignedEntry.budget r) : ∃ nb nm na,∃ actual,
    run machine (budget r) (MatrixSignedEntry.input r)=some actual ∧
    (∀ j,actual.final.tapes (slots j)=MatrixSignedMaskPass.output r false false 0 nb nm na j) ∧
    (∀ j,actual.final.heads (slots j)=MatrixSignedMaskPass.finalHeads r j) ∧
    (∀ i,(∀ j,slots j≠i) → actual.final.tapes i=base.final.tapes i ∧ actual.final.heads i=base.final.heads i) ∧
    actual.steps≤budget r := by
  obtain ⟨nb,nm,na,body,hr,rt,rh,_,_,_,rs⟩ := MatrixSignedMaskPass.plane_run r false false 0 hp
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes (entry r)=
      Composition.restart base.final last.start := WilliamsSourceCrop.focus_same slots base.final (entry r) bh bt
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective (MatrixSignedMaskPass.machine false)
    base.final.heads base.final.tapes _ (entry r) body hr
  rw [hi] at hf
  have hj := Composition.run_join MatrixSignedEntry.machine last _ _ _ base focused hb hf
  refine ⟨nb,nm,na,Composition.joinedReceipt base focused,hj,?_,?_,?_,?_⟩
  · intro j
    change focused.final.tapes (slots j)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,rt]
  · intro j
    change focused.final.heads (slots j)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,rh]
  · intro i hi
    change focused.final.tapes i=base.final.tapes i ∧ focused.final.heads i=base.final.heads i
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi]
  · change base.steps+1+focused.steps≤budget r
    rw [fs]
    unfold budget
    omega

theorem raw_run (r : Request) (hp : 0<r.p) : ∃ actual,
    run machine (budget r) (MatrixSignedEntry.input r)=some actual ∧
    actual.final.tapes 407=MatrixSignedPlane.plane r false 0 ∧ actual.final.heads 407=0 ∧
    actual.final.tapes 394=MatrixRightPlaneNative.plane r ∧ actual.final.heads 394=0 ∧
    actual.final.tapes 33=MatrixCoefficientLoop.output r.p r.cuts ∧ actual.final.heads 33=0 ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,_,_,rightT,rightH,bs⟩ := MatrixSignedEntry.raw_run r
  obtain ⟨nb,nm,na,actual,ha,atapes,ah,old,steps⟩ := plane_run r hp base hb bt bh bs
  have retained := old 394 (by decide)
  exact ⟨actual,ha,atapes 13,ah 13,retained.1.trans rightT,retained.2.trans rightH,atapes 0,ah 0,steps⟩

end NearCubicWires.RepairOrdinary.MatrixFirstSignedPlane
