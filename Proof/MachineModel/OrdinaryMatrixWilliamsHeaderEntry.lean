import Proof.MachineModel.OrdinaryMatrixPowerHeader

/-! The paid canonical Williams header on the same original-request run
that produced both matrices and the first signed coefficient plane. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsHeaderEntry
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 412 := ![12,409,410,411]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 3 MatrixFirstSignedPlane.machine
noncomputable def last := RecoveryFocus.machine slots MatrixPowerHeader.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 412 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixFirstSignedPlane.budget r+1+(6*r.d+14)

def selected : Fin 6 → Fin 412 := ![400,200,407,394,409,410]
noncomputable def values (r : Request) : Fin 6 → List Bool :=
  ![UnaryTemplate.tape r.U,UnaryTemplate.tape r.Capacity,MatrixSignedPlane.plane r false 0,
    MatrixRightPlaneNative.plane r,RepairRepresentation.natWord r.U,UnaryTemplate.tape (2*r.d+3)]
def heads : Fin 6 → ℕ := ![1,1,0,0,0,0]

theorem raw_run (r : Request) (hp : 0<r.p) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    (∀ j,actual.final.tapes (selected j)=values r j) ∧
    (∀ j,actual.final.heads (selected j)=heads j) ∧ actual.steps≤budget r := by
  obtain ⟨entry,he,et,eh,_,_,rightT,rightH,es⟩ := MatrixSignedEntry.raw_run r
  obtain ⟨same,hs,st,sh,_⟩ := MatrixSignedEntryRetained.retained_run r
  have heq : same=entry := Option.some.inj (hs.symm.trans he)
  subst same
  obtain ⟨nb,nm,na,base,hb,bt,bh,old,bs⟩ := MatrixFirstSignedPlane.plane_run r hp entry he et eh es
  have dT : base.final.tapes 12=UnaryTemplate.tape r.d := (old 12 (by decide)).1.trans (st 0)
  have dH : base.final.heads 12=0 := (old 12 (by decide)).2.trans (sh 0)
  have rt : base.final.tapes 394=MatrixRightPlaneNative.plane r := (old 394 (by decide)).1.trans rightT
  have rh : base.final.heads 394=0 := (old 394 (by decide)).2.trans rightH
  have hemb := TapeEmbedding.run_embed MatrixFirstSignedPlane.machine (fun _ : Fin 3 => 0) (fun _ : Fin 3 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 3 => 0) (fun _ : Fin 3 => []) base
  obtain ⟨body,hr,b0,b1,b2,bodyH,bodyS⟩ := MatrixPowerHeader.header_run r.d
  let localEntry := initialConfiguration MatrixPowerHeader.machine (MatrixPowerHeader.resetInput r.d)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes localEntry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      · exact dH
      all_goals rfl
    · intro j; fin_cases j
      · exact dT
      all_goals rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixPowerHeader.machine
    prepared.final.heads prepared.final.tapes _ localEntry body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused hemb hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 3 => 0) (fun _ : Fin 3 => [])
      (initialConfiguration MatrixFirstSignedPlane.machine (MatrixSignedEntry.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localT (j : Fin 4) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 4) : focused.final.heads (slots j)=body.final.heads j := by
    rw [ff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have retained (i : Fin 409) (hn : RecoveryFocus.pick slots (i.castAdd 3)=none) :
      focused.final.tapes (i.castAdd 3)=base.final.tapes i ∧ focused.final.heads (i.castAdd 3)=base.final.heads i := by
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,?_,?_⟩
  · intro j; fin_cases j
    · exact (retained 400 (by decide)).1.trans (bt 9)
    · exact (retained 200 (by decide)).1.trans (bt 8)
    · exact (retained 407 (by decide)).1.trans (bt 13)
    · exact (retained 394 (by decide)).1.trans rt
    · exact (localT 1).trans b1
    · exact (localT 2).trans b2
  · intro j; fin_cases j
    · exact (retained 400 (by decide)).2.trans (bh 9)
    · exact (retained 200 (by decide)).2.trans (bh 8)
    · exact (retained 407 (by decide)).2.trans (bh 13)
    · exact (retained 394 (by decide)).2.trans rh
    · exact (localH 1).trans (bodyH 1)
    · exact (localH 2).trans (bodyH 2)
  · change base.steps+1+focused.steps≤budget r
    rw [fs,bodyS]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixWilliamsHeaderEntry
