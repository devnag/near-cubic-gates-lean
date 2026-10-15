import Proof.MachineModel.OrdinaryMatrixSignedBootstrap

/-! Literal first-plane entry from the original framed Request and blank
work. Every signed-pass input is supplied by executed parsing, dimensions,
matrix/coefficients production and the paid two-transition bootstrap. -/
namespace NearCubicWires.RepairOrdinary.MatrixSignedEntry
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 15 → Fin 409 := ![33,401,402,403,32,404,256,321,200,400,376,405,406,407,408]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 8 MatrixSignedUEntry.machine
noncomputable def machine := Composition.machine first MatrixSignedBootstrap.machine
def input (r : Request) : Fin 409 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixSignedUEntry.budget r+3
noncomputable def entry (r : Request) := MatrixSignedMaskPass.input r false false 0

theorem entry_tapes (r : Request) : (entry r).tapes=
    ![MatrixCoefficientLoop.output r.p r.cuts,UnaryTemplate.tape 0,[false],[],UnaryTemplate.tape r.Gates,[],
      UnaryTemplate.tape r.Buckets,UnaryTemplate.tape (r.Capacity-r.Used),UnaryTemplate.tape r.Capacity,
      UnaryTemplate.tape r.U,MatrixBucketLeftPlane.plane r,[],[],[],[]] := by
  funext j
  fin_cases j
  all_goals simp [entry,MatrixSignedMaskPass.input,MatrixSignedMaskPrepare.input,Composition.leftConfig,TapeEmbedding.config,
    MatrixCoefficientBitPass.input,Rewind.recording,Rewind.config,MatrixCoefficientBitNative.cfg_tapes,
    MatrixSignedMaskPrepare.extraTapes,Fin.addCases]

theorem entry_heads (r : Request) : (entry r).heads=(![0,1,0,0,1,0,1,1,1,1,0,0,0,0,0] : Fin 15 → ℕ) := by
  funext j; fin_cases j <;> rfl

theorem raw_run (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    (∀ j,actual.final.tapes (slots j)=(entry r).tapes j) ∧
    (∀ j,actual.final.heads (slots j)=(entry r).heads j) ∧
    actual.final.tapes 22=UnaryTemplate.tape r.p ∧ actual.final.heads 22=1 ∧
    actual.final.tapes 394=MatrixRightPlaneNative.plane r ∧ actual.final.heads 394=0 ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,uT,uH,bt,bh,bs⟩ := MatrixSignedUEntry.raw_run r
  have he := TapeEmbedding.run_embed MatrixSignedUEntry.machine (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) base
  obtain ⟨body,hr,bf,bodyS⟩ := MatrixSignedBootstrap.boot_run prepared.final (by rfl) (by rfl) (by rfl) (by rfl)
  have hj := Composition.run_join first MatrixSignedBootstrap.machine _ _ _ prepared body he hr
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 8 => 0) (fun _ : Fin 8 => [])
      (initialConfiguration MatrixSignedUEntry.machine (MatrixSignedUEntry.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have hbudget : MatrixSignedUEntry.budget r+1+2=budget r := by unfold budget; omega
  rw [hbudget] at hj
  have oldT (j : Fin 11) : body.final.tapes (((MatrixSignedSourceFields.slots j).castAdd 5).castAdd 8)=MatrixSignedSourceFields.values r j := by
    rw [bf]
    have h401 : (((MatrixSignedSourceFields.slots j).castAdd 5).castAdd 8 : Fin 409)≠401 := by fin_cases j <;> decide
    have h402 : (((MatrixSignedSourceFields.slots j).castAdd 5).castAdd 8 : Fin 409)≠402 := by fin_cases j <;> decide
    simpa [MatrixSignedBootstrap.final,MatrixSignedBootstrap.middle,h401,h402,prepared,TapeEmbedding.receipt,
      TapeEmbedding.config] using bt j
  have oldH (j : Fin 11) : body.final.heads (((MatrixSignedSourceFields.slots j).castAdd 5).castAdd 8)=
      (if j=1 ∨ j=2 ∨ j=4 ∨ j=5 ∨ j=6 then 1 else 0) := by
    rw [bf]
    simp only [MatrixSignedBootstrap.final,MatrixSignedBootstrap.middle,prepared,TapeEmbedding.receipt,
      TapeEmbedding.config,Fin.addCases_left]
    rw [bh j]
    fin_cases j <;> rfl
  refine ⟨Composition.joinedReceipt prepared body,hj,?_,?_,oldT 1,oldH 1,oldT 10,oldH 10,?_⟩
  · intro j
    change body.final.tapes (slots j)=_
    rw [entry_tapes]
    fin_cases j
    · exact oldT 3
    · rw [bf]; rfl
    · rw [bf]; rfl
    · rw [bf]; rfl
    · exact oldT 2
    · rw [bf]; rfl
    · exact oldT 5
    · exact oldT 6
    · exact oldT 4
    · rw [bf]
      exact uT
    · exact oldT 9
    · rw [bf]; rfl
    · rw [bf]; rfl
    · rw [bf]; rfl
    · rw [bf]; rfl
  · intro j
    change body.final.heads (slots j)=_
    rw [entry_heads]
    fin_cases j
    · exact oldH 3
    · rw [bf]; rfl
    · rw [bf]; rfl
    · rw [bf]; rfl
    · exact oldH 2
    · rw [bf]; rfl
    · exact oldH 5
    · exact oldH 6
    · exact oldH 4
    · rw [bf]
      exact uH
    · exact oldH 9
    · rw [bf]; rfl
    · rw [bf]; rfl
    · rw [bf]; rfl
    · rw [bf]; rfl
  · change base.steps+1+body.steps≤budget r
    rw [bodyS]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixSignedEntry
