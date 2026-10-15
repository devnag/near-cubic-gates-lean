import Proof.MachineModel.OrdinaryMatrixFirstSignedPlane

/-! The retained scalar source fields of the same first-plane entry. The
Williams input serializer consumes its physical d sentinel and both native
U fields; no dimensions are installed from semantic values. -/
namespace NearCubicWires.RepairOrdinary.MatrixSignedEntryRetained
open LocalBitMultitape MatrixScoreBatch MatrixSignedEntry
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem retained_run (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    (∀ j,actual.final.tapes (((MatrixSignedSourceFields.slots j).castAdd 5).castAdd 8)=MatrixSignedSourceFields.values r j) ∧
    (∀ j,actual.final.heads (((MatrixSignedSourceFields.slots j).castAdd 5).castAdd 8)=
      if j=1 ∨ j=2 ∨ j=4 ∨ j=5 ∨ j=6 then 1 else 0) ∧
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
  refine ⟨Composition.joinedReceipt prepared body,hj,oldT,oldH,?_⟩
  change base.steps+1+body.steps≤budget r
  rw [bodyS]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixSignedEntryRetained
