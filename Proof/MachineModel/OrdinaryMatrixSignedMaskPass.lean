import Proof.MachineModel.OrdinaryMatrixSignedMaskPrepare

/-! The complete ordinary signed-plane pass consumes the actual canonical
coefficient bank and retained unweighted matrix. It executes bit extraction,
bucket expansion, zero padding and every matrix AND, retaining row order. -/
namespace NearCubicWires.RepairOrdinary.MatrixSignedMaskPass
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 6 → Fin 15 := ![8,11,10,13,9,14]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first (negative : Bool) := TapeEmbedding.machine 2 (MatrixSignedMaskPrepare.machine negative)
noncomputable def last := RecoveryFocus.machine slots MatrixMaskAndPass.machine
noncomputable def machine (negative : Bool) := Composition.machine (first negative) last
noncomputable def input (r : Request) (negative flag : Bool) (t : ℕ) :=
  Composition.leftConfig (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (2+3))+2)
    (TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) (MatrixSignedMaskPrepare.input r negative flag t))
def budget (r : Request) := MatrixSignedMaskPrepare.budget r+1+MatrixSignedPlane.budget r
noncomputable def output (r : Request) (negative flag : Bool) (t nb nm na : ℕ) : Fin 15 → List Bool :=
  Fin.addCases (m := 13) (n := 2) (motive := fun _ => List Bool) (MatrixSignedMaskPrepare.output r negative flag t nb nm)
    ![MatrixSignedPlane.plane r negative t,List.replicate na false]
def finalHeads (r : Request) : Fin 15 → ℕ :=
  Fin.addCases (m := 13) (n := 2) (motive := fun _ => ℕ) (MatrixSignedMaskPrepare.finalHeads r) (fun _ => 0)

theorem plane_run (r : Request) (negative flag : Bool) (t : ℕ) (ht : t<r.p) : ∃ nb nm na,∃ actual,
    runFrom (machine negative) (budget r) (input r negative flag t)=some actual ∧
    actual.final.tapes=output r negative flag t nb nm na ∧ actual.final.heads=finalHeads r ∧
    nb≤MatrixCoefficientBitNative.budget r ∧ nm≤MatrixMaskPad.forwardBudget r.Buckets (r.Capacity-r.Used) r.Gates ∧
    na≤MatrixMaskAndLoop.nativeBudget r.Capacity r.U ∧ actual.steps≤budget r := by
  obtain ⟨nb,nm,base,hb,bt,bh,nbound,nmbound,bs⟩ := MatrixSignedMaskPrepare.mask_run r negative flag t ht
  have he := TapeEmbedding.run_embed (MatrixSignedMaskPrepare.machine negative) (fun _ : Fin 2 => 0)
    (fun _ : Fin 2 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base
  obtain ⟨body,hr,rt,rh,rlh,⟨na,rlt,nabound⟩,rs⟩ := MatrixSignedPlane.plane_run r negative t
  let entry := MatrixSignedPlane.input r negative t
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      dsimp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
      rw [bh]
      fin_cases j <;> rfl
    · intro j
      dsimp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
      rw [bt]
      fin_cases j
      all_goals simp [slots,entry,MatrixSignedPlane.input,MatrixMaskAndPass.input,
        Rewind.recording,Rewind.config,MatrixMaskAndLoop.native_tapes,MatrixSignedMaskPrepare.output,
        MatrixMaskSemantics.mask_length,MatrixSignedPlane.rows_length,MatrixSignedPlane.rows_flatten,Fin.addCases]
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixMaskAndPass.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join (first negative) last _ _ _ prepared focused he hf
  have pick (i : Fin 15) : RecoveryFocus.pick slots i=
      (![none,none,none,none,none,none,none,none,some 0,some 4,some 2,some 1,none,some 3,some 5] : Fin 15 → Option (Fin 6)) i := by
    fin_cases i <;> first | decide | exact RecoveryFocus.pick_slot slots slots_injective 0 | exact RecoveryFocus.pick_slot slots slots_injective 1 | exact RecoveryFocus.pick_slot slots slots_injective 2 | exact RecoveryFocus.pick_slot slots slots_injective 3 | exact RecoveryFocus.pick_slot slots slots_injective 4 | exact RecoveryFocus.pick_slot slots slots_injective 5
  have rt' (i : Fin 6) : body.final.tapes i=
      (![UnaryTemplate.tape r.Capacity,MatrixMaskSemantics.mask r negative t,MatrixBucketLeftPlane.plane r,
        MatrixSignedPlane.plane r negative t,UnaryTemplate.tape r.U,List.replicate na false] : Fin 6 → List Bool) i := by
    fin_cases i <;> first | exact rt 0 | exact rt 1 | exact rt 2 | exact rt 3 | exact rt 4 | exact rlt
  have rh' (i : Fin 6) : body.final.heads i=(![1,0,0,0,1,0] : Fin 6 → ℕ) i := by
    fin_cases i <;> first | exact rh 0 | exact rh 1 | exact rh 2 | exact rh 3 | exact rh 4 | exact rlh
  refine ⟨nb,nm,na,Composition.joinedReceipt prepared focused,hj,?_,?_,nbound,nmbound,nabound,?_⟩
  · change focused.final.tapes=_
    rw [ff]
    funext i
    simp only [RecoveryFocus.config,pick]
    dsimp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [bt]
    fin_cases i <;> simp [rt',output,MatrixSignedMaskPrepare.output,Fin.addCases]
  · change focused.final.heads=_
    rw [ff]
    funext i
    simp only [RecoveryFocus.config,pick]
    dsimp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [bh]
    fin_cases i <;> simp [rh',finalHeads,MatrixSignedMaskPrepare.finalHeads,Fin.addCases]
  · change base.steps+1+focused.steps≤budget r
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixSignedMaskPass
