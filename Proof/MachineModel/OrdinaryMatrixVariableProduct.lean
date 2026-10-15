import Proof.MachineModel.OrdinaryMatrixVariableInput

/-! One physically indexed signed-plane call, from the original request and
its retained external offset through the corrected ordinary Williams wrapper.
Every native natural cell is returned in original row-major order. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableProduct
open LocalBitMultitape MatrixScoreBatch RepairRepresentation ExecutableInterfaces
open WilliamsLoaderForms WilliamsProductCertificate
open MatrixWilliamsProduct
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) := 425+(source a).program.tapeCount
noncomputable def slots (a : WilliamsAlgorithm) (i : Fin (source a).program.tapeCount) : Fin (tapes a) :=
  if i.val=0 then ⟨422,by unfold tapes; omega⟩ else i.natAdd 425

theorem slots_injective (a : WilliamsAlgorithm) : Function.Injective (slots a) := by
  intro i j he
  unfold slots at he
  split at he <;> split at he
  · exact Fin.ext (by omega)
  · have h := congrArg Fin.val he; simp only [Fin.val_natAdd] at h; omega
  · have h := congrArg Fin.val he; simp only [Fin.val_natAdd] at h; omega
  · have h := congrArg Fin.val he; simp only [Fin.val_natAdd] at h; exact Fin.ext (by omega)

noncomputable def first (a : WilliamsAlgorithm) (negative : Bool) := TapeEmbedding.machine (source a).program.tapeCount (MatrixVariableInput.machine negative)
noncomputable def last (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots a) (source a).program.machine
noncomputable def machine (a : WilliamsAlgorithm) (negative : Bool) := Composition.machine (first a negative) (last a)
noncomputable def input (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) :=
  Composition.leftConfig (source a).program.stateCount
    (TapeEmbedding.config (fun _ : Fin (source a).program.tapeCount => 0)
      (fun _ : Fin (source a).program.tapeCount => []) (MatrixVariableInput.input r bit))
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) := MatrixVariableInput.budget r+1+sourceBudget a r
noncomputable def outputTape (a : WilliamsAlgorithm) := slots a (source a).program.outputTape

theorem call_run {s : ℕ} (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ)
    (c : Configuration (tapes a) s)
    (ct : ∀ j,c.tapes (slots a j)=(source a).program.inputTapes
      (natWord r.U++MatrixSignedPlane.plane r negative bit++MatrixRightPlaneNative.plane r) j)
    (ch : ∀ j,c.heads (slots a j)=0) : ∃ actual,
    runFrom (last a) (sourceBudget a r) (Composition.restart c (last a).start)=some actual ∧
    actual.final.tapes (outputTape a)=planeCounts r negative bit ∧ actual.final.heads (outputTape a)=0 ∧
    (∀ i : Fin 425,i.val≠422 → actual.final.tapes (i.castAdd (source a).program.tapeCount)=c.tapes (i.castAdd (source a).program.tapeCount) ∧
      actual.final.heads (i.castAdd (source a).program.tapeCount)=c.heads (i.castAdd (source a).program.tapeCount)) ∧
    actual.steps≤ sourceBudget a r := by
  obtain ⟨body,hr,bodyT,bodyH,bodyS⟩ := source_run a r negative bit
  let entry := initialConfiguration (source a).program.machine ((source a).program.inputTapes
    (natWord r.U++MatrixSignedPlane.plane r negative bit++MatrixRightPlaneNative.plane r))
  have hi : RecoveryFocus.config (slots a) c.heads c.tapes entry=Composition.restart c (last a).start :=
    WilliamsSourceCrop.focus_same (slots a) c entry ch ct
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config (slots a) (slots_injective a) (source a).program.machine
    c.heads c.tapes _ entry body hr
  rw [hi] at hf
  refine ⟨focused,hf,?_,?_,?_,fs.trans_le bodyS⟩
  · rw [ff]
    simpa only [outputTape,RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a)] using bodyT
  · rw [ff]
    simp only [outputTape,RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a),bodyH]
  · intro i hi
    have hn : ∀ j,slots a j≠i.castAdd (source a).program.tapeCount := by
      intro j hj
      unfold slots at hj
      split at hj
      · have h := congrArg Fin.val hj; simp only [Fin.val_castAdd] at h; omega
      · have h := congrArg Fin.val hj; simp only [Fin.val_natAdd,Fin.val_castAdd] at h; omega
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hn]

theorem selected_ne (j : Fin 10) : (MatrixVariableDimensions.selected j).val≠422 := by
  fin_cases j <;> decide

theorem product_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) (ht : bit<r.p) : ∃ actual,
    runFrom (machine a negative) (budget a r) (input a r bit)=some actual ∧
    actual.final.tapes (outputTape a)=planeCounts r negative bit ∧ actual.final.heads (outputTape a)=0 ∧
    (∀ j,actual.final.tapes ((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount)=MatrixVariableDimensions.values r negative bit j) ∧
    (∀ j,actual.final.heads ((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount)=MatrixVariableDimensions.heads j) ∧
    actual.steps≤budget a r := by
  obtain ⟨base,hb,inputT,inputH,bt,bh,bs⟩ := MatrixVariableInput.input_run r negative bit ht
  have hemb := TapeEmbedding.run_embed (MatrixVariableInput.machine negative) (fun _ : Fin (source a).program.tapeCount => 0)
    (fun _ : Fin (source a).program.tapeCount => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin (source a).program.tapeCount => 0)
    (fun _ : Fin (source a).program.tapeCount => []) base
  have embeddedT (i : Fin 425) : prepared.final.tapes (i.castAdd (source a).program.tapeCount)=base.final.tapes i := by
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have embeddedH (i : Fin 425) : prepared.final.heads (i.castAdd (source a).program.tapeCount)=base.final.heads i := by
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  obtain ⟨focused,hf,ft,fh,old,steps⟩ := call_run a r negative bit prepared.final
    (by
      intro j
      by_cases hz : j.val=0
      · simp only [slots,hz,if_pos,Program.inputTapes]
        exact (embeddedT 422).trans inputT
      · simp [slots,hz,Program.inputTapes,prepared,TapeEmbedding.receipt,TapeEmbedding.config])
    (by
      intro j
      by_cases hz : j.val=0
      · simp only [slots,hz,if_pos]
        exact (embeddedH 422).trans inputH
      · simp [slots,hz,prepared,TapeEmbedding.receipt,TapeEmbedding.config])
  have hj := Composition.run_join (first a negative) (last a) _ _ _ prepared focused hemb hf
  refine ⟨Composition.joinedReceipt prepared focused,hj,ft,fh,?_,?_,?_⟩
  · intro j
    exact (old _ (selected_ne j)).1.trans ((embeddedT _).trans (bt j))
  · intro j
    exact (old _ (selected_ne j)).2.trans ((embeddedH _).trans (bh j))
  · change base.steps+1+focused.steps≤budget a r
    unfold budget
    omega

theorem budget_eq (a : WilliamsAlgorithm) (r : Request) : budget a r=MatrixWilliamsProduct.budget a r := rfl

end NearCubicWires.RepairOrdinary.MatrixVariableProduct
