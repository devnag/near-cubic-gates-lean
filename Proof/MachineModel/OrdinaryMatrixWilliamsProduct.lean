import Proof.MachineModel.OrdinaryMatrixWilliamsInput
import Proof.MachineModel.OrdinaryWilliamsCeilRealization

/-! The actual ordinary producer now calls the corrected Williams source
wrapper and pays a complete return scan. Native count cells retain their
original row-major order and exact natural values. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsProduct
open LocalBitMultitape MatrixScoreBatch RepairRepresentation ExecutableInterfaces
open WilliamsLoaderForms WilliamsProductCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def request (r : Request) (negative : Bool) (bit : ℕ) : RectangularProductRequest where
  dimension := r.U
  left := fun row inner => LeftPlaneCell.coefficientBit negative (signedLeft r row inner) bit
  right := booleanRight r
noncomputable def source (a : WilliamsAlgorithm) := (WilliamsCall.realization a).wrapper.reset
noncomputable def sourceBudget (a : WilliamsAlgorithm) (r : Request) := 2*WilliamsCall.budget a (request r false 0)+2

theorem source_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) : ∃ actual,
    run (source a).program.machine (sourceBudget a r)
      ((source a).program.inputTapes (RepairRepresentation.natWord r.U++MatrixSignedPlane.plane r negative bit++MatrixRightPlaneNative.plane r))=some actual ∧
    actual.final.tapes (source a).program.outputTape=planeCounts r negative bit ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤ sourceBudget a r := by
  obtain ⟨actual,ha,ho⟩ := (source a).realizes (request r negative bit)
  have hh := (source a).headsReset (request r negative bit) actual ha
  exact ⟨actual,ha,ho,hh,runFrom_steps_le _ _ _ _ ha⟩

noncomputable def tapes (a : WilliamsAlgorithm) := 424+(source a).program.tapeCount
noncomputable def slots (a : WilliamsAlgorithm) (i : Fin (source a).program.tapeCount) : Fin (tapes a) :=
  if i.val=0 then ⟨422,by unfold tapes; omega⟩ else i.natAdd 424

theorem slots_injective (a : WilliamsAlgorithm) : Function.Injective (slots a) := by
  intro i j he
  unfold slots at he
  split at he <;> split at he
  · exact Fin.ext (by omega)
  · have h := congrArg Fin.val he; simp only [Fin.val_natAdd] at h; omega
  · have h := congrArg Fin.val he; simp only [Fin.val_natAdd] at h; omega
  · have h := congrArg Fin.val he; simp only [Fin.val_natAdd] at h; exact Fin.ext (by omega)

noncomputable def first (a : WilliamsAlgorithm) := TapeEmbedding.machine (source a).program.tapeCount MatrixWilliamsInput.machine
noncomputable def last (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots a) (source a).program.machine
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (first a) (last a)
noncomputable def input (a : WilliamsAlgorithm) (r : Request) : Fin (tapes a) → List Bool :=
  Fin.addCases (m := 424) (n := (source a).program.tapeCount) (motive := fun _ => List Bool) (MatrixWilliamsInput.input r) (fun _ => [])
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) := MatrixWilliamsInput.budget r+1+sourceBudget a r
noncomputable def outputTape (a : WilliamsAlgorithm) := slots a (source a).program.outputTape

theorem initial_join {t e s v : ℕ} (p : Machine t s) (q : Machine (t+e) v) (ts : Fin t → List Bool) :
    Composition.leftConfig v (TapeEmbedding.config (fun _ : Fin e => 0) (fun _ : Fin e => []) (initialConfiguration p ts))=
      initialConfiguration (Composition.machine (TapeEmbedding.machine e p) q)
        (Fin.addCases (m := t) (n := e) (motive := fun _ => List Bool) ts (fun _ => [])) := by
  apply configuration_ext
  · rfl
  · funext i
    change (Fin.addCases (m := t) (n := e) (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0)) i=0
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]
  · rfl

theorem call_run {s : ℕ} (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ)
    (c : Configuration (tapes a) s)
    (ct : ∀ j,c.tapes (slots a j)=(source a).program.inputTapes
      (natWord r.U++MatrixSignedPlane.plane r negative bit++MatrixRightPlaneNative.plane r) j)
    (ch : ∀ j,c.heads (slots a j)=0) : ∃ actual,
    runFrom (last a) (sourceBudget a r) (Composition.restart c (last a).start)=some actual ∧
    actual.final.tapes (outputTape a)=planeCounts r negative bit ∧ actual.final.heads (outputTape a)=0 ∧
    (∀ i : Fin 424,i.val≠422 → actual.final.tapes (i.castAdd (source a).program.tapeCount)=c.tapes (i.castAdd (source a).program.tapeCount) ∧
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

theorem selected_ne (j : Fin 7) : ((MatrixWilliamsDimensions.selected j).castAdd 2).val≠422 := by
  fin_cases j <;> decide

theorem raw_run (a : WilliamsAlgorithm) (r : Request) (hp : 0<r.p) : ∃ actual,
    run (machine a) (budget a r) (input a r)=some actual ∧
    actual.final.tapes (outputTape a)=planeCounts r false 0 ∧ actual.final.heads (outputTape a)=0 ∧
    (∀ j,actual.final.tapes (((MatrixWilliamsDimensions.selected j).castAdd 2).castAdd (source a).program.tapeCount)=MatrixWilliamsDimensions.values r j) ∧
    (∀ j,actual.final.heads (((MatrixWilliamsDimensions.selected j).castAdd 2).castAdd (source a).program.tapeCount)=0) ∧
    actual.steps≤budget a r := by
  obtain ⟨base,hb,inputT,inputH,bt,bh,bs⟩ := MatrixWilliamsInput.raw_run r hp
  have hemb := TapeEmbedding.run_embed MatrixWilliamsInput.machine (fun _ : Fin (source a).program.tapeCount => 0)
    (fun _ : Fin (source a).program.tapeCount => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin (source a).program.tapeCount => 0)
    (fun _ : Fin (source a).program.tapeCount => []) base
  have embeddedT (i : Fin 424) : prepared.final.tapes (i.castAdd (source a).program.tapeCount)=base.final.tapes i := by
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have embeddedH (i : Fin 424) : prepared.final.heads (i.castAdd (source a).program.tapeCount)=base.final.heads i := by
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  obtain ⟨focused,hf,ft,fh,old,steps⟩ := call_run a r false 0 prepared.final
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
  have hj := Composition.run_join (first a) (last a) _ _ _ prepared focused hemb hf
  have hin := initial_join MatrixWilliamsInput.machine (last a) (MatrixWilliamsInput.input r)
  rw [hin] at hj
  refine ⟨Composition.joinedReceipt prepared focused,hj,ft,fh,?_,?_,?_⟩
  · intro j
    exact (old _ (selected_ne j)).1.trans ((embeddedT _).trans (bt j))
  · intro j
    exact (old _ (selected_ne j)).2.trans ((embeddedH _).trans (bh j))
  · change base.steps+1+focused.steps≤budget a r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixWilliamsProduct
