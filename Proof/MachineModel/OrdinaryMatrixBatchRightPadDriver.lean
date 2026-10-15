import Proof.MachineModel.OrdinaryMatrixRightDimensions
import Proof.MachineModel.OrdinaryMatrixRightPlaneNative

/-! The right-plane pad-bit driver is physically multiplied from the
retained Capacity-Used and U templates. All preceding tapes and heads,
including both aggregate streams and the left matrix, are preserved. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightPadDriver
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 12 → Fin 358 := ![287,348,349,350,351,39,352,353,354,355,356,357]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 10 MatrixBatchRightPass.machine
noncomputable def last := RecoveryFocus.machine slots MatrixTemplateProduct.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 358 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixBatchRightPass.budget r+1+
  (8*(r.Capacity-r.Used)*r.U+10*(r.Capacity-r.Used)+28)

theorem product_run (r : Request) (base : ExecutionReceipt 348 _)
    (hb : run MatrixBatchRightPass.machine (MatrixBatchRightPass.budget r) (MatrixBatchRightPass.input r)=some base)
    (b287 : base.final.tapes 287=UnaryTemplate.tape (r.Capacity-r.Used)) (h287 : base.final.heads 287=0)
    (b39 : base.final.tapes 39=UnaryTemplate.tape r.U) (h39 : base.final.heads 39=0)
    (bs : base.steps≤MatrixBatchRightPass.budget r) : ∃ actual,
      run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 356=UnaryTemplate.tape ((r.Capacity-r.Used)*r.U) ∧ actual.final.heads 356=0 ∧
      (∀ i : Fin 348,actual.final.tapes (i.castAdd 10)=base.final.tapes i ∧
        actual.final.heads (i.castAdd 10)=base.final.heads i) ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchRightPass.machine (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base
  obtain ⟨body,hr,t0,t5,t10,rh,rs⟩ := MatrixTemplateProduct.product_run (r.Capacity-r.Used) r.U
  let entry := initialConfiguration MatrixTemplateProduct.machine (MatrixTemplateProduct.input (r.Capacity-r.Used) r.U)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j <;> first | exact h287 | exact h39 | rfl
    · intro j
      fin_cases j <;> first | exact b287 | exact b39 | rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixTemplateProduct.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
      (initialConfiguration MatrixBatchRightPass.machine (MatrixBatchRightPass.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localT (j : Fin 12) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 12) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,rh]
  refine ⟨Composition.joinedReceipt prepared focused,hj,(localT 10).trans t10,localH 10,?_,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 10)=_ ∧ focused.final.heads (i.castAdd 10)=_
    by_cases hi287 : i=287
    · subst i
      exact ⟨(localT 0).trans (t0.trans b287.symm),(localH 0).trans h287.symm⟩
    by_cases hi39 : i=39
    · subst i
      exact ⟨(localT 5).trans (t5.trans b39.symm),(localH 5).trans h39.symm⟩
    have hn : ∀ j,slots j≠i.castAdd 10 := by
      intro j
      have hv287 : i.val≠287 := fun h => hi287 (Fin.ext h)
      have hv39 : i.val≠39 := fun h => hi39 (Fin.ext h)
      fin_cases j <;> simp [slots,Fin.ext_iff] <;> omega
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change base.steps+1+body.steps≤budget r
    rw [rs]
    unfold budget
    omega

theorem raw_run (r : Request) : ∃ base : ExecutionReceipt 348 _,∃ actual,
    run MatrixBatchRightPass.machine (MatrixBatchRightPass.budget r) (MatrixBatchRightPass.input r)=some base ∧
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 356=UnaryTemplate.tape ((r.Capacity-r.Used)*r.U) ∧ actual.final.heads 356=0 ∧
    (∀ i : Fin 348,actual.final.tapes (i.castAdd 10)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 10)=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixRightDimensions.source_fields r
  obtain ⟨actual,ha,t,h,old,steps⟩ := product_run r base hb (bt 1) (bh 1) (bt 2) (bh 2) bs
  exact ⟨base,actual,hb,ha,t,h,old,steps⟩

end NearCubicWires.RepairOrdinary.MatrixBatchRightPadDriver
