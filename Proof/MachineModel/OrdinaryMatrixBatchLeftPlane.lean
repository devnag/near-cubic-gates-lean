import Proof.MachineModel.OrdinaryMatrixBatchLeftFields

/-! Original framed Request and blank work through the complete unweighted
left plane. The same execution supplies every dimension and source field. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchLeftPlane
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 6 → Fin 344 := ![314,342,285,287,39,343]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 2 MatrixBatchCoordinateSort.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBucketLeftPlane.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 344 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixBatchCoordinateSort.budget r+1+MatrixBucketLeftPlane.budget r

theorem plane_run (r : Request) (base : ExecutionReceipt 342 _)
    (hb : run MatrixBatchCoordinateSort.machine (MatrixBatchCoordinateSort.budget r) (MatrixBatchCoordinateSort.input r)=some base)
    (b314 : base.final.tapes 314=MatrixBucketCoordinateSort.output r) (h314 : base.final.heads 314=0)
    (b285 : base.final.tapes 285=UnaryTemplate.tape r.Used) (h285 : base.final.heads 285=0)
    (b287 : base.final.tapes 287=UnaryTemplate.tape (r.Capacity-r.Used)) (h287 : base.final.heads 287=0)
    (b39 : base.final.tapes 39=UnaryTemplate.tape r.U) (h39 : base.final.heads 39=0)
    (bs : base.steps≤MatrixBatchCoordinateSort.budget r) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 342=MatrixBucketLeftPlane.plane r ∧ actual.final.heads 342=0 ∧
    (∀ i : Fin 342,actual.final.tapes (i.castAdd 2)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 2)=base.final.heads i) ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchCoordinateSort.machine (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base
  obtain ⟨body,hr,t0,t1,t2,t3,t4,rh,rs⟩ := MatrixBucketLeftPlane.plane_run r
  let entry := initialConfiguration MatrixBucketLeftPlane.machine (MatrixBucketLeftPlane.input r)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · exact h314
      · rfl
      · exact h285
      · exact h287
      · exact h39
      · rfl
    · intro j
      fin_cases j
      · exact b314
      · rfl
      · exact b285
      · exact b287
      · exact b39
      · rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBucketLeftPlane.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => [])
      (initialConfiguration MatrixBatchCoordinateSort.machine (MatrixBatchCoordinateSort.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localT (j : Fin 6) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 6) : focused.final.heads (slots j)=0 := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact rh j
  refine ⟨Composition.joinedReceipt prepared focused,hj,(localT 1).trans t1,localH 1,?_,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 2)=_ ∧ focused.final.heads (i.castAdd 2)=_
    by_cases hi314 : i=314
    · subst i; exact ⟨(localT 0).trans (t0.trans b314.symm),(localH 0).trans h314.symm⟩
    by_cases hi285 : i=285
    · subst i; exact ⟨(localT 2).trans (t2.trans b285.symm),(localH 2).trans h285.symm⟩
    by_cases hi287 : i=287
    · subst i; exact ⟨(localT 3).trans (t3.trans b287.symm),(localH 3).trans h287.symm⟩
    by_cases hi39 : i=39
    · subst i; exact ⟨(localT 4).trans (t4.trans b39.symm),(localH 4).trans h39.symm⟩
    have hn : ∀ j,slots j≠i.castAdd 2 := by
      intro j
      have hil := i.isLt
      have v314 : i.val≠314 := fun h => hi314 (Fin.ext h)
      have v285 : i.val≠285 := fun h => hi285 (Fin.ext h)
      have v287 : i.val≠287 := fun h => hi287 (Fin.ext h)
      have v39 : i.val≠39 := fun h => hi39 (Fin.ext h)
      fin_cases j <;> simp [slots,Fin.ext_iff] <;> omega
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [fs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) : ∃ base : ExecutionReceipt 342 _,∃ actual,
    run MatrixBatchCoordinateSort.machine (MatrixBatchCoordinateSort.budget r) (MatrixBatchCoordinateSort.input r)=some base ∧
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 342=MatrixBucketLeftPlane.plane r ∧ actual.final.heads 342=0 ∧
    (∀ i : Fin 342,actual.final.tapes (i.castAdd 2)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 2)=base.final.heads i) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,b314,h314,b285,h285,b287,h287,b39,h39,bs⟩ := MatrixBatchLeftFields.source_fields r
  obtain ⟨actual,ha,outputT,ah,old,steps⟩ := plane_run r base hb b314 h314 b285 h285 b287 h287 b39 h39 bs
  exact ⟨base,actual,hb,ha,outputT,ah,old,steps⟩

end NearCubicWires.RepairOrdinary.MatrixBatchLeftPlane
