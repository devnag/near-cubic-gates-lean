import Proof.MachineModel.OrdinaryMatrixCoefficient

/-! A single original request now produces its signed coefficient bank and
both Boolean matrices. The coefficient pass runs once; the existing whole
matrix producer then runs on the retained original input and fresh work,
preserving the coefficient bank at head zero. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchCoefficientPlanes
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 362) : Fin 396 := if i.val=0 then 0 else ⟨i.val+34,by omega⟩
theorem slots_zero : slots 0=0 := rfl
theorem slots_succ (j : Fin 361) : slots j.succ=j.natAdd 35 := by
  apply Fin.ext
  simp [slots]
  omega
theorem slots_injective : Function.Injective slots := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_zero] at hv <;> omega
noncomputable def first := TapeEmbedding.machine 361 MatrixCoefficientCold.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBatchRightPlane.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 396 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixCoefficientCold.budget r+1+MatrixBatchRightPlane.budget r

theorem raw_run (r : Request) : ∃ base,∃ actual,
    run MatrixCoefficientCold.machine (MatrixCoefficientCold.budget r) (MatrixCoefficientCold.input r)=some base ∧
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes (slots 342)=MatrixBucketLeftPlane.plane r ∧ actual.final.heads (slots 342)=0 ∧
    actual.final.tapes (slots 360)=MatrixRightPlaneNative.plane r ∧ actual.final.heads (slots 360)=0 ∧
    actual.final.tapes 33=MatrixCoefficientLoop.output r.p r.cuts ∧ actual.final.heads 33=0 ∧
    (∀ i : Fin 35,i≠0 → actual.final.tapes (i.castAdd 361)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 361)=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt0,bank,bh,bs⟩ := MatrixCoefficientCold.cold_run r
  have he := TapeEmbedding.run_embed MatrixCoefficientCold.machine (fun _ : Fin 361 => 0)
    (fun _ : Fin 361 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 361 => 0) (fun _ : Fin 361 => []) base
  obtain ⟨_,body,_,hbody,rightT,rightH,leftT,leftH,_,_,bodyS⟩ := MatrixBatchRightPlane.raw_run r
  let entry := initialConfiguration MatrixBatchRightPlane.machine (MatrixBatchRightPlane.input r)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa [slots_zero,prepared,TapeEmbedding.receipt,TapeEmbedding.config,entry,initialConfiguration,Fin.addCases] using bh 0
      · simp [slots_succ,prepared,TapeEmbedding.receipt,TapeEmbedding.config,entry,initialConfiguration]
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa [slots_zero,prepared,TapeEmbedding.receipt,TapeEmbedding.config,entry,initialConfiguration,
          MatrixBatchRightPlane.input,Fin.addCases] using bt0
      · simp [slots_succ,prepared,TapeEmbedding.receipt,TapeEmbedding.config,entry,initialConfiguration,
          MatrixBatchRightPlane.input]
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBatchRightPlane.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 361 => 0) (fun _ : Fin 361 => [])
      (initialConfiguration MatrixCoefficientCold.machine (MatrixCoefficientCold.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 35) (n := 361) ?_ ?_ i
      · intro j; simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
      · intro j; simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · funext i
      refine Fin.addCases (m := 35) (n := 361) ?_ ?_ i
      · intro j
        have hz : (j.castAdd 361 : Fin 396)=0 ↔ j=0 := by
          constructor
          · intro h; apply Fin.ext; have hv := congrArg (fun k : Fin 396 => k.val) h; exact hv
          · intro h; subst j; rfl
        simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,MatrixCoefficientCold.input,input,hz]
      · intro j
        have hz : (j.natAdd 35 : Fin 396)≠0 := by
          intro h; have hv := congrArg Fin.val h; change 35+j.val=0 at hv; omega
        simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,input,hz]
  rw [hin] at hj
  have pick (j : Fin 362) : RecoveryFocus.pick slots (slots j)=some j := RecoveryFocus.pick_slot slots slots_injective j
  have localT (j : Fin 362) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]
    simp only [RecoveryFocus.config,pick]
  have localH (j : Fin 362) : focused.final.heads (slots j)=body.final.heads j := by
    rw [ff]
    simp only [RecoveryFocus.config,pick]
  have old (i : Fin 35) (hi : i≠0) : focused.final.tapes (i.castAdd 361)=base.final.tapes i ∧
      focused.final.heads (i.castAdd 361)=0 := by
    have hn : RecoveryFocus.pick slots (i.castAdd 361)=none := by
      simp only [RecoveryFocus.pick]
      split
      · next h =>
        obtain ⟨j,hj⟩ := h
        have hv := congrArg Fin.val hj
        have hiv : i.val≠0 := by
          intro h; apply hi; apply Fin.ext; exact h
        simp only [slots] at hv
        split_ifs at hv <;> simp only [Fin.val_zero,Fin.val_castAdd] at hv <;> omega
      · rfl
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config,bh]
  have oldBank := old 33 (by decide)
  refine ⟨base,Composition.joinedReceipt prepared focused,hb,hj,(localT 342).trans leftT,
    (localH 342).trans leftH,(localT 360).trans rightT,(localH 360).trans rightH,
    oldBank.1.trans bank,oldBank.2,old,?_⟩
  change base.steps+1+focused.steps≤budget r
  rw [fs]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixBatchCoefficientPlanes
