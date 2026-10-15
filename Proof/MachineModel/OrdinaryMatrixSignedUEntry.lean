import Proof.MachineModel.OrdinaryMatrixSignedSourceFields

/-! Paid materialization of a reusable U sentinel from the retained binary
U and its physical native width. All previous tapes and cursors survive;
the extra U driver will also serve the required odd-residual row slice. -/
namespace NearCubicWires.RepairOrdinary.MatrixSignedUEntry
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7 → Fin 401 := ![259,396,397,398,399,66,400]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 5 MatrixBatchCoefficientPlanes.machine
noncomputable def last := RecoveryFocus.machine slots MatrixUnaryTemplate.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 401 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixBatchCoefficientPlanes.budget r+1+MatrixUnaryTemplate.budget r.M r.U

theorem u_run (r : Request) (base : ExecutionReceipt 396 _)
    (hb : run MatrixBatchCoefficientPlanes.machine (MatrixBatchCoefficientPlanes.budget r) (MatrixBatchCoefficientPlanes.input r)=some base)
    (bt : ∀ j,base.final.tapes (MatrixSignedSourceFields.slots j)=MatrixSignedSourceFields.values r j)
    (bh : ∀ j,base.final.heads (MatrixSignedSourceFields.slots j)=0)
    (bs : base.steps≤MatrixBatchCoefficientPlanes.budget r) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 400=UnaryTemplate.tape r.U ∧ actual.final.heads 400=1 ∧
    (∀ i : Fin 396,actual.final.tapes (i.castAdd 5)=base.final.tapes i ∧
      actual.final.heads (i.castAdd 5)=base.final.heads i) ∧ actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchCoefficientPlanes.machine (fun _ : Fin 5 => 0)
    (fun _ : Fin 5 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base
  have hu : 0<r.U := by exact Nat.two_pow_pos r.d
  have hfit : r.U<2^r.M := by have hh := MatrixScoreRawRanks.size_fit r; omega
  obtain ⟨body,hr,wT,uT,outT,outH,rh,rs⟩ := MatrixUnaryTemplate.template_run r.M r.U hfit
  let entry := initialConfiguration MatrixUnaryTemplate.machine (MatrixUnaryTemplate.input r.M r.U)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · exact bh 7
      · rfl
      · rfl
      · rfl
      · rfl
      · exact bh 8
      · rfl
    · intro j
      fin_cases j
      · exact bt 7
      · rfl
      · rfl
      · rfl
      · rfl
      · exact bt 8
      · rfl
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixUnaryTemplate.machine
    prepared.final.heads prepared.final.tapes _ entry body hr
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => [])
      (initialConfiguration MatrixBatchCoefficientPlanes.machine (MatrixBatchCoefficientPlanes.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have localT (j : Fin 7) : focused.final.tapes (slots j)=body.final.tapes j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 7) : focused.final.heads (slots j)=body.final.heads j := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  refine ⟨Composition.joinedReceipt prepared focused,hj,(localT 6).trans outT,(localH 6).trans outH,?_,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 5)=base.final.tapes i ∧ focused.final.heads (i.castAdd 5)=base.final.heads i
    by_cases hi259 : i=259
    · subst i
      exact ⟨(localT 0).trans (wT.trans (bt 7).symm),(localH 0).trans ((rh 0 (by decide)).trans (bh 7).symm)⟩
    by_cases hi66 : i=66
    · subst i
      exact ⟨(localT 5).trans (uT.trans (bt 8).symm),(localH 5).trans ((rh 5 (by decide)).trans (bh 8).symm)⟩
    have hn : ∀ j,slots j≠i.castAdd 5 := by
      intro j
      have h259 : i.val≠259 := fun h => hi259 (Fin.ext h)
      have h66 : i.val≠66 := fun h => hi66 (Fin.ext h)
      fin_cases j <;> simp [slots,Fin.ext_iff] <;> omega
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change base.steps+1+focused.steps≤budget r
    rw [fs]
    unfold budget
    omega

theorem raw_run (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 400=UnaryTemplate.tape r.U ∧ actual.final.heads 400=1 ∧
    (∀ j,actual.final.tapes ((MatrixSignedSourceFields.slots j).castAdd 5)=MatrixSignedSourceFields.values r j) ∧
    (∀ j,actual.final.heads ((MatrixSignedSourceFields.slots j).castAdd 5)=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bh,bs⟩ := MatrixSignedSourceFields.source_fields r
  obtain ⟨actual,ha,ut,uh,old,steps⟩ := u_run r base hb bt bh bs
  exact ⟨actual,ha,ut,uh,fun j => (old _).1.trans (bt j),fun j => (old _).2.trans (bh j),steps⟩

end NearCubicWires.RepairOrdinary.MatrixSignedUEntry
