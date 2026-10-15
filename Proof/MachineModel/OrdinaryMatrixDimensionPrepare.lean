import Proof.MachineModel.OrdinaryMatrixUnaryTemplate

/-! The unary dimension is computed from the value physically read from
the same header. All width drivers, the scalar zero and local scratch tapes
are outputs of the preceding executed calls. -/
namespace NearCubicWires.RepairOrdinary.MatrixDimensionPrepare
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7 → Fin 11 := ![1,6,7,8,9,4,10]
noncomputable def field : Machine 11 8 := TapeEmbedding.machine 5 MatrixDimensionField.machine
noncomputable def unary := RecoveryFocus.machine slots MatrixUnaryTemplate.machine
noncomputable def machine := Composition.machine field unary
def budget (w n : ℕ) := n*(8*w+10)+14*w+n+25
def input (source : List Bool) (pos : ℕ) : Configuration 11 8 :=
  TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => [])
    (Composition.leftConfig 4 (MatrixDimensionField.input source pos))

theorem prepare_run (pre suffix : List Bool) (w n : ℕ) (hn : n<2^w) :
    let source := pre ++ List.replicate w true ++ false :: (binary w n ++ suffix)
    ∃ r : ExecutionReceipt 11 (8+(8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes))),
      runFrom machine (budget w n) (Composition.leftConfig _ (input source pre.length))=some r ∧
      r.final.tapes 0=source ∧ r.final.heads 0=pre.length+2*w+1 ∧
      r.final.tapes 1=List.replicate w true ∧ r.final.heads 1=0 ∧
      r.final.tapes 3=UnaryTemplate.tape w ∧ r.final.heads 3=1 ∧
      r.final.tapes 4=frame (binary w n) ∧ r.final.heads 4=0 ∧
      r.final.tapes 10=UnaryTemplate.tape n ∧ r.final.heads 10=1 ∧ r.steps≤budget w n := by
  dsimp only
  let source := pre ++ List.replicate w true ++ false :: (binary w n ++ suffix)
  obtain ⟨base,hr,hf,hs⟩ := MatrixDimensionField.field_run pre (binary w n) suffix
  simp only [binary_length] at hr hf hs
  have he := TapeEmbedding.run_embed MatrixDimensionField.machine (fun _ : Fin 5 => 0)
    (fun _ : Fin 5 => []) _ _ base hr
  let ambient := TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base.final
  obtain ⟨localRun,hl,hw,hu,ht,hth,hh,hsteps⟩ := MatrixUnaryTemplate.template_run w n hn
  let entry := initialConfiguration MatrixUnaryTemplate.machine (MatrixUnaryTemplate.input w n)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry =
      Composition.restart ambient unary.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,entry,initialConfiguration,MatrixDimensionField.output,TapeEmbedding.config,Fin.addCases]
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,entry,initialConfiguration,MatrixUnaryTemplate.input,
        MatrixDimensionField.output,TapeEmbedding.config,Fin.addCases]
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide)
    MatrixUnaryTemplate.machine ambient.heads ambient.tapes _ entry localRun hl
  rw [hi] at hfocus
  have hj := Composition.run_join field unary (6*w+7) (MatrixUnaryTemplate.budget w n) _
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused he hfocus
  have htime : 6*w+7+1+MatrixUnaryTemplate.budget w n=budget w n := by
    unfold budget MatrixUnaryTemplate.budget
    omega
  rw [htime] at hj
  have hnone0 : RecoveryFocus.pick slots (0 : Fin 11)=none := by decide
  have hnone3 : RecoveryFocus.pick slots (3 : Fin 11)=none := by decide
  have hpick (i : Fin 7) : RecoveryFocus.pick slots (slots i)=some i := RecoveryFocus.pick_slot slots (by decide) i
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused,hj,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone0]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.heads 0=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone0]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.tapes (slots 0)=_
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hw
  · change focused.final.heads (slots 0)=0
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hh 0 (by decide)
  · change focused.final.tapes 3=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone3]
    dsimp only [ambient]
    rw [hf]
    simp [TapeEmbedding.config,MatrixDimensionField.output,Fin.addCases]
  · change focused.final.heads 3=1
    rw [hff]
    simp only [RecoveryFocus.config,hnone3]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.tapes (slots 5)=_
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hu
  · change focused.final.heads (slots 5)=0
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hh 5 (by decide)
  · change focused.final.tapes (slots 6)=_
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using ht
  · change focused.final.heads (slots 6)=1
    rw [hff]
    simpa only [RecoveryFocus.config,hpick] using hth
  · change base.steps+1+focused.steps≤_
    rw [hs,hfs]
    rw [← htime]
    omega

end NearCubicWires.RepairOrdinary.MatrixDimensionPrepare
