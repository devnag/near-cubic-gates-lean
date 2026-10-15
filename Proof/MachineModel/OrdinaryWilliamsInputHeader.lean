import Proof.MachineModel.OrdinaryMatrixHeaderCursor

/-! The actual external framed request supplies both the raw matrix stream
and all U/bit-width metadata. No prepared header or scratch tape is an
input to this enclosing program. -/
namespace NearCubicWires.RepairOrdinary.WilliamsInputHeader
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev dimensionStates := 8+(8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes))
def slots : Fin 11 → Fin 13 := ![1,3,4,5,6,7,8,9,10,11,12]
def copy : Machine 13 5 := TapeEmbedding.machine 10 Streaming.machine
noncomputable def header := RecoveryFocus.machine slots MatrixDimensionPrepare.machine
noncomputable def machine := Composition.machine copy header
def input (word : List Bool) : Fin 13 → List Bool := fun i => if i=0 then frame word else []
def budget (n : ℕ) (suffix : List Bool) :=
  4*(natWord n++suffix).length+3+MatrixDimensionPrepare.budget (natBitLength n) n

theorem natWord_eq (n : ℕ) : natWord n =
    List.replicate (natBitLength n) true ++ false :: binary (natBitLength n) n := by
  have hb : WilliamsPublishedForm.fixedWidthNatBits (natBitLength n) n = binary (natBitLength n) n :=
    RepairSource.VerifierDecoding.fixedBits_binary _ _
  exact congrArg (fun bits => List.replicate (natBitLength n) true ++ false :: bits) hb

theorem header_run (n : ℕ) (suffix : List Bool) :
    ∃ r : ExecutionReceipt 13 (5+dimensionStates),
      run machine (budget n suffix) (input (natWord n++suffix))=some r ∧
      r.final.tapes 0=frame (natWord n++suffix) ∧ r.final.heads 0=0 ∧
      r.final.tapes 1=natWord n++suffix ∧ r.final.heads 1=2*natBitLength n+1 ∧
      r.final.tapes 3=List.replicate (natBitLength n) true ∧ r.final.heads 3=0 ∧
      r.final.tapes 5=UnaryTemplate.tape (natBitLength n) ∧ r.final.heads 5=1 ∧
      r.final.tapes 6=frame (binary (natBitLength n) n) ∧ r.final.heads 6=0 ∧
      r.final.tapes 12=UnaryTemplate.tape n ∧ r.final.heads 12=1 ∧ r.steps≤budget n suffix := by
  let word := natWord n++suffix
  let w := natBitLength n
  obtain ⟨base,hr,hf,hs,_⟩ := Streaming.copy_run word
  have he := TapeEmbedding.run_embed Streaming.machine (fun _ : Fin 10 => 0)
    (fun _ : Fin 10 => []) _ _ base hr
  let ambient := TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base.final
  obtain ⟨localRun,hl,hsource,hpos,hw,hwh,hwidth,hwidthh,hu,huh,hunary,hunaryh,hsteps⟩ :=
    MatrixDimensionPrepare.prepare_run [] suffix w n (Nat.lt_pow_succ_log_self (by decide) n)
  have hword : [] ++ List.replicate w true ++ false :: (binary w n++suffix)=word := by
    simp [word,w,natWord_eq,List.append_assoc]
  rw [hword] at hl hsource
  simp only [List.length_nil,Nat.zero_add] at hl hpos
  let entry : Configuration 11 dimensionStates :=
    Composition.leftConfig _ (MatrixDimensionPrepare.input word 0)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry =
      Composition.restart ambient header.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        Streaming.finished,Streaming.config]
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        Streaming.finished,Streaming.config]
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide)
    MatrixDimensionPrepare.machine ambient.heads ambient.tapes _ entry localRun hl
  rw [hi] at hfocus
  have hj := Composition.run_join copy header (4*word.length+2)
    (MatrixDimensionPrepare.budget w n) _
    (TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base) focused he hfocus
  have htime : 4*word.length+2+1+MatrixDimensionPrepare.budget w n=budget n suffix := by rfl
  rw [htime] at hj
  have hinput : Composition.leftConfig dimensionStates
      (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
        (initialConfiguration Streaming.machine (fun t => if t.val=0 then frame word else []))) =
      initialConfiguration machine (input word) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hinput] at hj
  have hnone : RecoveryFocus.pick slots (0 : Fin 13)=none := by decide
  have hpick (i : Fin 11) : RecoveryFocus.pick slots (slots i)=some i := RecoveryFocus.pick_slot slots (by decide) i
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base) focused,hj,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff]
    simp only [RecoveryFocus.config,hnone]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.heads 0=0
    rw [hff]
    simp only [RecoveryFocus.config,hnone]
    dsimp only [ambient]
    rw [hf]
    rfl
  · change focused.final.tapes (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hsource
  · change focused.final.heads (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hpos
  · change focused.final.tapes (slots 1)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hw
  · change focused.final.heads (slots 1)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hwh
  · change focused.final.tapes (slots 3)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hwidth
  · change focused.final.heads (slots 3)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hwidthh
  · change focused.final.tapes (slots 4)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hu
  · change focused.final.heads (slots 4)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using huh
  · change focused.final.tapes (slots 10)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hunary
  · change focused.final.heads (slots 10)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hunaryh
  · change base.steps+1+focused.steps≤_
    rw [hs,hfs]
    rw [← htime]
    omega

end NearCubicWires.RepairOrdinary.WilliamsInputHeader
