import Proof.MachineModel.OrdinaryMatrixScoreBatchTarget

/-! Actual raw-cut entry: remove the ordinary outer frame once and read both
d and p, constructing the binary values and their physical unary drivers. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreHeaders
open LocalBitMultitape SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev D := WilliamsInputHeader.dimensionStates
def slots : Fin 11 → Fin 23 := ![1,13,14,15,16,17,18,19,20,21,22]
noncomputable def first : Machine 23 (5+D) := TapeEmbedding.machine 10 WilliamsInputHeader.machine
noncomputable def second : Machine 23 D := RecoveryFocus.machine slots MatrixDimensionPrepare.machine
noncomputable def machine : Machine 23 ((5+D)+D) := Composition.machine first second
def input (bs : List Bool) : Fin 23 → List Bool := fun i => if i.val=0 then frame bs else []
def budget (d p : ℕ) (suffix : List Bool) :=
  WilliamsInputHeader.budget d (natWord p++suffix)+1+MatrixDimensionPrepare.budget (natBitLength p) p

theorem headers_run (d p : ℕ) (suffix : List Bool) :
    ∃ actual : ExecutionReceipt 23 ((5+D)+D),
      run machine (budget d p suffix) (input (natWord d++natWord p++suffix))=some actual ∧
      actual.final.tapes 0=frame (natWord d++natWord p++suffix) ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 1=natWord d++natWord p++suffix ∧
      actual.final.heads 1=2*natBitLength d+1+(2*natBitLength p+1) ∧
      actual.final.tapes 3=List.replicate (natBitLength d) true ∧ actual.final.heads 3=0 ∧
      actual.final.tapes 6=frame (binary (natBitLength d) d) ∧ actual.final.heads 6=0 ∧
      actual.final.tapes 12=UnaryTemplate.tape d ∧ actual.final.heads 12=1 ∧
      actual.final.tapes 13=List.replicate (natBitLength p) true ∧ actual.final.heads 13=0 ∧
      actual.final.tapes 16=frame (binary (natBitLength p) p) ∧ actual.final.heads 16=0 ∧
      actual.final.tapes 22=UnaryTemplate.tape p ∧ actual.final.heads 22=1 ∧
      actual.steps≤budget d p suffix := by
  let source := natWord d++natWord p++suffix
  obtain ⟨base,hb,ht0,hh0,ht1,hh1,ht3,hh3,_,_,ht6,hh6,ht12,hh12,hbs⟩ :=
    WilliamsInputHeader.header_run d (natWord p++suffix)
  simp only [←List.append_assoc] at hb ht0 ht1
  have he := TapeEmbedding.run_embed WilliamsInputHeader.machine (fun _ : Fin 10 => 0)
    (fun _ : Fin 10 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base.final
  obtain ⟨last,hl,hs,hpos,hw,hwh,_,_,hv,hvh,hu,huh,hls⟩ := MatrixDimensionPrepare.prepare_run
    (natWord d) suffix (natBitLength p) p (Nat.lt_pow_succ_log_self (by decide) p)
  have hsource : natWord d++List.replicate (natBitLength p) true++
      false::(binary (natBitLength p) p++suffix)=source := by
    simp [source,WilliamsInputHeader.natWord_eq,List.append_assoc]
  have hlength : (natWord d).length=2*natBitLength d+1 := by
    simp [WilliamsInputHeader.natWord_eq]; omega
  rw [hsource] at hl hs
  rw [hlength] at hl hpos
  let entry : Configuration 11 D := Composition.leftConfig _
    (MatrixDimensionPrepare.input source (2*natBitLength d+1))
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes entry=
      Composition.restart ambient second.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · simpa [ambient,slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
          MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases] using hh1
      all_goals simp [ambient,slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases]
    · intro i
      fin_cases i
      · simpa [ambient,slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
          MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases,source] using ht1
      all_goals simp [ambient,slots,entry,MatrixDimensionPrepare.input,MatrixDimensionField.input,
        MatrixDimensionHeader.input,Composition.leftConfig,TapeEmbedding.config,Fin.addCases]
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixDimensionPrepare.machine
    ambient.heads ambient.tapes _ entry last hl
  rw [hi] at hf
  have hj := Composition.run_join first second (WilliamsInputHeader.budget d (natWord p++suffix))
    (MatrixDimensionPrepare.budget (natBitLength p) p) _
    (TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base) focused he hf
  have hin : Composition.leftConfig D (TapeEmbedding.config (fun _ : Fin 10 => 0)
      (fun _ : Fin 10 => []) (initialConfiguration WilliamsInputHeader.machine
        (WilliamsInputHeader.input source)))=initialConfiguration machine (input source) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases]
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        initialConfiguration,input,WilliamsInputHeader.input]
  rw [hin] at hj
  have pick (i : Fin 11) : RecoveryFocus.pick slots (slots i)=some i :=
    RecoveryFocus.pick_slot slots (by decide) i
  have otherT (i : Fin 13) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.tapes (i.castAdd 10)=base.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,hn]
    simp [ambient,TapeEmbedding.config]
  have otherH (i : Fin 13) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.heads (i.castAdd 10)=base.final.heads i := by
    rw [hff]
    simp only [RecoveryFocus.config,hn]
    simp [ambient,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt _ focused,hj,
    (otherT 0 (by decide)).trans ht0,(otherH 0 (by decide)).trans hh0,?_,?_,
    (otherT 3 (by decide)).trans ht3,(otherH 3 (by decide)).trans hh3,
    (otherT 6 (by decide)).trans ht6,(otherH 6 (by decide)).trans hh6,
    (otherT 12 (by decide)).trans ht12,(otherH 12 (by decide)).trans hh12,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hs
  · change focused.final.heads (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick,Nat.add_assoc] using hpos
  · change focused.final.tapes (slots 1)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hw
  · change focused.final.heads (slots 1)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hwh
  · change focused.final.tapes (slots 4)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hv
  · change focused.final.heads (slots 4)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hvh
  · change focused.final.tapes (slots 10)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using hu
  · change focused.final.heads (slots 10)=_
    rw [hff]; simpa only [RecoveryFocus.config,pick] using huh
  · change base.steps+1+focused.steps≤_
    rw [hfs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreHeaders
