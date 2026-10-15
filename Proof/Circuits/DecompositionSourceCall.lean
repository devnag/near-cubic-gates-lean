import Proof.Circuits.DecompositionSourcePrepare

/-! Invoke precisely the chosen decomposition constructor once after the
arity has been retained on physically separate tapes. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource.Call
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)
def sourceProgram := Rewind.program a.constructor.program
abbrev tapes := 16+(sourceProgram a).tapeCount
def old (i : Fin 16) : Fin (tapes a) := i.castAdd (sourceProgram a).tapeCount
def slots (i : Fin (sourceProgram a).tapeCount) : Fin (tapes a) :=
  if i.val=0 then old a 0 else i.natAdd 16
theorem slots_injective : Function.Injective (slots a) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem old_none (i : Fin 16) (hi : i≠0) : RecoveryFocus.pick (slots a) (old a i)=none := by
  have hn : ¬∃ j,slots a j=old a i := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    dsimp [slots,old] at hv
    split_ifs at hv <;> dsimp at hv
    · exact hi (Fin.ext (by omega))
    · omega
  simp [RecoveryFocus.pick,hn]

def tail (r : ExactDecompositionRequest) :=
  (List.ofFn r.gate.weight).flatMap intWord++intWord r.gate.threshold
noncomputable def prepare := TapeEmbedding.machine (sourceProgram a).tapeCount Prepare.machine
noncomputable def source := RecoveryFocus.machine (slots a) (sourceProgram a).machine
noncomputable def machine := Composition.machine (prepare a) (source a)
def input (r : ExactDecompositionRequest) : Fin (tapes a)→List Bool :=
  Fin.addCases (Prepare.input r.arity (tail r)) (fun _ => [])
def budget (r : ExactDecompositionRequest) := Prepare.budget r.arity (tail r)+2*sourceBudget a r+3
def outputTape := slots a (sourceProgram a).outputTape

theorem output_ne_old (i : Fin 16) : outputTape a≠old a i := by
  intro h
  have hf := (sourceProgram a).outputFresh
  have hv := congrArg Fin.val h
  simp only [outputTape,slots,hf,if_false,old,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

theorem call_run (r : ExactDecompositionRequest) :
    ∃ receipt,run (machine a) (budget a r) (input a r)=some receipt ∧
      receipt.steps ≤ budget a r ∧
      receipt.final.tapes (outputTape a)=exactListWord (a.output r).children ∧
      receipt.final.heads (outputTape a)=0 ∧
      receipt.final.tapes (old a 12)=UnaryTemplate.tape r.arity ∧ receipt.final.heads (old a 12)=1 ∧
      receipt.final.tapes (old a 14)=PCPPQueryField.saved r.arity [] ∧ receipt.final.heads (old a 14)=0 ∧
      receipt.final.tapes (old a 15)=natWord r.arity ∧ receipt.final.heads (old a 15)=(natWord r.arity).length := by
  obtain ⟨base,hb,hbs,hframe,hframeHead,hn,hnh,hback,hbackHead,hout,houtHead⟩ := Prepare.prepare_run r.arity (tail r)
  have he := TapeEmbedding.run_embed Prepare.machine (fun _ : Fin (sourceProgram a).tapeCount => 0)
    (fun _ : Fin (sourceProgram a).tapeCount => []) _ _ base hb
  rw [RepairSource.ProjectionNormalization.StreamPrepare.embed_initial] at he
  let ambient := TapeEmbedding.config (fun _ : Fin (sourceProgram a).tapeCount => 0)
    (fun _ : Fin (sourceProgram a).tapeCount => []) base.final
  obtain ⟨baseSource,hs,hsout,hsheads⟩ := a.constructor.reset_realizes r
  have hs' : run (sourceProgram a).machine (2*sourceBudget a r+2)
      ((sourceProgram a).inputTapes (thresholdWord r.gate))=some baseSource := hs
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config (slots a) (slots_injective a) (sourceProgram a).machine
    ambient.heads ambient.tapes _ _ baseSource hs'
  have hi : RecoveryFocus.config (slots a) ambient.heads ambient.tapes
      (initialConfiguration (sourceProgram a).machine ((sourceProgram a).inputTapes (thresholdWord r.gate)))=
      Composition.restart ambient (source a).start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      by_cases hj : j.val=0
      · simpa [ambient,slots,hj,old,TapeEmbedding.config,initialConfiguration] using hframeHead
      · simp [ambient,slots,hj,TapeEmbedding.config,initialConfiguration]
    · intro j
      by_cases hj : j.val=0
      · simpa [ambient,slots,hj,old,TapeEmbedding.config,initialConfiguration,Program.inputTapes,
          thresholdWord,tail,List.append_assoc] using hframe
      · simp [ambient,slots,hj,TapeEmbedding.config,initialConfiguration,Program.inputTapes]
  rw [hi] at hf
  have hj := Composition.run_join (prepare a) (source a) _ (2*sourceBudget a r+2) _
    (TapeEmbedding.receipt (fun _ : Fin (sourceProgram a).tapeCount => 0)
      (fun _ : Fin (sourceProgram a).tapeCount => []) base) focused he hf
  have ht : Prepare.budget r.arity (tail r)+1+(2*sourceBudget a r+2)=budget a r := by unfold budget; omega
  rw [ht] at hj
  change run (machine a) (budget a r) (input a r)=_ at hj
  have tape (j : Fin (sourceProgram a).tapeCount) : focused.final.tapes (slots a j)=baseSource.final.tapes j := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a)]
  have head (j : Fin (sourceProgram a).tapeCount) : focused.final.heads (slots a j)=baseSource.final.heads j := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a)]
  have other (i : Fin 16) (hi : i≠0) : focused.final.tapes (old a i)=base.final.tapes i ∧
      focused.final.heads (old a i)=base.final.heads i := by
    simp only [hff,RecoveryFocus.config,old_none a i hi]
    simp [ambient,old,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin (sourceProgram a).tapeCount => 0)
      (fun _ : Fin (sourceProgram a).tapeCount => []) base) focused,hj,?_,
      (tape _).trans hsout,(head _).trans (hsheads _),
      (other 12 (by decide)).1.trans hn,(other 12 (by decide)).2.trans hnh,
      (other 14 (by decide)).1.trans hback,(other 14 (by decide)).2.trans hbackHead,
      (other 15 (by decide)).1.trans hout,(other 15 (by decide)).2.trans houtHead⟩
  change base.steps+1+focused.steps ≤ _
  rw [hfs]
  have hsourceSteps := runFrom_steps_le (sourceProgram a).machine _ _ baseSource hs'
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.DecompositionSource.Call
