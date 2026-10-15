import Proof.PCP.ProjectionSourceFrame
import Proof.Amplification.RecoveryTapeSupport

/-! The one selected source algorithm is called on the two physically
produced fields. Its reset and output support are paid by its actual receipt. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.SourceCall
open LocalBitMultitape RepairOrdinary RecoveryRootRound SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {v : OrdinaryVerifier} {T : ℕ → ℕ}
variable (source : ProjectionSourceAlgorithm v T)
def program := Rewind.program source.constructor.program
def tapes := 4+(program source).tapeCount
def old (i : Fin 4) : Fin (tapes source) := i.castAdd (program source).tapeCount
def slots (i : Fin (program source).tapeCount) : Fin (tapes source) :=
  if i.val=0 then old source 2 else i.natAdd 4

theorem old_injective : Function.Injective (old source) := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin (tapes source) => i.val) h)
theorem slots_injective : Function.Injective (slots source) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (r : InputRequest) : Fin (tapes source) → List Bool :=
  Fin.addCases (SourceFrame.input (List.ofFn r.2) (T r.1).bits) (fun _ => [])
noncomputable def framingProgram := RecoveryFocus.machine (old source) SourceFrame.machine
noncomputable def sourceProgram := RecoveryFocus.machine (slots source) (program source).machine
noncomputable def machine := Composition.machine (framingProgram source) (sourceProgram source)
def sourceBudget (r : InputRequest) := source.coefficient*
  (r.1+natBitLength (T r.1)+1)^source.degrees.construction
def budget (r : InputRequest) := 8*(r.1+(T r.1).bits.length)+12+1+2*sourceBudget source r+2
def outputTape := slots source (program source).outputTape

theorem output_length (r : InputRequest) :
    (source.output r).word.length ≤ max (4*(r.1+(T r.1).bits.length)+5)
      (sourceBudget source r+1) := by
  obtain ⟨receipt,hr,ho⟩ := source.constructor.realizes r
  let word := frame (List.ofFn r.2)++frame (T r.1).bits
  have hi (i : Fin source.constructor.program.tapeCount) :
      (source.constructor.program.inputTapes word i).length ≤ max (2*word.length+1) (0+1) := by
    simp only [Program.inputTapes]
    split <;> simp [frame_length]
  have h := RecoveryTapeSupport.run_support source.constructor.program.machine _ _ receipt hr
    (2*word.length+1) 0 (by intro i; exact Nat.zero_le _) hi source.constructor.program.outputTape
  have hs := runFrom_steps_le source.constructor.program.machine _ _ receipt hr
  change receipt.steps ≤ sourceBudget source r at hs
  rw [ho] at h
  have hw : 2*word.length+1=4*(r.1+(T r.1).bits.length)+5 := by
    simp [word,frame_length]; omega
  rw [hw] at h
  exact h.trans (max_le_max (Nat.le_refl _) (by change 0+receipt.steps+1 ≤ sourceBudget source r+1; omega))

theorem call_run (r : InputRequest) : ∃ out,
    ClockJoin.ReadyRun (machine source) (budget source r) (input source r) out ∧
      out (outputTape source)=(source.output r).word ∧
      out (old source 0)=frame (List.ofFn r.2) ∧
      out (old source 1)=frame (T r.1).bits := by
  let fields := SourceFrame.output (List.ofFn r.2) (T r.1).bits
  have hf := (SourceFrame.ready (List.ofFn r.2) (T r.1).bits).focus
    (old source) (old_injective source) (input source r) (by intro i; simp [input,old])
  let middle := install (old source) (input source r) fields
  have hi : ∀ i,middle (slots source i)=(program source).inputTapes
      (frame (List.ofFn r.2)++frame (T r.1).bits) i := by
    intro i
    simp only [Program.inputTapes]
    by_cases hi : i.val=0
    · rw [if_pos hi]
      change install (old source) (input source r) fields (slots source i)=_
      rw [slots,if_pos hi,install_slot _ (old_injective source)]
      rfl
    · rw [if_neg hi]
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj; have hv := congrArg Fin.val hj
        simp only [slots,hi,if_false,old,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega)]
      simp only [slots,hi,if_false,input,Fin.addCases_right]
  obtain ⟨base,hb,ho,hh⟩ := source.constructor.reset_realizes r
  have hb' : run (program source).machine (2*sourceBudget source r+2)
      ((program source).inputTapes (frame (List.ofFn r.2)++frame (T r.1).bits))=some base := hb
  have hs := runFrom_steps_le (program source).machine _ _ base hb'
  have hsource := (show ClockJoin.ReadyRun _ _ _ base.final.tapes from ⟨base,hb',rfl,hh,hs⟩).focus
    (slots source) (slots_injective source) middle hi
  have hjoin := ClockJoin.join _ _ _ _ _ _ _ hf hsource
  have he : (8*((List.ofFn r.2).length+(T r.1).bits.length)+12)+1+
      (2*sourceBudget source r+2)=budget source r := by simp [budget]; omega
  rw [he] at hjoin
  refine ⟨_,hjoin,(install_slot _ (slots_injective source) _ _ _).trans ho,?_,?_⟩
  all_goals
    rw [install_other _ _ _ _ (by
      intro i hi; have hv := congrArg Fin.val hi
      dsimp [slots,old] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    change install (old source) (input source r) fields (old source _)=_
    rw [install_slot _ (old_injective source)]
    rfl

end NearCubicWires.RepairSource.ProjectionNormalization.SourceCall
