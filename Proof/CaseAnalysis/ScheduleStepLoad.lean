import Proof.CaseAnalysis.ScheduleStepWrites

/-! Copy the actual retained index and input length into the reusable
candidate test. These are paid scans of existing unary templates. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Step
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def indexTarget (sources : EightSources) (k D : Nat) :=
  testSlots sources k D (Test.old sources k D (Candidate.powerSlots sources k D 0))
def lengthTarget (sources : EightSources) (k D : Nat) :=
  testSlots sources k D (Test.extra sources k D 0)
def indexed (sources : EightSources) (k D C s n best : Nat) :=
  Function.update (bank sources k D C s n best) (indexTarget sources k D) (ZeroPadding.pad C (List.replicate s true))
def loaded (sources : EightSources) (k D C s n best : Nat) :=
  Function.update (indexed sources k D C s n best) (lengthTarget sources k D) (ZeroPadding.pad C (List.replicate n true))
def load (sources : EightSources) (k D : Nat) := Composition.machine (copyIndex sources k D) (copyLength sources k D)

theorem ne_index (sources : EightSources) (k D : Nat) (i : Fin (tapes sources k D)) (hi : 0 < i.val) :
    i≠indexTarget sources k D := by
  intro h;have hv:=congrArg Fin.val h
  change i.val=0 at hv;omega
theorem length_ne_index (sources : EightSources) (k D : Nat) : lengthTarget sources k D≠indexTarget sources k D := by
  apply ne_index
  change 0<Candidate.tapes sources k D
  dsimp [Candidate.tapes];omega

theorem index_run (sources : EightSources) (k D C s n best : Nat) (hs : s+2≤C) :
    ClockJoin.ReadyRun (copyIndex sources k D) (2*s+6) (bank sources k D C s n best)
      (indexed sources k D C s n best) := by
  apply Reusable.copy_into (indexSlots sources k D) (small_injective sources k D).1 0 C s hs
  · change bank sources k D C s n best (port sources k D 0)=ZeroPadding.pad 0 (UnaryTemplate.tape s)
    rw [ZeroPadding.pad_zero]
    exact bank_port sources k D C s n best 0
  · exact bank_work sources k D C s n best _
  · exact bank_work sources k D C s n best _

theorem length_run (sources : EightSources) (k D C s n best : Nat) (hn : n+2≤C) :
    ClockJoin.ReadyRun (copyLength sources k D) (2*n+6) (indexed sources k D C s n best)
      (loaded sources k D C s n best) := by
  apply Reusable.copy_into (lengthSlots sources k D) (small_injective sources k D).2.1 0 C n hn
  · change indexed sources k D C s n best (port sources k D 1)=_
    rw [indexed,Function.update_of_ne (ne_index sources k D _ (by
      change 0<workTapes sources k D+1;omega))]
    rw [ZeroPadding.pad_zero]
    exact bank_port sources k D C s n best 1
  · change indexed sources k D C s n best (lengthTarget sources k D)=_
    rw [indexed,Function.update_of_ne (length_ne_index sources k D)]
    exact bank_work sources k D C s n best _
  · change indexed sources k D C s n best (copyLog sources k D 1)=_
    rw [indexed,Function.update_of_ne (ne_index sources k D _ (by
      change 0<Test.tapes sources k D+1;omega))]
    exact bank_work sources k D C s n best _

theorem load_run (sources : EightSources) (k D C s n best : Nat) (hs : s+2≤C) (hn : n+2≤C) :
    ClockJoin.ReadyRun (load sources k D) ((2*s+6)+1+(2*n+6))
      (bank sources k D C s n best) (loaded sources k D C s n best) :=
  ClockJoin.join _ _ _ _ _ _ _ (index_run sources k D C s n best hs) (length_run sources k D C s n best hn)

theorem test_input_shape (sources : EightSources) (k D s n : Nat) (i : Fin (Test.tapes sources k D)) :
    Test.input sources k D s n i=
      if i.val=0 then List.replicate s true
      else if i.val=Candidate.tapes sources k D then List.replicate n true else [] := by
  refine Fin.addCases (m:=Candidate.tapes sources k D) (n:=5) (fun j=>?_) (fun j=>?_) i
  · have hj:=j.isLt
    simp only [Test.input,Fin.addCases_left,Candidate.input,Fin.val_castAdd]
    by_cases hz : j.val=0 <;> simp [hz,show j.val≠Candidate.tapes sources k D by omega]
  · have ht : 0<Candidate.tapes sources k D := by dsimp [Candidate.tapes];omega
    simp only [Test.input,Fin.addCases_right,Fin.val_natAdd]
    simp [Nat.ne_of_gt ht]

theorem loaded_input (sources : EightSources) (k D C s n best : Nat) (i : Fin (Test.tapes sources k D)) :
    loaded sources k D C s n best (testSlots sources k D i)=ZeroPadding.pad C (Test.input sources k D s n i) := by
  rw [test_input_shape]
  by_cases h0 : i.val=0
  · have he : testSlots sources k D i=indexTarget sources k D := Fin.ext h0
    rw [if_pos h0,he,loaded,Function.update_of_ne (length_ne_index sources k D).symm,indexed,Function.update_self]
  · rw [if_neg h0]
    have hni : testSlots sources k D i≠indexTarget sources k D := by
      intro he;have hv:=congrArg Fin.val he
      change i.val=0 at hv;exact h0 hv
    by_cases hn : i.val=Candidate.tapes sources k D
    · have he : testSlots sources k D i=lengthTarget sources k D := Fin.ext hn
      rw [if_pos hn,he,loaded,Function.update_self]
    · have hnl : testSlots sources k D i≠lengthTarget sources k D := by
        intro he;have hv:=congrArg Fin.val he
        change i.val=Candidate.tapes sources k D at hv;exact hn hv
      rw [if_neg hn,loaded,Function.update_of_ne hnl,indexed,Function.update_of_ne hni]
      rw [show testSlots sources k D i=work sources k D (i.castAdd 3) from rfl,bank_work]
      simp [ZeroPadding.pad]

end
end NearCubicWires.RepairSource.CloseoutSchedule.Step
