import SourceAdapters.Code.PairTransformSplit

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": disjoint tape routing for a first-field computation while
the second input frame is retained exactly. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.PairTransform

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

def tapes (p : Program) : ℕ := 6 + p.tapeCount + 6

def splitSlots (p : Program) (i : Fin 6) : Fin (tapes p) := ⟨i.val, by dsimp [tapes]; omega⟩

def callSlots (p : Program) (i : Fin p.tapeCount) : Fin (tapes p) :=
  if i.val = 0 then ⟨2, by dsimp [tapes]; omega⟩
  else ⟨6 + i.val, by dsimp [tapes]; omega⟩

def finishSlots (p : Program) (i : Fin 6) : Fin (tapes p) :=
  if i.val = 0 then ⟨6 + p.outputTape.val, by dsimp [tapes]; have := p.outputTape.isLt; omega⟩
  else if i.val = 2 then ⟨3, by dsimp [tapes]; omega⟩
  else ⟨6 + p.tapeCount + i.val, by dsimp [tapes]; omega⟩

theorem callSlots_val (p : Program) (i : Fin p.tapeCount) :
    (callSlots p i).val = if i.val = 0 then 2 else 6 + i.val := by
  unfold callSlots
  split <;> rfl

theorem finishSlots_val (p : Program) (i : Fin 6) :
    (finishSlots p i).val =
      if i.val = 0 then 6 + p.outputTape.val else if i.val = 2 then 3 else 6 + p.tapeCount + i.val := by
  unfold finishSlots
  split_ifs <;> rfl

theorem splitSlots_injective (p : Program) : Function.Injective (splitSlots p) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin (tapes p) => z.val) h

theorem callSlots_injective (p : Program) : Function.Injective (callSlots p) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [callSlots_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem finishSlots_injective (p : Program) : Function.Injective (finishSlots p) := by
  intro i j h
  have hv := congrArg Fin.val h
  have ho := p.outputTape.isLt
  simp only [finishSlots_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem call_not_second (p : Program) (i : Fin p.tapeCount) :
    callSlots p i ≠ splitSlots p 3 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [callSlots_val, splitSlots] at hv
  split_ifs at hv <;> omega

theorem call_not_split (p : Program) (i : Fin p.tapeCount) (hi : i.val ≠ 0) (j : Fin 6) :
    splitSlots p j ≠ callSlots p i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [callSlots_val, hi, if_false, splitSlots] at hv
  have hj := j.isLt
  omega

theorem finish_work_not_split (p : Program) (i : Fin 6) (hi : i.val ≠ 0 ∧ i.val ≠ 2) (j : Fin 6) :
    splitSlots p j ≠ finishSlots p i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [finishSlots_val, hi.1, hi.2, if_false, splitSlots] at hv
  have hj := j.isLt
  omega

theorem finish_work_not_call (p : Program) (i : Fin 6) (hi : i.val ≠ 0 ∧ i.val ≠ 2)
    (j : Fin p.tapeCount) : callSlots p j ≠ finishSlots p i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [finishSlots_val, hi.1, hi.2, if_false, callSlots_val] at hv
  have hj := j.isLt
  split_ifs at hv <;> omega

noncomputable def rawMachine (p : Program) :=
  Composition.machine
    (Composition.machine (RecoveryFocus.machine (splitSlots p) splitMachine)
      (RecoveryFocus.machine (callSlots p) p.machine))
    (RecoveryFocus.machine (finishSlots p) Retained.pairMachine)

end NearCubicGates.Adapters.Code.PairTransform
