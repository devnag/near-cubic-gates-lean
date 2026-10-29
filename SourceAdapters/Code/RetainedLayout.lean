import SourceAdapters.Code.RetainedCopy

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": disjoint tapes for a preserved input, one actual call,
and an executed frame concatenation. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.Retained

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

def tapes (p : Program) : ℕ := 6 + p.tapeCount + 6

def copySlots (p : Program) (i : Fin 6) : Fin (tapes p) := ⟨i.val, by dsimp [tapes]; omega⟩

def callSlots (p : Program) (i : Fin p.tapeCount) : Fin (tapes p) :=
  if i.val = 0 then ⟨3, by dsimp [tapes]; omega⟩
  else ⟨6 + i.val, by dsimp [tapes]; omega⟩

def pairSlots (p : Program) (i : Fin 6) : Fin (tapes p) :=
  if i.val = 0 then ⟨0, by dsimp [tapes]; omega⟩
  else if i.val = 2 then ⟨6 + p.outputTape.val, by dsimp [tapes]; have := p.outputTape.isLt; omega⟩
  else ⟨6 + p.tapeCount + i.val, by dsimp [tapes]; omega⟩

theorem callSlots_val (p : Program) (i : Fin p.tapeCount) :
    (callSlots p i).val = if i.val = 0 then 3 else 6 + i.val := by
  unfold callSlots
  split <;> rfl

theorem pairSlots_val (p : Program) (i : Fin 6) :
    (pairSlots p i).val =
      if i.val = 0 then 0 else if i.val = 2 then 6 + p.outputTape.val else 6 + p.tapeCount + i.val := by
  unfold pairSlots
  split_ifs <;> rfl

theorem copySlots_injective (p : Program) : Function.Injective (copySlots p) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin (tapes p) => z.val) h

theorem callSlots_injective (p : Program) : Function.Injective (callSlots p) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [callSlots_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem pairSlots_injective (p : Program) : Function.Injective (pairSlots p) := by
  intro i j h
  have hv := congrArg Fin.val h
  have ho := p.outputTape.isLt
  simp only [pairSlots_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem call_not_original (p : Program) (i : Fin p.tapeCount) :
    callSlots p i ≠ copySlots p 0 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [callSlots_val, copySlots] at hv
  split_ifs at hv <;> omega

theorem call_not_copy (p : Program) (i : Fin p.tapeCount) (hi : i.val ≠ 0) (j : Fin 6) :
    copySlots p j ≠ callSlots p i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [callSlots, hi, if_false, copySlots] at hv
  have hj := j.isLt
  omega

theorem pair_work_not_copy (p : Program) (i : Fin 6) (hi : i.val ≠ 0 ∧ i.val ≠ 2) (j : Fin 6) :
    copySlots p j ≠ pairSlots p i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [pairSlots, hi.1, hi.2,
    if_false, copySlots] at hv
  have hj := j.isLt
  omega

theorem pair_work_not_call (p : Program) (i : Fin 6) (hi : i.val ≠ 0 ∧ i.val ≠ 2) (j : Fin p.tapeCount) :
    callSlots p j ≠ pairSlots p i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [pairSlots, hi.1, hi.2, if_false] at hv
  simp only [callSlots_val] at hv
  have hj := j.isLt
  split_ifs at hv <;> omega

noncomputable def program (p : Program) : Program where
  tapeCount := tapes p
  stateCount := (copyScript.size + 2 + p.stateCount) + (pairScript.size + 2)
  twoTapes := by dsimp [tapes]; omega
  machine := Composition.machine
    (Composition.machine (RecoveryFocus.machine (copySlots p) copyMachine)
      (RecoveryFocus.machine (callSlots p) p.machine))
    (RecoveryFocus.machine (pairSlots p) pairMachine)
  outputTape := pairSlots p 3
  outputFresh := by simp [pairSlots]

end NearCubicGates.Adapters.Code.Retained
