import SourceAdapters.Code.Algorithms
import Proof.Gates.CheckedPCPP.Harness
import Proof.Hierarchy.HierarchyBinaryPower

/-!
`app:sources`, "Uniform three-query PCPP and code interfaces": ordinary word-program composition with explicitly paid framing.
The first program emits the framed input of the second; both head resets are
paid by the existing rewind construction. No raw-output framing is assumed.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.CheckedPCPP

def firstSlots (p q : Program) : Fin p.tapeCount → Fin (p.tapeCount + q.tapeCount) :=
  Fin.castAdd q.tapeCount

def secondSlots (p q : Program) (i : Fin q.tapeCount) : Fin (p.tapeCount + q.tapeCount) :=
  if i.val = 0 then p.outputTape.castAdd q.tapeCount else i.natAdd p.tapeCount

theorem firstSlots_injective (p q : Program) : Function.Injective (firstSlots p q) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin (p.tapeCount + q.tapeCount) => z.val) h

theorem secondSlots_injective (p q : Program) : Function.Injective (secondSlots p q) := by
  intro i j h
  have hp := p.outputTape.isLt
  have hh := congrArg Fin.val h
  dsimp [secondSlots] at hh
  split_ifs at hh with hi hj hj
  · apply Fin.ext; omega
  · simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
    omega
  · simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
    omega
  · apply Fin.ext
    simp only [Fin.val_natAdd] at hh
    omega

noncomputable def composeProgram (p q : Program) : Program where
  tapeCount := p.tapeCount + q.tapeCount
  stateCount := p.stateCount + q.stateCount
  twoTapes := by have h := p.twoTapes; omega
  machine := Composition.machine (RecoveryFocus.machine (firstSlots p q) p.machine)
    (RecoveryFocus.machine (secondSlots p q) q.machine)
  outputTape := secondSlots p q q.outputTape
  outputFresh := by
    rw [secondSlots, if_neg q.outputFresh]
    have hp := p.twoTapes
    simp only [Fin.val_natAdd]
    omega

/-- Two actual ordinary algorithms compose when their framing conversion is
already performed by the first program. -/
noncomputable def composeFramed {Request : Type} {input middle output : Request → List Bool}
    {firstBudget secondBudget : Request → ℕ}
    (P : WordFunction Request input (fun r => frame (middle r)) firstBudget)
    (Q : WordFunction Request middle output secondBudget) :
    WordFunction Request input output (fun r => (2 * firstBudget r + 2) + 1 + (2 * secondBudget r + 2)) where
  program := composeProgram (Rewind.program P.program) (Rewind.program Q.program)
  realizes r := by
    let p := Rewind.program P.program
    let q := Rewind.program Q.program
    let A := (composeProgram p q).inputTapes (input r)
    obtain ⟨op, hp, hop⟩ := wordFunction_ready P r
    obtain ⟨oq, hq, hoq⟩ := wordFunction_ready Q r
    have hp' := hp.focus (firstSlots p q) (firstSlots_injective p q) A (by
      intro i
      simp [A, Program.inputTapes, composeProgram, firstSlots, p])
    let B := install (firstSlots p q) A op
    have hinput : ∀ i, B (secondSlots p q i) = q.inputTapes (middle r) i := by
      intro i
      by_cases hi : i.val = 0
      · rw [secondSlots, if_pos hi]
        change install (firstSlots p q) A op (firstSlots p q p.outputTape) = _
        rw [install_slot _ (firstSlots_injective p q)]
        simpa [Program.inputTapes, hi, p, q] using hop
      · rw [secondSlots, if_neg hi]
        change install (firstSlots p q) A op (i.natAdd p.tapeCount) = _
        rw [install_other]
        · simp [A, composeProgram, Program.inputTapes, hi]
        · intro j h
          have hh := congrArg Fin.val h
          have hj := j.isLt
          simp only [firstSlots, Fin.val_castAdd, Fin.val_natAdd] at hh
          omega
    have hq' := hq.focus (secondSlots p q) (secondSlots_injective p q) B hinput
    have hj := ClockJoin.join _ _ _ _ A B _ hp' hq'
    obtain ⟨receipt, hrun, hout, _, _⟩ := hj
    refine ⟨receipt, hrun, ?_⟩
    change receipt.final.tapes (secondSlots p q q.outputTape) = output r
    rw [hout, install_slot _ (secondSlots_injective p q)]
    exact hoq

theorem composeFramed_budget_poly {Request : Type} (input : Request → List Bool)
    (firstBudget secondBudget : Request → ℕ)
    (hfirst : ∃ K e : ℕ, ∀ r, firstBudget r ≤ K * ((input r).length + 1) ^ e)
    (hsecond : ∃ K e : ℕ, ∀ r, secondBudget r ≤ K * ((input r).length + 1) ^ e) :
    ∃ K e : ℕ, ∀ r,
      (2 * firstBudget r + 2) + 1 + (2 * secondBudget r + 2) ≤ K * ((input r).length + 1) ^ e := by
  obtain ⟨K1, e1, h1⟩ := hfirst
  obtain ⟨K2, e2, h2⟩ := hsecond
  refine ⟨2 * K1 + 2 * K2 + 5, max e1 e2, fun r => ?_⟩
  have hp1 := Nat.pow_le_pow_right (by omega : 1 ≤ (input r).length + 1) (le_max_left e1 e2)
  have hp2 := Nat.pow_le_pow_right (by omega : 1 ≤ (input r).length + 1) (le_max_right e1 e2)
  have hb1 := (h1 r).trans (Nat.mul_le_mul_left K1 hp1)
  have hb2 := (h2 r).trans (Nat.mul_le_mul_left K2 hp2)
  have hp : 1 ≤ ((input r).length + 1) ^ max e1 e2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

end NearCubicGates.Adapters.Code
