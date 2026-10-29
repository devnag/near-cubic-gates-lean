import SourceAdapters.Routing.CoordinateMachineInputRun
import Proof.Foundations.OrdinaryMachine

/-!
# Ordinary packaging of a fixed coordinate program

The construction in `lem:generator`: the raw request is framed and prefixed by
paid ordinary machines, then processed by the existing ordinary FL compiler.
The budget coefficient and exponent depend only on the fixed program. This
generic packaging lemma leaves the program's concrete output and no-read-error
proofs explicit; it does not assume a coordinate-array machine.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Close.Cells (langBudget VV MM)
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

noncomputable def programBudget (main : S) (word : List Bool) : ℕ :=
  langBudget noCallee zF VV MM (preparedInput word)
    (preCost (preparedInput word) + costS (globOf (preparedInput word)) main + 1)

noncomputable def ordinaryBudget (main : S) (word : List Bool) : ℕ :=
  (2 * preparedBudget word + 2) + 1 + (2 * programBudget main word + 2)

def ordinaryDegree (main : S) : ℕ := 6 * (dpS main + 5)

noncomputable def ordinaryCoefficient (main : S) : ℕ :=
  4805 + 2 * (flConst main * 5000 ^ (dpS main + 5))

theorem programBudget_le (main : S) (word : List Bool) :
    programBudget main word ≤ flConst main * 5000 ^ (dpS main + 5) *
      (word.length + 1) ^ ordinaryDegree main := by
  have hf := flBudget_le main (preparedInput word)
  have hp := Nat.pow_le_pow_left (prepared_runtime_base word) (dpS main + 5)
  have hm := Nat.mul_le_mul_left (flConst main) hp
  rw [mul_pow, ← pow_mul] at hm
  exact le_trans hf (by simpa only [ordinaryDegree, Nat.mul_assoc] using hm)

theorem ordinaryBudget_le (main : S) (word : List Bool) :
    ordinaryBudget main word ≤ ordinaryCoefficient main * (word.length + 1) ^ ordinaryDegree main := by
  have hp := preparedBudget_le word
  have hf := programBudget_le main word
  have hpow : (word.length + 1) ^ 2 ≤ (word.length + 1) ^ ordinaryDegree main :=
    Nat.pow_le_pow_right (by omega) (by simp only [ordinaryDegree]; omega)
  have hone : 1 ≤ (word.length + 1) ^ ordinaryDegree main := Nat.one_le_pow _ _ (by omega)
  simp only [ordinaryBudget, ordinaryCoefficient]
  nlinarith

/-- Compose the physical preparers and compiled program on the raw input. -/
noncomputable def ordinaryProgram {Req : Type} (input output : Req → List Bool) (main : S)
    (hwf : wfS main 0 = true)
    (hbad : ∀ r, (evalS (globOf (preparedInput (input r))) main (s0 (preparedInput (input r)))).bad = false)
    (hout : ∀ r, (evalS (globOf (preparedInput (input r))) main (s0 (preparedInput (input r)))).out = output r) :
    WordFunction Req input output (fun r => ordinaryBudget main (input r)) := by
  let P : WordFunction Req input (fun r => frame (preparedInput (input r)))
      (fun r => preparedBudget (input r)) :=
    { program := preparedWF.program, realizes := fun r => preparedWF.realizes (input r) }
  let W := flWF (fun r => preparedInput (input r)) main hwf
    (fun r => prepared_lead_pos (input r)) (fun r => prepared_lead_lt (input r)) hbad
  let Q : WordFunction Req (fun r => preparedInput (input r)) output
      (fun r => programBudget main (input r)) :=
    { program := W.program, realizes := fun r => by simpa only [hout r, programBudget] using W.realizes r }
  exact Code.composeFramed P Q

/-- Polynomial-budget ordinary machine; both constants are fixed before the request. -/
noncomputable def polynomialProgram {Req : Type} (input output : Req → List Bool) (main : S)
    (hwf : wfS main 0 = true)
    (hbad : ∀ r, (evalS (globOf (preparedInput (input r))) main (s0 (preparedInput (input r)))).bad = false)
    (hout : ∀ r, (evalS (globOf (preparedInput (input r))) main (s0 (preparedInput (input r)))).out = output r) :
    WordFunction Req input output
      (fun r => ordinaryCoefficient main * ((input r).length + 1) ^ ordinaryDegree main) :=
  (ordinaryProgram input output main hwf hbad hout).enlargeBudget (fun r => ordinaryBudget_le main (input r))

end NearCubicGates.Adapters.Routing.CoordinateMachine
