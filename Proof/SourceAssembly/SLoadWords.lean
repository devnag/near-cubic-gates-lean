import Proof.SourceAssembly.SLoadCore

/-! The two local word producers the mask input load is built from.

Both are existing accepted three-tape programs, restated on a zero-padded
retained bank so that they can be docked into a source layout:
* `Streaming.machine` reads a retained `frame w` and writes the bare `w`;
* `RecoveryFieldCopy.widthMachine` reads a retained `frame w` and writes the
  unary sentinel `CompareMachine.word w.length`.
In both cases every head is physically restored to zero and the retained
source and reset log are returned unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Words
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
noncomputable section

/-- Retained framed source, empty target, paid reset log. -/
def entry (cap : Nat) (w : List Bool) : Fin 3 → List Bool :=
  ![ZeroPadding.pad cap (frame w), [], List.replicate cap false]

/-- The same bank with the decoded payload installed on the target. -/
def bare (cap : Nat) (w : List Bool) : Fin 3 → List Bool :=
  ![ZeroPadding.pad cap (frame w), w, List.replicate cap false]

/-- The same bank with the unary width sentinel installed on the target. -/
def width (cap : Nat) (w : List Bool) : Fin 3 → List Bool :=
  ![ZeroPadding.pad cap (frame w), CompareMachine.word w.length, List.replicate cap false]

theorem pad_nil (cap : Nat) : ZeroPadding.pad cap ([] : List Bool) = List.replicate cap false := by
  simp [ZeroPadding.pad]

theorem pad_false (cap n : Nat) (h : n ≤ cap) :
    ZeroPadding.pad cap (List.replicate n false) = List.replicate cap false := by
  have : n + (cap - n) = cap := by omega
  simp only [ZeroPadding.pad, List.length_replicate, ← List.replicate_add, this]

/-- Unframing a retained field onto a blank target. -/
theorem bare_step (cap : Nat) (w : List Bool) (hcap : w.length ≤ cap) :
    Step Streaming.machine (4 * w.length + 2) (fun _ => 0) (entry cap w) (fun _ => 0)
      (bare cap w) := by
  obtain ⟨receipt, hrun, hfinal, hsteps, _⟩ := Streaming.copy_run w
  have ready : RecoveryRootRound.ReadyRun Streaming.machine (4 * w.length + 2)
      (fun t : Fin 3 => if t.val = 0 then frame w else [])
      ![frame w, w, List.replicate w.length false] := by
    refine ⟨receipt, hrun, ?_, ?_, hsteps⟩
    · rw [hfinal]
      funext i
      fin_cases i <;> rfl
    · intro i
      rw [hfinal]
      fin_cases i <;> rfl
  have base := (Step.of_ready ready).pad ![cap, 0, cap]
  refine base.congr_in ?_ ?_ |>.congr rfl ?_
  · rfl
  · funext i
    fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad cap [] = _
      rw [pad_nil]
      rfl
  · funext i
    fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad cap (List.replicate w.length false) = _
      rw [pad_false cap w.length hcap]
      rfl

/-- Producing the unary width sentinel of a retained field. -/
theorem width_step (cap : Nat) (w : List Bool) (hcap : 4 * w.length + 3 ≤ cap) :
    Step RecoveryFieldCopy.widthMachine (8 * w.length + 8) (fun _ => 0) (entry cap w)
      (fun _ => 0) (width cap w) := by
  have ready := RecoveryFieldCopy.width_ready w cap
  have base := (Step.of_ready ready).pad ![cap, 0, 0]
  have hmax : max cap (4 * w.length + 3) = cap := by omega
  refine base.congr_in ?_ ?_ |>.congr rfl ?_
  · rfl
  · funext i
    fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
  · funext i
    fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad 0 (List.replicate (max cap (4 * w.length + 3)) false) = _
      rw [ZeroPadding.pad_zero, hmax]
      rfl

end
end SLoad.Words
