import Proof.Gates.Solve.Bound

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (intWord listWord)
open NearCubicGates.Close.Interfaces.Formats (SysReq sysWord solveWord)
open NearCubicGates.Close.Interfaces (startState)

def mainP : WMX NS NR :=
  .seq setupP (.seq buildP (.seq elimP (.seq outP (.seq rewOutP (clearAll (List.finRange NR))))))

/-- The cap of the run. -/
def capT (ℓ : ℕ) : ℕ :=
  setupCap ℓ + capB ℓ ℓ ℓ (wOf ℓ) + capE (2 * ℓ * (ℓ + 1)) (wOf ℓ) + ℓ + 2 * (wOf ℓ + 1) + 2

theorem listWord_pos {α : Type} (f : α → List Bool) (l : List α) : 1 ≤ (listWord f l).length := by
  unfold listWord; rw [List.length_append]; have := natWord_pos l.length; omega

theorem rowF_pos (r : ℕ × List ℕ × ℕ) : 1 ≤ (rowF r).length := by
  unfold rowF; rw [List.length_append, List.length_append]; have := natWord_pos r.1; omega

theorem pts_len_le (s : SysReq) : s.pts.length ≤ (sysWord s).length := by
  have h1 := len_le_flatMap (listWord intWord) (listWord_pos intWord) s.pts
  rw [sysWord_split]; simp only [List.length_append]; omega

theorem rows_len_le (s : SysReq) : s.rows.length ≤ (sysWord s).length := by
  have h1 := len_le_flatMap rowF rowF_pos s.rows
  rw [sysWord_split]; simp only [List.length_append]; omega

theorem capB_le {m n ℓ W : ℕ} (hm : m ≤ ℓ) (hn : n ≤ ℓ) : capB m n ℓ W ≤ capB ℓ ℓ ℓ W := by
  unfold capB capP capC; gcongr

theorem capE_le {N N' W : ℕ} (h : N ≤ N') : capE N W ≤ capE N' W := by unfold capE; gcongr

theorem RC_le {m n ℓ : ℕ} (hm : m ≤ ℓ) (hn : n ≤ ℓ) : (m + n) * (n + 1) ≤ 2 * ℓ * (ℓ + 1) := by
  have : m + n ≤ 2 * ℓ := by omega
  calc (m + n) * (n + 1) ≤ (2 * ℓ) * (ℓ + 1) := Nat.mul_le_mul this (by omega)
    _ = 2 * ℓ * (ℓ + 1) := rfl

theorem bRegs_setS {r : Reg} (hr : r ∈ bRegs) : r ≠ rR2 ∧ r ≠ rWL ∧ r ≠ rLL := by
  revert r; decide

theorem setS_zero (word : List Bool) {r : Reg} (h1 : r ≠ rR2) (h2 : r ≠ rWL) (h3 : r ≠ rLL) : (setS word).val r = 0 := by
  rw [setS_val, if_neg h1, if_neg h2, if_neg h3]

theorem elimRegs_cases {r : Reg} (hr : r ∈ elimRegs) : r = rCM ∨ (r ∉ bRegs ∧ r ≠ rR2 ∧ r ≠ rWL ∧ r ≠ rLL) := by
  revert r; decide

/-- The total cost. -/
def mainCost (s : SysReq) : ℕ :=
  setupCost (sysWord s).length + 1 + (buildCost s.rows.length s.pts.length (sysWord s).length (wOf (sysWord s).length) + 1 +
    (elimCost (s.rows.length + s.pts.length) (s.pts.length + 1) s.pts.length
      (ucost (wOf (sysWord s).length) ((s.rows.length + s.pts.length) * (s.pts.length + 1))) + 1 +
    (outCost (wOf (sysWord s).length) ((s.rows.length + s.pts.length) * (s.pts.length + 1)) (s.pts.length + 1)
      s.rows.length s.pts.length + 1 +
    (rewOutCost (wOf (sysWord s).length) s.pts.length + 1 + (List.finRange NR).length * (3 * capT (sysWord s).length + 2)))))

end NearCubicGates.Close.Solve
