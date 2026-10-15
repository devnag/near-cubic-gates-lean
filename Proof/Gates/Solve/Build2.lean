import Proof.Gates.Solve.Build

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
open StablePartition.Workspace (overlay)
open NearCubicGates.Close.Interfaces.Formats (SysReq sysWord)
open NearCubicWires.RepairRepresentation (natWord)

theorem matV_add (C : ℕ) (a : ℕ → ℕ → ℤ) (m : ℕ) : ∀ k, matV (m + k) C a =
    matV m C a ++ (List.range k).flatMap fun v => (List.range C).map fun j => encS (a (m + v) j)
  | 0 => by simp
  | k + 1 => by
    rw [show m + (k + 1) = (m + k) + 1 by ring, matV, flat_succ, ← matV, matV_add C a m k, List.range_succ,
      List.flatMap_append]
    simp [List.append_assoc]

theorem matV_amat (s : SysReq) : matV (s.rows.length + s.pts.length) (s.pts.length + 1) (amat s) =
    matV s.rows.length (s.pts.length + 1) (amat s) ++ (List.range s.pts.length).flatMap (idRow s.pts.length) := by
  rw [matV_add]
  congr 1
  apply List.flatMap_congr
  intro v hv
  exact idRow_eq s (List.mem_range.mp hv)

theorem sysWord_eq (s : SysReq) : sysWord s =
    natWord s.pts.length ++ s.pts.flatMap ptW ++ (natWord s.rows.length ++ s.rows.flatMap rowW) := by
  have e1 : (ptW : List ℤ → List Bool) = Interfaces.listWord Interfaces.intWord := rfl
  have e2 : rowW = fun row => natWord row.1 ++ (natWord row.2.1.length ++ (List.flatMap natWord row.2.1 ++
      natWord row.2.2)) := by
    funext row; simp [rowW, Interfaces.listWord, List.append_assoc]
  rw [e1, e2]
  simp [sysWord, Interfaces.listWord, List.append_assoc]

def buildA : WMX NS NR :=
  .seq pointsP (.seq (BinW.zero wTWO wZ rF rR) (.seq (BinW.inc wTWO wZ rF rR) (.seq (BinW.inc wTWO wZ rF rR)
  (.seq rowsP (.seq identP (closeOutX sMAT rCM))))))

def buildB : WMX NS NR :=
  .seq (addR rMM rRR rTa) (.seq (addR rNN rRR rTa) (.seq (addR rNN rCC rTa) (.seq (WMX.inc rCC)
  (.seq (BinW.copy wDD wTWO rF rR) (.seq (addR rLL rT1 rTa) (.wm (WM.rewind sRAW rT1)))))))

def buildP : WMX NS NR := .seq buildA buildB

/-- The registers the build touches. -/
def bRegs : List Reg :=
  [rNN, rLP, rUL, rPAD, rSGN, rCP, rMM, rLR, rLS, rCSG, rNZQ, rSLN, rPB, rLP2, rFL, rIXP, rISG, rT4, rLV2, rBEF, rAFT,
    rK3, rCM, rRR, rCC, rT1]

/-- The registers the first part of the build touches. -/
def bRegsA : List Reg :=
  [rNN, rLP, rUL, rPAD, rSGN, rCP, rMM, rLR, rLS, rCSG, rNZQ, rSLN, rPB, rLP2, rFL, rIXP, rISG, rT4, rLV2, rBEF, rAFT,
    rK3, rCM]

/-- The registers zero after the build. -/
def bZero : List Reg :=
  [rLP, rUL, rPAD, rSGN, rCP, rLR, rLS, rCSG, rNZQ, rSLN, rPB, rLP2, rFL, rIXP, rISG, rT4, rLV2, rBEF, rAFT, rK3, rCM, rT1]

end NearCubicGates.Close.Solve
