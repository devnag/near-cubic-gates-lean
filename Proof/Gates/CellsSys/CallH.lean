import Proof.Gates.CellsSys.CallG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN bitN)

section H
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) (part : Option Bool)

open Classical in
/-- The true count at a score vector (a natural; `trueDist` is its cast). -/
noncomputable def tdN (u : Role c → ℤ) : ℕ :=
  ((Finset.univ : Finset (Points wt.I)).filter fun x =>
    inPart c wt part x = true ∧ digitVec c p wt y x = κ ∧ scoreVec c wt y x = u).card

theorem trueDist_tdN (u : Role c → ℤ) : trueDist c p wt y part κ u = (tdN c p wt y κ part u : ℚ) := rfl

/-- The true count at the point `(a, b)`. -/
noncomputable def mdAB (a b : ℕ) : ℕ := tdN c p wt y κ part (ptAB c p wt y κ a b)

theorem ptsOf_loops : ptsOf c p wt y κ = (List.range (lenR c p wt y κ 0)).flatMap fun a =>
    (List.range (lenR c p wt y κ 1)).map fun b => ptAB c p wt y κ a b := by
  unfold ptsOf
  rw [vecsM_two _ (by rw [boxLens_length]; exact rc12 c), boxLens_get0, boxLens_get1, boxLens_length,
    List.map_flatMap]
  apply List.flatMap_congr
  intro a _
  rw [List.map_map]
  rfl

theorem solve_word {cT : ℕ} (S : SolveMachine) (hs : Spec cT (header c) p) (ht : CellTests c p wt y)
    (hκ : κ ∈ digitVectors c p wt y) :
    solveWord (S.solve (sysOf c p wt y κ part)) = natWord 1 ++ (natWord (lenR c p wt y κ 0 * lenR c p wt y κ 1) ++
      ((List.range (lenR c p wt y κ 0)).flatMap (fun a => (List.range (lenR c p wt y κ 1)).flatMap
        (rdW (mdAB c p wt y κ part) a)) ++ [])) := by
  rw [solve_sysOf c p wt y κ S hs ht part hκ]
  have hlen := pts_len c p wt y κ
  rw [List.length_map] at hlen
  simp only [solveWord, listWord, List.length_map, hlen, List.append_nil]
  congr 2
  rw [List.flatMap_map, ptsOf_loops, List.flatMap_assoc]
  apply List.flatMap_congr
  intro a _
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  simp only [trueDist_tdN, ratWord_nat, rdW, mdAB]

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List ℚ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_append, ih]

theorem sum_pts (g : (Role c → ℤ) → ℚ) : ((ptsOf c p wt y κ).map g).sum =
    ((List.range (lenR c p wt y κ 0)).map fun a =>
      ((List.range (lenR c p wt y κ 1)).map fun b => g (ptAB c p wt y κ a b)).sum).sum := by
  rw [ptsOf_loops, List.map_flatMap, sum_flatMap']
  congr 1
  apply List.map_congr_left
  intro a _
  rw [List.map_map]
  rfl

end H

end NearCubicGates.Close.Cells.SystemsPhase
