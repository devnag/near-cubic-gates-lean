import Proof.CaseAnalysis.FinalRowScannerReload
import Proof.CaseAnalysis.FinalRowFrameJoin

/-! The scanner reload at the actual post-row bank. The native header has
already been overwritten by its paid producer. Only the three named source
fields are added; the existing D driver/log and all other tapes are retained. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10RowScannerDock
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.CloseoutRowsEstimator RepairOrdinary.C10RowFrameJoin
open ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def small (p : Program) (i : Fin 64) : Fin (Reuse.tapes p + 3) :=
  ⟨i.val, by have h := tapes_ge p; have hi := i.isLt; unfold Reuse.tapes; omega⟩
def slots (p : Program) : Fin 69 → Fin (Reuse.tapes p + 3) :=
  Fin.addCases (m:=64) (n:=5) (motive:=fun _ => Fin (Reuse.tapes p + 3)) (small p)
    ![(0 : Fin 3).natAdd (Reuse.tapes p), (1 : Fin 3).natAdd (Reuse.tapes p),
      (2 : Fin 3).natAdd (Reuse.tapes p), (Reuse.driver p).castAdd 3, (Reuse.log p).castAdd 3]

theorem injective (p : Program) : Function.Injective (slots p) := by
  intro i j he
  have wide := tapes_ge p
  have hv := congrArg Fin.val he
  revert hv
  refine Fin.addCases (m:=64) (n:=5) (fun x => ?_) (fun x => ?_) i <;>
    refine Fin.addCases (m:=64) (n:=5) (fun y => ?_) (fun y => ?_) j
  · intro hv
    simp only [slots, Fin.addCases_left] at hv
    exact congrArg (Fin.castAdd 5) (Fin.ext hv)
  · intro hv
    simp only [slots, Fin.addCases_left, Fin.addCases_right] at hv
    fin_cases y <;> (dsimp [small, Reuse.driver, Reuse.log, Reuse.tapes] at hv; omega)
  · intro hv
    simp only [slots, Fin.addCases_left, Fin.addCases_right] at hv
    fin_cases x <;> (dsimp [small, Reuse.driver, Reuse.log, Reuse.tapes] at hv; omega)
  · intro hv
    simp only [slots, Fin.addCases_right] at hv
    fin_cases x <;> fin_cases y <;> first | rfl |
      (dsimp [Reuse.driver, Reuse.log, Reuse.tapes] at hv; omega)

noncomputable def heads (p : Program) (out : List Bool) : Fin (Reuse.tapes p + 3) → ℕ :=
  Fin.addCases (m:=Reuse.tapes p) (n:=3) (motive:=fun _ => ℕ) (bankHeads p out) (fun _ => 0)
noncomputable def input (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) :
    Fin (Reuse.tapes p + 3) → List Bool :=
  Fin.addCases (m:=Reuse.tapes p) (n:=3) (motive:=fun _ => List Bool)
    (Function.update (exitTapes p D old out) (Reuse.native p) (ZeroPadding.pad C (Header.stream row)))
    (C10RowScannerReload.fields row)

theorem projected_heads (p : Program) (out : List Bool) (i : Fin 69) :
    heads p out (slots p i) = 0 := by
  have wide := tapes_ge p
  refine Fin.addCases (m:=64) (n:=5) (fun j => ?_) (fun j => ?_) i
  · simp only [slots, Fin.addCases_left]
    have hj : j.val < Reuse.tapes p := by have h := j.isLt; unfold Reuse.tapes; omega
    change heads p out ((⟨j.val,hj⟩ : Fin (Reuse.tapes p)).castAdd 3) = 0
    simp only [heads, Fin.addCases_left, bankHeads]
    apply if_neg
    intro he; have hv := congrArg Fin.val he
    dsimp [Reuse.output] at hv; omega
  · simp only [slots, Fin.addCases_right]
    fin_cases j <;> norm_num [heads, bankHeads, Reuse.driver, Reuse.log, Reuse.output]
    all_goals
      intro he
      have hv := congrArg Fin.val he
      simp at hv

theorem projected (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) (i : Fin 69) :
    input p row C D old out (slots p i) = C10RowScannerReload.input row C D i := by
  classical
  have wide := tapes_ge p
  refine Fin.addCases (m:=64) (n:=5) (fun j => ?_) (fun j => ?_) i
  · simp only [slots, Fin.addCases_left, C10RowScannerReload.input]
    have hj : j.val < Reuse.tapes p := by have h := j.isLt; unfold Reuse.tapes; omega
    let k : Fin (Reuse.tapes p) := ⟨j.val,hj⟩
    change input p row C D old out (k.castAdd 3) =
      (if j=52 then ZeroPadding.pad C (Header.stream row) else List.replicate D false)
    simp only [input, Fin.addCases_left]
    by_cases hn : j=52
    · subst j
      have he : k=Reuse.native p := Fin.ext rfl
      rw [he, Function.update_self, if_pos rfl]
    · have kn : k ≠ Reuse.native p := by
        intro he
        have hv := congrArg Fin.val he
        apply hn
        exact Fin.ext hv
      rw [Function.update_of_ne kn, if_neg hn]
      have ko : k ≠ Reuse.output p := by
        intro he; have hv := congrArg Fin.val he
        dsimp [k, Reuse.output] at hv; omega
      have kd : k ≠ Reuse.driver p := by
        intro he; have hv := congrArg Fin.val he
        dsimp [k, Reuse.driver] at hv; omega
      have kl : k ≠ Reuse.log p := by
        intro he; have hv := congrArg Fin.val he
        dsimp [k, Reuse.log] at hv; omega
      have kc : k ≠ Reuse.capacity p := by
        intro he; have hv := congrArg Fin.val he
        dsimp [k, Reuse.capacity, Reuse.old, Retained.capacity] at hv; omega
      simp only [exitTapes, ko, kd, kl, kn, kc, if_false]
  · simp only [slots, Fin.addCases_right, C10RowScannerReload.input]
    fin_cases j
    · simp only [Matrix.cons_val_zero', input, Fin.addCases_right]
      rfl
    · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', input, Fin.addCases_right]
      rfl
    · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', input, Fin.addCases_right]
      rfl
    · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', input, Fin.addCases_left]
      have hn : Reuse.driver p ≠ Reuse.native p := by
        intro he; have hv := congrArg Fin.val he
        dsimp [Reuse.driver, Reuse.native, Reuse.old] at hv; omega
      rw [Function.update_of_ne hn]
      exact exitTapes_driver p D old out
    · simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', input, Fin.addCases_left]
      have hn : Reuse.log p ≠ Reuse.native p := by
        intro he; have hv := congrArg Fin.val he
        dsimp [Reuse.log, Reuse.native, Reuse.old] at hv; omega
      rw [Function.update_of_ne hn]
      exact exitTapes_log p D old out

theorem run (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool)
    (hd : row.d ≤ D) (hp : row.p ≤ D) (hD : 1 ≤ D) :
    Step (RecoveryFocus.machine (slots p) C10RowScannerReload.machine)
      (C10RowScannerReload.budget row D) (heads p out) (input p row C D old out)
      (heads p out) (install (slots p) (input p row C D old out) (C10RowScannerReload.output row C D)) := by
  exact ((C10RowScannerReload.run row C D hd hp hD).dock (slots p) (injective p)
    (heads p out) (input p row C D old out) (projected_heads p out) (projected p row C D old out)).congr
      (dockH_existing (slots p) (heads p out) _ (projected_heads p out)) rfl

end NearCubicWires.RepairSource.CloseoutFinal.C10RowScannerDock
