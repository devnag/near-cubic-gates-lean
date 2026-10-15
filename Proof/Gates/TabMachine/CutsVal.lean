import Proof.Gates.TabMachine.ExactVal
import Proof.Gates.Tabulator.Request

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.ThresholdCompiler NearCubicWires.SupplierPipeline NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut fields)
open NearCubicGates.Close.Tabulator

/-! ## Equations as lists -/

/-- An equation on the printer's halves as a list: the `s` weights in outer order, then the target. -/
def eqF {s : ℕ} (e : RowBinLift.Equation ((s + 1) / 2) (s / 2)) : List ℤ :=
  List.ofFn (fun t : Fin s => e.weights ((halves s).symm t)) ++ [e.target]

theorem ofFn_halves {s : ℕ} {α : Type} (f : Fin s → α) :
    List.ofFn (fun i : Fin ((s + 1) / 2) => f (halves s (.inl i))) ++
      List.ofFn (fun j : Fin (s / 2) => f (halves s (.inr j))) = List.ofFn f := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_ofFn]; omega
  · intro i h1 h2
    rw [List.getElem_append]
    split
    · rename_i h; simp only [List.getElem_ofFn]; congr 1 <;> ext <;> simp
    · rename_i h; simp only [List.getElem_ofFn]; simp only [List.length_ofFn] at h
      congr 1 <;> ext <;> simp <;> omega

theorem fields_split {s : ℕ} (coef : ℤ) (e : RowBinLift.Equation ((s + 1) / 2) (s / 2)) :
    fields (RowBinLift.split coef e) = eqF e ++ [coef] := by
  have h := ofFn_halves (fun t : Fin s => e.weights ((halves s).symm t))
  simp only [Equiv.symm_apply_apply] at h
  unfold fields RowBinLift.split eqF
  simp only
  rw [h]; simp

theorem eqF_toHalves {s : ℕ} (c : ExactEquation s) : eqF (toHalves c) = kidL c := by
  unfold eqF toHalves kidL; simp

/-! ## Radix stacking -/

/-- Radix stacking of field lists with base `b` (`stackEquations` as lists). -/
def stackL (s : ℕ) (b : ℤ) : List (List ℤ) → List ℤ
  | [] => List.replicate (s + 1) 0
  | l :: ls => List.zipWith (fun a c => a + b * c) l (stackL s b ls)

theorem eqF_stack {s : ℕ} (b : ℤ) (es : List (RowBinLift.Equation ((s + 1) / 2) (s / 2))) :
    eqF (stackEquations b es) = stackL s b (es.map eqF) := by
  induction es with
  | nil =>
    simp only [stackEquations, eqF, List.map_nil, stackL]
    rw [List.ofFn_const, List.replicate_succ']
  | cons e es ih =>
    simp only [stackEquations, List.map_cons, stackL]
    rw [← ih]
    apply List.ext_getElem
    · simp [eqF]
    · intro i h1 h2
      simp only [List.getElem_zipWith]
      have hl : i < s + 1 := by simpa [eqF] using h1
      by_cases hi : i < s
      · simp [eqF, List.getElem_append, hi]
      · have : i = s := by omega
        subst this; simp [eqF, List.getElem_append]

/-- The canonical base's magnitude sum: `Σ` of the absolute values of all fields. -/
def magL (ls : List (List ℤ)) : ℕ := (ls.map fun l => (l.map Int.natAbs).sum).sum

theorem magnitude_eqF {s : ℕ} (e : RowBinLift.Equation ((s + 1) / 2) (s / 2)) :
    SupplierPrime.equationMagnitudeBound e = ((eqF e).map Int.natAbs).sum := by
  unfold SupplierPrime.equationMagnitudeBound eqF
  rw [List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_apply]
  congr 1
  exact (Equiv.sum_comp (halves s).symm (fun u => (e.weights u).natAbs)).symm

/-- One packed cut's fields: the stacked weights and target with base `Σ|·| + 1`, then the coefficient. -/
def cutL (s : ℕ) (coef : ℤ) (ls : List (List ℤ)) : List ℤ := stackL s ((magL ls + 1 : ℕ) : ℤ) ls ++ [coef]

theorem fields_cut {s : ℕ} (coef : ℤ) (es : List (RowBinLift.Equation ((s + 1) / 2) (s / 2))) :
    fields (RowBinLift.split coef (SupplierEstimator.canonicalEquationStack es)) = cutL s coef (es.map eqF) := by
  rw [fields_split]
  unfold SupplierEstimator.canonicalEquationStack SupplierEstimator.equationListBase cutL
  rw [eqF_stack]
  congr 4
  unfold magL
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp [magnitude_eqF]

/-! ## Tuples and the inner contribution -/

theorem tuples_map {α β : Type} (f : α → β) (Ls : List (List α)) :
    tuples (Ls.map (List.map f)) = (tuples Ls).map (List.map f) := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
    simp only [List.map_cons, tuples, ih, List.flatMap_map, List.map_flatMap, List.map_map]
    rfl

/-- The inner contribution `Σ_j w_j x_j` with `x_j` bit `j` of `c` (low bit first). -/
def innerDot : List ℤ → ℕ → ℤ
  | [], _ => 0
  | w :: ws, c => (if c % 2 = 1 then w else 0) + innerDot ws (c / 2)

theorem innerDot_ofFn {k : ℕ} (w : Fin k → ℤ) (c : ℕ) :
    innerDot (List.ofFn w) c = ∑ j, w j * if c.testBit j.val then 1 else 0 := by
  induction k generalizing c with
  | zero => simp [innerDot]
  | succ k ih =>
    rw [List.ofFn_succ, innerDot, ih, Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.val_zero, Nat.testBit_zero]
      by_cases h : c % 2 = 1 <;> simp [h]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.val_succ, Nat.testBit_succ]

/-! ## The encoded tabulation -/

/-- One variable occurrence of a monomial, with its role resolved: the reference flag and the gate's threshold,
inner weights and outer weights (in the layout's order). -/
structure Occ where
  ref : Bool
  thr : ℤ
  inW : List ℤ
  outW : List ℤ

/-- The data of lem:print as the cut machine reads it: the inner and outer dimensions, the indicator of `H` over
the inner indices, and the monomials (occurrences in decreasing variable order, coefficient). -/
structure Code where
  k : ℕ
  s : ℕ
  hb : List Bool
  terms : List (List Occ × ℤ)

/-- The exact children (as field lists) of an occurrence at the inner point with index `c`: lem:exact for the gate
restricted to `x` (or to `0^I` for a reference variable). -/
def Occ.kids (o : Occ) (c : ℕ) : List (List ℤ) :=
  compileL o.outW (o.thr - (if o.ref then 0 else innerDot o.inW c) - 1)

namespace Code
variable (C : Code)

/-- A monomial's cuts (its occurrences are stored in decreasing variable order). -/
def termCutsL (c : ℕ) (t : List Occ × ℤ) : List (List ℤ) :=
  (tuples (t.1.reverse.map fun o => o.kids c)).map (cutL C.s t.2)

def pointCutsL (c : ℕ) : List (List ℤ) := C.terms.flatMap (C.termCutsL c)

/-- All cuts, as field lists. -/
def cutsL : List (List ℤ) :=
  (List.range (2 ^ C.k)).flatMap fun c => if C.hb.getD c false then C.pointCutsL c else []

end Code

/-- The occurrence of variable `v`: its role's flag and gate, the gate's weights split by the layout. -/
def occ {n k s G V : ℕ} (T : Tabulation n k s G V) (v : Fin V) : Occ where
  ref := (T.role v).reference
  thr := (T.gates (T.role v).gate).threshold
  inW := List.ofFn fun j : Fin k => (T.gates (T.role v).gate).weight (T.layout.symm (.inl j))
  outW := List.ofFn fun t : Fin s => (T.gates (T.role v).gate).weight (T.layout.symm (.inr t))

/-- The encoding of a tabulation: dimensions, the indicator of `H` over the inner indices, the monomials with their
occurrences (roles resolved) in decreasing variable order. -/
def code {n k s G V : ℕ} (T : Tabulation n k s G V) : Code where
  k := k
  s := s
  hb := List.ofFn fun c : Fin (2 ^ k) => decide (innerPoint k c ∈ T.H)
  terms := T.Q.map fun t => ((((t.1.sort (· ≤ ·)).map (occ T)).reverse), t.2)

theorem getD_ofFn {α : Type} {m : ℕ} (f : Fin m → α) (i : Fin m) (d : α) : (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]; simp

theorem occ_kids {n k s G V : ℕ} (T : Tabulation n k s G V) (c : Fin (2 ^ k)) (v : Fin V) :
    (occ T v).kids c.val = (T.kids (innerPoint k c) v).map eqF := by
  unfold Occ.kids Tabulation.kids
  simp only [occ, List.map_map]
  have e : eqF ∘ toHalves = @kidL s := funext fun c => eqF_toHalves c
  rw [e, exactChildren, compileL_eq]
  congr 1
  unfold restrict roleInner
  by_cases hr : (T.role v).reference
  · simp [hr]
  · simp only [hr, if_false, Bool.false_eq_true]
    rw [innerDot_ofFn]
    rfl

theorem exactCuts_fields {n k s G V : ℕ} (T : Tabulation n k s G V) :
    T.exactCuts.map fields = (code T).cutsL := by
  unfold Tabulation.exactCuts Code.cutsL
  rw [List.map_flatMap]
  have hk : (code T).k = k := rfl
  rw [hk, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  congr 1; funext c
  have hh : (code T).hb.getD c.val false = decide (innerPoint k c ∈ T.H) := getD_ofFn _ c false
  rw [hh]
  by_cases hH : innerPoint k c ∈ T.H
  · simp only [hH, if_true, decide_true]
    unfold Tabulation.pointCuts Code.pointCutsL
    rw [List.map_flatMap]
    simp only [code, List.flatMap_map]
    congr 1; funext t
    unfold Tabulation.termCuts Code.termCutsL
    rw [List.reverse_reverse, List.map_map, List.map_map]
    have e1 : (fields ∘ fun es => RowBinLift.split t.2 (SupplierEstimator.canonicalEquationStack es)) =
        (cutL s t.2) ∘ List.map eqF := funext fun es => fields_cut t.2 es
    rw [e1, ← List.map_map, ← tuples_map, List.map_map]
    congr 2
    apply List.map_congr_left
    intro v _
    exact (occ_kids T c v).symm
  · simp [hH]

end NearCubicGates.Close.TabMachine
