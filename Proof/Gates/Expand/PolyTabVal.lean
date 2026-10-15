import Proof.Gates.Expand.Machine
import Proof.Gates.TabMachine.Back
import Proof.Gates.CounterMachine.PrefixSpec

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand NearCubicGates.Close.Counter

variable (E : ExpandMachine)

def tabT (r : TabReq) : Tabulation r.n r.k r.s r.G r.V := ⟨r.gates, r.layout, r.H, r.role, E.expand ⟨r.V, r.F⟩⟩

theorem tabT_target (r : TabReq) (y : Fin r.s → Bool) : (tabT E r).target y = tabTarget r y := by
  unfold Tabulation.target tabTarget
  apply Finset.sum_congr rfl
  intro x _
  exact (E.ok ⟨r.V, r.F⟩).eval _

theorem coeff_le_absSum {V : ℕ} (P : Terms V) (t : Finset (Fin V) × ℤ) (ht : t ∈ P) : t.2.natAbs ≤ Terms.absSum P := by
  unfold Terms.absSum
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨t, ht, rfl⟩)

theorem tabT_coeff (r : TabReq) (t : Finset (Fin r.V) × ℤ) (ht : t ∈ (tabT E r).Q) : t.2.natAbs ≤ 2 ^ r.F.weight :=
  ((coeff_le_absSum _ t ht).trans (E.ok ⟨r.V, r.F⟩).mass).trans (Formula.mass_le_two_pow_weight r.F)

theorem tabT_bounds (r : TabReq) : (tabT E r).Bounds r.B r.F.degree (r.F.weight + 1) where
  gates := r.hB
  nodup := (E.ok ⟨r.V, r.F⟩).nodup
  degree := (E.ok ⟨r.V, r.F⟩).degree
  coeff := fun t ht => lt_of_le_of_lt (tabT_coeff E r t ht) (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-! ## The printer's order -/

theorem ofFn_val_eq {β : Type} (m : ℕ) (h : ℕ → β) : (List.ofFn fun i : Fin m => h i.val) = (List.range m).map h := by
  apply List.ext_getElem <;> simp

theorem ofFn_ofFn_flatten {α : Type} (U W : ℕ) (g : Fin U → Fin W → α) (h : ℕ → ℕ → α)
    (hg : ∀ (i : Fin U) (j : Fin W), g i j = h i.val j.val) :
    (List.ofFn fun i => List.ofFn fun j => g i j).flatten = (List.range U).flatMap fun i => (List.range W).map (h i) := by
  have e1 : ∀ i : Fin U, (List.ofFn fun j => g i j) = (List.range W).map (h i.val) := by
    intro i
    rw [← ofFn_val_eq]; congr 1; funext j; exact hg i j
  rw [show (List.ofFn fun i => List.ofFn fun j => g i j) = List.ofFn fun i : Fin U => (List.range W).map (h i.val)
    from by congr 1; funext i; exact e1 i]
  have e2 := ofFn_val_eq U (fun i => (List.range W).map (h i))
  rw [e2]
  simp [List.flatMap]

theorem outerPoint_eq (s i j : ℕ) (hi : i < 2 ^ ((s + 1) / 2)) :
    outerPoint s i j = outerOf s (i + 2 ^ ((s + 1) / 2) * j) := by
  funext t
  unfold outerPoint outerOf
  rw [show i + 2 ^ ((s + 1) / 2) * j = 2 ^ ((s + 1) / 2) * j + i by ring, Nat.testBit_two_pow_mul_add j hi]

/-- **The printed list in `printerOrder`.** -/
theorem pvals_input {n k s G V : ℕ} (T : Tabulation n k s G V) (p : ℕ)
    (hfits : ∀ c ∈ T.exactCuts, EquationRow.Fits p c) (hs : 67 ≤ s) (hcap : T.exactCuts.length ^ 100 ≤ 2 ^ s) :
    pvals (T.input p hfits hs hcap).odd (wdOf (T.input p hfits hs hcap)) =
      (CounterMachine.printerOrder s).map fun i => T.target (outerOf s i) := by
  have hv : ∀ (row column : Fin (EquationRow.request (T.input p hfits hs hcap)).U),
      wdOf (T.input p hfits hs hcap) row column = T.target (outerPoint s row.val column.val) :=
    T.input_value p hfits hs hcap
  have hU : (EquationRow.request (T.input p hfits hs hcap)).U = 2 ^ ((s + 1) / 2) := rfl
  unfold pvals CounterMachine.printerOrder
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def]
  by_cases ho : s % 2 = 1
  · have hodd : (T.input p hfits hs hcap).odd = true := by simp [Tabulation.input, ho]
    rw [if_pos hodd]
    have hW : (EquationRow.request (T.input p hfits hs hcap)).U / 2 = 2 ^ (s / 2) := by
      rw [hU, show (s + 1) / 2 = s / 2 + 1 by omega, pow_succ]; simp
    have := ofFn_ofFn_flatten (EquationRow.request (T.input p hfits hs hcap)).U
      ((EquationRow.request (T.input p hfits hs hcap)).U / 2)
      (fun i j => wdOf (T.input p hfits hs hcap) i (CompetitorFinalTable.lowerColumn j))
      (fun i j => T.target (outerOf s (i + 2 ^ ((s + 1) / 2) * j))) (fun i j => by
        rw [hv, outerPoint_eq s _ _ (lt_of_lt_of_eq i.isLt hU)]; rfl)
    rw [this, hW, hU]
  · have hodd : (T.input p hfits hs hcap).odd = false := by simp [Tabulation.input, ho]
    rw [if_neg (by simp [hodd])]
    have := ofFn_ofFn_flatten (EquationRow.request (T.input p hfits hs hcap)).U
      (EquationRow.request (T.input p hfits hs hcap)).U
      (fun i j => wdOf (T.input p hfits hs hcap) i j)
      (fun i j => T.target (outerOf s (i + 2 ^ ((s + 1) / 2) * j))) (fun i j => by
        rw [hv, outerPoint_eq s _ _ (lt_of_lt_of_eq i.isLt hU)])
    rw [this, hU, show (s + 1) / 2 = s / 2 by omega]

end NearCubicGates.Close.Expand.PolyTab
