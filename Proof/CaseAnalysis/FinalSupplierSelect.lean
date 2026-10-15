import Proof.CaseAnalysis.FinalPrinterBridge
import Proof.Supplier.RowExternalSelection
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.MachineModel.Runs
import Proof.CaseAnalysis.RowsEstimatorRecord

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch (Step)
open NearCubicWires.RepairOrdinary.CompetitorCountMask (mask selected)
open NearCubicWires.RepairOrdinary.CompetitorFinalTable (lowerColumn)
open NearCubicWires.RepairSource.CloseoutFinal

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierSelect

section Offsets

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- The residual column addressed by physical cell `(row, column)`: the larger external
RIGHT half carries the physical row, the smaller external LEFT half the physical column
(`RowExternalSelection`, `Proof/Supplier/RowExternalSelection.lean`). -/
noncomputable def residualPoint (row column : ℕ) :
    BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card :=
  (normalizedExternalInputEquiv
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm
    (fun a => column.testBit a.val, fun a => row.testBit a.val)

/-- \(\mathbf F(z)=\bigl(C_i(z)\bigr)_i\) (A.3 :1970-1974), a function of the residual
column `z` ALONE (`C10PrinterBridge.residualOffset_spec`). -/
noncomputable def offsetOf
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)
    (circuitIndex : Fin request.circuits.length) : ℕ :=
  C10PrinterBridge.residualOffset request liveScale z circuitIndex

theorem offsetOf_eq (z) (circuitIndex : Fin request.circuits.length) :
    offsetOf request liveScale z circuitIndex =
      occurrenceResidualConstantCount (symmetricFourfoldOccurrences request) liveScale
        (C10PrinterBridge.inputOf request liveScale (fun _ => false) z)
        (symmetricCircuitMask request circuitIndex) :=
  rfl

/-- The physical cell address and the residual column agree: the point `residualPoint`
names is the input `RowExternalSelection.input` builds from the same two nat addresses. -/
theorem inputOf_residualPoint (row column : ℕ) :
    C10PrinterBridge.inputOf request liveScale (fun _ => false)
        (residualPoint request liveScale row column) =
      RowExternalSelection.input (symmetricFourfoldOccurrences request) liveScale row column := by
  rfl

/-- The cell offset in `RowExternalSelection`'s own coordinates: the physical cell
`(row, column)` carries the tuple \(\mathbf F(z)\) of that cell's residual column. -/
theorem offsetOf_residualPoint (row column : ℕ) (circuitIndex : Fin request.circuits.length) :
    offsetOf request liveScale (residualPoint request liveScale row column) circuitIndex =
      (RowExternalSelection.symmetricOffset request liveScale row column circuitIndex).val := by
  rw [offsetOf_eq, inputOf_residualPoint]
  rfl

end Offsets

section Selector

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- A.3 :1978-1979 "During the fixed-column scan compute \(F(z)\) and select the
corresponding printed row": the physical selection bit of cell `(i, j)` is
\(\mathbf 1[\mathbf F(z_{ij})=\mathbf f]\). -/
noncomputable def offsetSelect (f : Fin request.circuits.length → ℕ) {u : ℕ} :
    Fin u → Fin u → Bool :=
  fun i j => decide (offsetOf request liveScale (residualPoint request liveScale i.val j.val) = f)

theorem offsetSelect_eq_select (f : Fin request.circuits.length → ℕ) {u : ℕ} (i j : Fin u) :
    offsetSelect request liveScale f i j =
      RowExternalSelection.select
        (fun a b : Fin u => fun c => (RowExternalSelection.symmetricOffset request liveScale
          a.val b.val c).val) f i j := by
  have h : offsetOf request liveScale (residualPoint request liveScale i.val j.val) =
      fun c => (RowExternalSelection.symmetricOffset request liveScale i.val j.val c).val :=
    funext (offsetOf_residualPoint request liveScale i.val j.val)
  unfold offsetSelect RowExternalSelection.select
  rw [h]

end Selector

section MaskWord

/-- Physical columns of the cropped cell grid (`CompetitorSelectedCells.cells`: an odd
residual arity crops the column half to `u / 2` through `lowerColumn`). -/
def maskColumns (odd : Bool) (u : ℕ) : ℕ := if odd then u / 2 else u

/-- Physical cells of the cropped grid; `cellCount_eq` identifies it with \(2^{q-K}\). -/
def cellCount (odd : Bool) (u : ℕ) : ℕ := u * maskColumns odd u

theorem ofFn_val {α : Type} (v : ℕ) (g : ℕ → α) :
    (List.ofFn fun j : Fin v => g j.val) = (List.range v).map g := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp

theorem flatten_ofFn {α : Type} (u : ℕ) (h : ℕ → List α) :
    (List.ofFn fun i : Fin u => h i.val).flatten = (List.range u).flatMap h := by
  rw [ofFn_val, List.flatMap_def]

theorem range_mul_map {α : Type} (v : ℕ) (g : ℕ → ℕ → α) (u : ℕ) :
    (List.range (u * v)).map (fun k => g (k / v) (k % v)) =
      (List.range u).flatMap (fun a => (List.range v).map (g a)) := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hsplit : (u + 1) * v = u * v + v := by ring
    rw [hsplit, List.range_add, List.map_append, ih, List.range_succ, List.flatMap_append]
    congr 1
    rw [List.map_map]
    have hstep : ∀ b ∈ List.range v,
        ((fun k => g (k / v) (k % v)) ∘ fun x => u * v + x) b = g u b := by
      intro b hb
      have hbv : b < v := List.mem_range.mp hb
      have hv : 0 < v := Nat.lt_of_le_of_lt (Nat.zero_le b) hbv
      have hdiv : (u * v + b) / v = u := by
        rw [Nat.add_comm, Nat.add_mul_div_right b u hv, Nat.div_eq_of_lt hbv, Nat.zero_add]
      have hmod : (u * v + b) % v = b := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbv]
      simp only [Function.comp_apply, hdiv, hmod]
    rw [List.map_congr_left hstep]
    simp

theorem mask_rect {u v : ℕ} (f : Fin u → Fin v → ℕ) (s : Fin u → Fin v → Bool) :
    mask (CompetitorSelectedCells.rect f s) =
      (List.ofFn fun i => List.ofFn fun j => s i j).flatten := by
  simp [mask, CompetitorSelectedCells.rect, List.map_flatten, List.map_ofFn, Function.comp_def]

/-- Row-major scan of a rectangle of Boolean cells whose value depends on the two
addresses only through their numerals. -/
theorem mask_rect_range {u v : ℕ} (sel : Fin u → Fin v → Bool) (G : ℕ → ℕ → Bool)
    (hsel : ∀ (i : Fin u) (j : Fin v), sel i j = G i.val j.val) :
    mask (CompetitorSelectedCells.rect (fun _ _ => (0 : ℕ)) sel) =
      (List.range (u * v)).map (fun k => G (k / v) (k % v)) := by
  have hrow : ∀ i : Fin u, (List.ofFn fun j : Fin v => sel i j) = (List.range v).map (G i.val) := by
    intro i
    rw [show (fun j : Fin v => sel i j) = fun j : Fin v => G i.val j.val from
      funext fun j => hsel i j]
    exact ofFn_val v (G i.val)
  calc mask (CompetitorSelectedCells.rect (fun _ _ => (0 : ℕ)) sel)
      = (List.ofFn fun i : Fin u => List.ofFn fun j : Fin v => sel i j).flatten :=
        mask_rect _ _
    _ = (List.ofFn fun i : Fin u => (List.range v).map (G i.val)).flatten := by
        rw [show (fun i : Fin u => List.ofFn fun j : Fin v => sel i j) =
          fun i : Fin u => (List.range v).map (G i.val) from funext hrow]
    _ = (List.range u).flatMap fun a => (List.range v).map (G a) :=
        flatten_ofFn u fun a => (List.range v).map (G a)
    _ = (List.range (u * v)).map (fun k => G (k / v) (k % v)) := (range_mul_map v G u).symm

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- The column scan's per-cell decision at the physical cell address `(row, column)`. -/
noncomputable def cellBitAt (f : Fin request.circuits.length → ℕ) (row column : ℕ) : Bool :=
  decide (offsetOf request liveScale (residualPoint request liveScale row column) = f)

/-- The selection bit of the `k`-th physical cell in the scan's row-major order. -/
noncomputable def cellBit (f : Fin request.circuits.length → ℕ) (odd : Bool) (u k : ℕ) : Bool :=
  cellBitAt request liveScale f (k / maskColumns odd u) (k % maskColumns odd u)

theorem offsetSelect_eq_cellBitAt (f : Fin request.circuits.length → ℕ) {u : ℕ}
    (i j : Fin u) :
    offsetSelect request liveScale f i j = cellBitAt request liveScale f i.val j.val :=
  rfl

/-- **The mask word `Record.input` reads.**  `CloseoutRowsEstimator.Record.input`
(`Proof/CaseAnalysis/RowsEstimatorRecord.lean`) feeds the cell list
`CompetitorSelectedCells.cells row.odd (fun _ _ => 0) select` to `Table.input`, which
consumes it only through `mask` (`Record.table_mask`, :30).  That word is exactly the
row-major scan of the per-cell selection bits \(\mathbf 1[\mathbf F(z)=\mathbf f]\). -/
theorem mask_cells_eq (f : Fin request.circuits.length → ℕ) (odd : Bool) (u : ℕ) :
    mask (CompetitorSelectedCells.cells odd (fun _ _ => (0 : ℕ))
        (offsetSelect request liveScale f (u := u))) =
      (List.range (cellCount odd u)).map (cellBit request liveScale f odd u) := by
  cases odd with
  | false =>
    exact mask_rect_range (offsetSelect request liveScale f (u := u))
      (cellBitAt request liveScale f) fun i j => rfl
  | true =>
    exact mask_rect_range
      (fun (i : Fin u) (j : Fin (u / 2)) =>
        offsetSelect request liveScale f (u := u) i (lowerColumn j))
      (cellBitAt request liveScale f) fun i j => rfl

end MaskWord

section Reindex

/-- The cropped physical grid has exactly \(2^{q-K}\) cells: `u` rows over the larger
external half, `u / 2` (odd) or `u` (even) columns over the smaller one. -/
theorem cellCount_pow (c : ℕ) : cellCount (decide (c % 2 = 1)) (2 ^ (c - c / 2)) = 2 ^ c := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · have he : c - c / 2 + (c - c / 2) = c := by omega
    simp only [h, cellCount, maskColumns, Nat.zero_ne_one, decide_false, Bool.false_eq_true,
      if_false]
    rw [← pow_add, he]
  · have hR : c - c / 2 = c / 2 + 1 := by omega
    have he : c / 2 + 1 + c / 2 = c := by omega
    simp only [h, cellCount, maskColumns, decide_true, if_true, hR]
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2), ← pow_succ, ← pow_add, he]

theorem sum_fin_congr {a b : ℕ} (h : a = b) (F : ℕ → ℕ) :
    ∑ j : Fin a, F j.val = ∑ j : Fin b, F j.val := by
  subst h
  rfl

/-- The cropped physical grid IS the product of the two external half-cubes: `u = 2^{|right|}`
rows and `2^{|left|}` columns, the odd case cropping through `lowerColumn`. -/
theorem total_eq_sum_half {q : ℕ} (live : Finset (Fin q)) (G : ℕ → ℕ → ℕ) (u : ℕ) (odd : Bool)
    (hu : u = 2 ^ normalizedExternalRightCount live)
    (hodd : odd = decide (liveᶜ.card % 2 = 1)) :
    RowExternalSelection.total odd (fun i j : Fin u => G i.val j.val) =
      ∑ i : Fin (2 ^ normalizedExternalRightCount live),
        ∑ j : Fin (2 ^ normalizedExternalLeftCount live), G i.val j.val := by
  subst hu
  cases odd with
  | false =>
    have hpar : liveᶜ.card % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one liveᶜ.card with h | h
      · exact h
      · rw [h] at hodd
        simp at hodd
    have hRL : normalizedExternalRightCount live = normalizedExternalLeftCount live := by
      unfold normalizedExternalRightCount normalizedExternalLeftCount
      omega
    simp only [RowExternalSelection.total, Bool.false_eq_true, if_false]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact sum_fin_congr (by rw [hRL]) fun b => G i.val b
  | true =>
    have hpar : liveᶜ.card % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one liveᶜ.card with h | h
      · rw [h] at hodd
        simp at hodd
      · exact h
    have hR : normalizedExternalRightCount live = normalizedExternalLeftCount live + 1 := by
      unfold normalizedExternalRightCount normalizedExternalLeftCount
      omega
    have hhalf : 2 ^ normalizedExternalRightCount live / 2 =
        2 ^ normalizedExternalLeftCount live := by
      rw [hR, pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    simp only [RowExternalSelection.total, if_true]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact sum_fin_congr hhalf fun b => G i.val b

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- **The half-cube reindexing.**  Scanning the physical grid row-major — the larger
external RIGHT half as the row, the smaller external LEFT half as the column — visits
every residual column \(z\in\{0,1\}^{q-K}\) exactly once
(`SupplierEstimator.normalizedExternalInputEquiv`, `bitInputIndexEquiv`). -/
theorem sum_residualPoint
    (g : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card → ℕ) :
    (∑ i : Fin (2 ^ normalizedExternalRightCount
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)),
        ∑ j : Fin (2 ^ normalizedExternalLeftCount
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)),
          g (residualPoint request liveScale i.val j.val)) =
      ∑ z, g z := by
  have step1 : ∀ i : Fin (2 ^ normalizedExternalRightCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)),
      (∑ j : Fin (2 ^ normalizedExternalLeftCount
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)),
        g (residualPoint request liveScale i.val j.val)) =
        ∑ b : BitInput (normalizedExternalLeftCount
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)),
          g ((normalizedExternalInputEquiv
              (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm
            (b, bitInputIndexEquiv (normalizedExternalRightCount
              (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)) i)) :=
    fun i => Equiv.sum_comp
      (bitInputIndexEquiv (normalizedExternalLeftCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)))
      (fun b => g ((normalizedExternalInputEquiv
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm
        (b, bitInputIndexEquiv (normalizedExternalRightCount
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)) i)))
  have step2 := Equiv.sum_comp
    (bitInputIndexEquiv (normalizedExternalRightCount
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)))
    (fun a => ∑ b : BitInput (normalizedExternalLeftCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)),
      g ((normalizedExternalInputEquiv
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm (b, a)))
  have step3 := Equiv.sum_comp (normalizedExternalInputEquiv
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm g
  rw [Fintype.sum_prod_type] at step3
  rw [Finset.sum_congr rfl (fun i _ => step1 i), step2, Finset.sum_comm, step3]

end Reindex

section SelectedSum

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

theorem selected_sum
    (f : Fin request.circuits.length → ℕ) (monomials : StructuralGF2Polynomial)
    (u : ℕ) (odd : Bool)
    (hu : u = 2 ^ normalizedExternalRightCount
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))
    (hodd : odd = decide
      ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card % 2 = 1))
    (table : Fin u → Fin u → ℕ)
    (htable : ∀ i j : Fin u, table i j =
      exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials
        (residualPoint request liveScale i.val j.val)) :
    ((selected (CompetitorSelectedCells.cells odd table
        (offsetSelect request liveScale f))).sum : ℕ) =
      ∑ z : BitInput
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
        if offsetOf request liveScale z = f then
          exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials z
        else 0 := by
  have hfun : (fun i j : Fin u =>
        if offsetSelect request liveScale f i j = true then table i j else 0) =
      fun i j : Fin u =>
        (fun a b : ℕ =>
          if offsetOf request liveScale (residualPoint request liveScale a b) = f then
            exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials
              (residualPoint request liveScale a b)
          else 0) i.val j.val := by
    funext i j
    rw [htable i j]
    simp only [offsetSelect, decide_eq_true_eq]
  rw [RowExternalSelection.cells_selected_sum, hfun,
    total_eq_sum_half (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (fun a b : ℕ =>
        if offsetOf request liveScale (residualPoint request liveScale a b) = f then
          exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials
            (residualPoint request liveScale a b)
        else 0) u odd hu hodd,
    sum_residualPoint request liveScale fun z =>
      if offsetOf request liveScale z = f then
        exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials z else 0]

end SelectedSum

section Corollary

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- **A.13.9 :3148-3160, per external row.**  The printed row for offset \(\mathbf f\)
(A.3 :1976-1978) selected at the columns whose actual offset is \(\mathbf f\) contributes
exactly \(\sum_{z:\mathbf F(z)=\mathbf f}T_{e,\mathbf F(z)}(z)\), with
\(T_{e,\mathbf F(z)}(z)=\sum_{y\in\{0,1\}^K}P_{e,\mathbf F(z)}(y,z)\)
(`C10PrinterBridge.exactColumnCount_residualHolds`). -/
theorem selected_sum_printed (denominator : ℕ)
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      denominator)
    (f : Fin request.circuits.length → ℕ) (u : ℕ) (odd : Bool)
    (hu : u = 2 ^ normalizedExternalRightCount
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))
    (hodd : odd = decide
      ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card % 2 = 1))
    (table : Fin u → Fin u → ℕ)
    (htable : ∀ i j : Fin u, table i j =
      exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
        (structuralCanonicalSymmetricFourfoldRow request liveScale denominator sample f)
        (residualPoint request liveScale i.val j.val)) :
    ((selected (CompetitorSelectedCells.cells odd table
        (offsetSelect request liveScale f))).sum : ℕ) =
      ∑ z : BitInput
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
        if offsetOf request liveScale z = f then
          ∑ y : BitInput
              (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card,
            (canonicalSymmetricFourfoldRow request liveScale denominator
              (C10PrinterBridge.inputOf request liveScale y z) sample).toNat
        else 0 := by
  rw [selected_sum request liveScale f _ u odd hu hodd table htable]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : offsetOf request liveScale z = f
  · rw [if_pos hz, if_pos hz, ← hz]
    exact C10PrinterBridge.exactColumnCount_residualHolds request liveScale denominator sample z
  · rw [if_neg hz, if_neg hz]

end Corollary

section Writer

noncomputable def selectWriter {t s : ℕ} (body : Machine t s) :=
  CloseoutRowsDegreeLoop.machine body

/-- **The ONE table factor.**  A.8 :2259 — the column phase "has exponent
\(q-K+h_DL_q+O(1)\)"; thm:batch :2783 — "\(2^{q-K}\operatorname{poly}(q)\)".  One pass over
the \(2^{q-K}\) residual columns at `cellCost` steps per column, plus the driver's three
paid steps per round and its final rewind. -/
def selectFuel (q K cellCost : ℕ) : ℕ := 2 ^ (q - K) * (cellCost + 3) + 3

theorem selectFuel_le (q K cellCost c e : ℕ) (hcell : cellCost ≤ c * (q + 1) ^ e) :
    selectFuel q K cellCost ≤ (c + 6) * (2 ^ (q - K) * (q + 1) ^ e) := by
  have hP : 1 ≤ (q + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have hT : 1 ≤ 2 ^ (q - K) := Nat.one_le_pow _ _ (by norm_num)
  have hstep : 2 ^ (q - K) * (cellCost + 3) + 3 ≤
      2 ^ (q - K) * (c * (q + 1) ^ e + 3) + 3 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hcell 3)) 3
  refine hstep.trans ?_
  have hexpand : 2 ^ (q - K) * (c * (q + 1) ^ e + 3) + 3 =
      c * (2 ^ (q - K) * (q + 1) ^ e) + 3 * 2 ^ (q - K) + 3 := by ring
  have hA : 3 * 2 ^ (q - K) ≤ 3 * (2 ^ (q - K) * (q + 1) ^ e) := by
    have := Nat.mul_le_mul_left (2 ^ (q - K)) hP
    omega
  have hB : (3 : ℕ) ≤ 3 * (2 ^ (q - K) * (q + 1) ^ e) := by
    have : 1 ≤ 2 ^ (q - K) * (q + 1) ^ e := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hC : (c + 6) * (2 ^ (q - K) * (q + 1) ^ e) =
      c * (2 ^ (q - K) * (q + 1) ^ e) + 3 * (2 ^ (q - K) * (q + 1) ^ e) +
        3 * (2 ^ (q - K) * (q + 1) ^ e) := by ring
  rw [hexpand, hC]
  omega

end Writer

section Run

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- The cropped physical grid has exactly \(2^{q-K}\) cells. -/
theorem cellCount_eq (u : ℕ) (odd : Bool)
    (hu : u = 2 ^ normalizedExternalRightCount
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))
    (hodd : odd = decide
      ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card % 2 = 1)) :
    cellCount odd u = 2 ^ (request.q - normalizedLiveCount request.q liveScale) := by
  subst hu
  subst hodd
  rw [show normalizedExternalRightCount
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) =
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card -
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card / 2 from rfl,
    cellCount_pow, C10PrinterBridge.residualArity_eq]

/-- The loop driver's added counter tape is the last one: the body's slots are unchanged. -/
theorem cfg_tapes_castAdd {t s : ℕ} (phase : Fin 5) (data : Configuration t s)
    (total head : ℕ) (i : Fin t) :
    (RepairSource.VerifierDecoding.RepeatMachine.cfg phase data total head).tapes
        (i.castAdd 1) = data.tapes i := by
  simp [RepairSource.VerifierDecoding.RepeatMachine.cfg, controlConfig, TapeEmbedding.config]

theorem select_run {t s : ℕ} (body : Machine t s)
    (source : ℕ → List Bool → Configuration t s) (slot : Fin t) (cellCost : ℕ)
    (f : Fin request.circuits.length → ℕ) (u : ℕ) (odd : Bool) (out : List Bool)
    (hu : u = 2 ^ normalizedExternalRightCount
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))
    (hodd : odd = decide
      ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card % 2 = 1))
    (hslot : ∀ k pre, (source k pre).tapes slot = pre)
    (hstart : ∀ k < cellCount odd u, ∀ pre, (source k pre).control = body.start)
    (hcell : ∀ k < cellCount odd u, ∀ pre, ∃ rc : ExecutionReceipt t s,
      runFrom body cellCost (source k pre) = some rc ∧
      rc.final.heads =
        (source (k + 1) (pre ++ [cellBit request liveScale f odd u k])).heads ∧
      rc.final.tapes =
        (source (k + 1) (pre ++ [cellBit request liveScale f odd u k])).tapes ∧
      rc.steps ≤ cellCost) :
    ∃ T, Step (selectWriter body)
        (selectFuel request.q (normalizedLiveCount request.q liveScale) cellCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (cellCount odd u) 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (cellCount odd u) 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (source (cellCount odd u) (out ++ mask (CompetitorSelectedCells.cells odd
            (fun _ _ => (0 : ℕ)) (offsetSelect request liveScale f (u := u)))))
          (cellCount odd u) 1).heads T ∧
      T (slot.castAdd 1) = out ++ mask (CompetitorSelectedCells.cells odd (fun _ _ => (0 : ℕ))
        (offsetSelect request liveScale f (u := u))) := by
  have hword : (List.range (cellCount odd u)).flatMap
      (fun k => [cellBit request liveScale f odd u k]) =
      mask (CompetitorSelectedCells.cells odd (fun _ _ => (0 : ℕ))
        (offsetSelect request liveScale f (u := u))) := by
    rw [mask_cells_eq, List.map_eq_flatMap]
  have hfuel : cellCount odd u * (cellCost + 3) + 3 =
      selectFuel request.q (normalizedLiveCount request.q liveScale) cellCost := by
    rw [selectFuel, cellCount_eq request liveScale u odd hu hodd]
  obtain ⟨r, hr, hf, hs⟩ := CloseoutRowsDegreeLoop.loop_run body source
    (fun k => [cellBit request liveScale f odd u k]) cellCost (cellCount odd u) hstart hcell out
  rw [hword] at hf
  rw [hfuel] at hr hs
  refine ⟨_, ⟨r, hr, congrArg Configuration.heads hf, congrArg Configuration.tapes hf, hs⟩, ?_⟩
  rw [cfg_tapes_castAdd]
  exact hslot _ _

end Run

section Consumer

/-- **What `Record.input` reads is exactly this mask word.**  `Record.input` feeds the
selector to `Table.input` only through `CompetitorSelectedCells.cells … (fun _ _ => 0)`,
and `Table.input` consumes that list only through `mask` (`Record.table_mask`,
`Proof/CaseAnalysis/RowsEstimatorRecord.lean`).  So two selectors with the same mask
word give the identical physical entry configuration. -/
theorem record_input_congr (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (left right : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (hmask : mask (CompetitorSelectedCells.cells row.odd (fun _ _ => (0 : ℕ)) left) =
      mask (CompetitorSelectedCells.cells row.odd (fun _ _ => (0 : ℕ)) right)) :
    CloseoutRowsEstimator.Record.input p row Q q denominator left =
      CloseoutRowsEstimator.Record.input p row Q q denominator right := by
  unfold CloseoutRowsEstimator.Record.input
  rw [CloseoutRowsEstimator.Record.table_mask p row Q q denominator _ _ hmask]

end Consumer

section ExternalRows

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

noncomputable def offsetRange : Finset (Fin request.circuits.length → ℕ) :=
  Finset.image (fun w : RowOffsets.SymmetricOffsets request => fun c => (w c).val) Finset.univ

theorem offsetOf_mem_offsetRange
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    offsetOf request liveScale z ∈ offsetRange request := by
  refine Finset.mem_image.mpr ⟨RowOffsets.symmetricOffsets request liveScale
    (C10PrinterBridge.inputOf request liveScale (fun _ => false) z), Finset.mem_univ _, rfl⟩

theorem offsetRange_card_le (degree : ℕ) (hfour : request.circuits.length ≤ 4)
    (hcap : ∀ c ∈ request.circuits, c.wireCount ≤ (request.q + 1) ^ degree) :
    (offsetRange request).card ≤ 16 * (request.q + 1) ^ (4 * degree) := by
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_univ]
  exact RowOffsets.symmetric_card_polynomial request degree hfour hcap

/-- **A.13.9 :3155-3164, the whole column sum.**  Summing the per-offset external rows over
the offset range restores \(\sum_zT_{e,\mathbf F(z)}(z)\): each residual column is charged
to exactly the one printed row whose offset is its own \(\mathbf F(z)\). -/
theorem offsets_partition
    (T : (Fin request.circuits.length → ℕ) →
      BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card → ℕ) :
    (∑ f ∈ offsetRange request, ∑ z, if offsetOf request liveScale z = f then T f z else 0) =
      ∑ z, T (offsetOf request liveScale z) z := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [Finset.sum_ite_eq (offsetRange request) (offsetOf request liveScale z)
    (fun f => T f z)]
  exact if_pos (offsetOf_mem_offsetRange request liveScale z)

end ExternalRows

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierSelect
