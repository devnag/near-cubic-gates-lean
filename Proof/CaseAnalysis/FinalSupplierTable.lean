import Proof.CaseAnalysis.FinalSupplierRowInput
import Proof.Hierarchy.CompetitorCountTable

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.ThresholdCompiler
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput
open scoped BigOperators

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierTable

noncomputable section

/-- Reindexing the `2^K` bank rows as the live cube: the bank is `Finset.univ.toList`. -/
theorem sum_liveList {q : ℕ} (live : Finset (Fin q)) {M : Type} [AddCommMonoid M]
    (f : BitInput live.card → M) :
    (∑ yi : Fin (liveList live).length, f ((liveList live)[yi.val])) =
      ∑ y : BitInput live.card, f y := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map, liveList]
  exact Finset.sum_map_toList _ _

section Table
variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)
  (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
  (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
  (hpos : 1 ≤ w) (hload : 200 * (live.card + w * (live.card + 2)) ≤ s)

/-- **The printed signed score table**, mod `2^Q`: entry `(i,j)` is the number of bank
polynomials that evaluate to `1` at the half-cube point `(i,j)` (`rowValues`). -/
def table :
    Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U →
      Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U → ℕ :=
  fun i j => CompetitorCountTable.rowValues
    (CloseoutRowsCacheInput.family (pool a live occ s harity) (bank a live occ s harity P))
    (rowInput a live occ s harity P w hs hmon hpos hload) i j

/-- **`hf` of `WholeRetained.run`**: every printed entry is below `2^Q`, because there are only
`2^K` bank rows and `Q = K+1` (`paper.tex:2869`). -/
theorem table_lt
    (i j : Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U) :
    table a live occ s harity P w hs hmon hpos hload i j < 2 ^ (live.card + 1) := by
  have hcount := CompetitorRowCountMeaning.count_le_length
    (CloseoutRowsCacheInput.family (pool a live occ s harity) (bank a live occ s harity P))
    i.val j.val
  have hlen : (CloseoutRowsCacheInput.family (pool a live occ s harity)
      (bank a live occ s harity P)).length = 2 ^ live.card := by
    rw [CloseoutRowsCacheInput.family_length, bank_length]
  have hmono : (2 : ℕ) ^ live.card < 2 ^ (live.card + 1) :=
    Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  rw [hlen] at hcount
  exact Nat.lt_of_le_of_lt hcount hmono

/-- **`hc` of `WholeRetained.run`** — `CloseoutRowsSharedInput.count_modEq`, verbatim. -/
theorem table_modEq
    (i j : Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U) :
    Int.ModEq ((2 : ℤ) ^ (live.card + 1))
      (SupplierPrinter.weightedDominance
        (leftScore (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)))
        (rightScore (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)))
        (weight (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload))) i j)
      (table a live occ s harity P w hs hmon hpos hload i j) :=
  CloseoutRowsSharedInput.count_modEq s (live.card + 1) w (pool a live occ s harity)
    (bank a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
    (bank_rows_le a live occ s harity P w hmon) i j

/-- The bank, read as the `2^K` printed polynomials indexed by the live cube. -/
theorem family_eq_ofFn :
    CloseoutRowsCacheInput.family (pool a live occ s harity) (bank a live occ s harity P) =
      List.ofFn (fun yi : Fin (liveList live).length =>
        CloseoutRowsCacheInput.polynomial (pool a live occ s harity)
          (ExtIncidence.rawRows (indexRow a live occ s harity P yi))) := by
  rw [bank, ExtIncidence.NativeRowInput.bank, ps, CloseoutRowsCacheInput.family]
  simp only [List.map_ofFn, Function.comp_def]

theorem table_eq_exactColumnCount
    (i j : Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U) :
    table a live occ s harity P w hs hmon hpos hload i j =
      exactColumnCount
        (fun (code : ℕ) (y : BitInput live.card) (z : BitInput liveᶜ.card) =>
          encodedFiniteBooleanAssignment
            (fun idx : Fin occ.length =>
              residualVariable (occ.get idx).gate live (joinInput live y z)) code)
        P (residualPoint live s harity (halfPoint ((s+1)/2) (s/2) i.val j.val)) := by
  show CompetitorRowCountMeaning.count
      (CloseoutRowsCacheInput.family (pool a live occ s harity) (bank a live occ s harity P))
      i.val j.val = _
  rw [CompetitorRowCountMeaning.count, family_eq_ofFn]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]
  rw [exactColumnCount, ← sum_liveList live
    (fun y => (exactPolynomialValue
      (fun (code : ℕ) (y' : BitInput live.card) (z' : BitInput liveᶜ.card) =>
        encodedFiniteBooleanAssignment
          (fun idx : Fin occ.length =>
            residualVariable (occ.get idx).gate live (joinInput live y' z')) code)
      P y (residualPoint live s harity (halfPoint ((s+1)/2) (s/2) i.val j.val))).toNat)]
  refine Finset.sum_congr rfl (fun yi _ => ?_)
  rw [← List.get_eq_getElem]
  exact bank_eval a live occ s harity P yi i.val j.val

end Table

section C10
variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)
  (a : DecompositionAlgorithm) (s : ℕ)
  (harity : (s+1)/2+s/2 = (liveSet request liveScale)ᶜ.card)
  (P : StructuralGF2Polynomial) (w : ℕ) (hs : 67 ≤ s)
  (hmon : (CloseoutRowsUniversal.lower a (liveSet request liveScale)
    (symmetricFourfoldOccurrences request) P).length < 2 ^ w)
  (hpos : 1 ≤ w)
  (hload : 200 * ((liveSet request liveScale).card +
    w * ((liveSet request liveScale).card + 2)) ≤ s)

theorem table_eq_exactColumnCount_residualHolds
    (i j : Fin (EquationRow.request (rowInput a (liveSet request liveScale)
      (symmetricFourfoldOccurrences request) s harity P w hs hmon hpos hload)).U) :
    table a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity P w hs
        hmon hpos hload i j =
      exactColumnCount (C10PrinterBridge.residualHolds request liveScale) P
        (residualPoint (liveSet request liveScale) s harity
          (halfPoint ((s+1)/2) (s/2) i.val j.val)) :=
  table_eq_exactColumnCount a (liveSet request liveScale) (symmetricFourfoldOccurrences request)
    s harity P w hs hmon hpos hload i j

end C10

end

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierTable
