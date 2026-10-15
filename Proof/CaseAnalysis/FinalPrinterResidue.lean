import Proof.Foundations.SupplierPrinter

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires.SupplierPrinter
open NearCubicWires.ThresholdCompiler

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PrinterResidue

section Residue

variable {Row Column Equation : Type} [Fintype Row]

/-- **S3b (A.12.1, paper.tex:2861–2866).**  The row-sum of truncated lifts agrees with
the exact column count modulo `2^Q`.  Citation of
`SupplierPrinter.liftedColumnScore_modEq_exactColumnCount` in the shape S3c prints. -/
theorem binLift_sum_mod (Q : ℕ)
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (z : Column) :
    (∑ y : Row, binLift Q (polynomialOccurrenceCount holds monomials y z)) % (2 : ℤ) ^ Q =
      (exactColumnCount holds monomials z : ℤ) % (2 : ℤ) ^ Q := by
  have hmod := liftedColumnScore_modEq_exactColumnCount Q holds monomials z
  unfold liftedColumnScore Int.ModEq at hmod
  exact hmod

/-- **S3d (A.12.1, paper.tex:2869–2870).**  "Because \(0\le N_P(z)\le 2^K<2^Q\), the least
nonnegative residue determines the exact count."  Citation of
`SupplierPrinter.recoveredColumnCount_eq` (itself from `exactColumnCount_le_card`), with
the live cube bounded by `2^K` and thm:batch's `Q ≥ K + 1`. -/
theorem exactColumnCount_eq_residue {K Q : ℕ}
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (z : Column)
    (hK : Fintype.card Row ≤ 2 ^ K) (hQ : K < Q) :
    exactColumnCount holds monomials z =
      Int.toNat
        ((∑ y : Row, binLift Q (polynomialOccurrenceCount holds monomials y z)) %
          (2 : ℤ) ^ Q) := by
  have hcard : Fintype.card Row < 2 ^ Q :=
    lt_of_le_of_lt hK (Nat.pow_lt_pow_right Nat.one_lt_two hQ)
  have hrecovered := recoveredColumnCount_eq Q holds monomials z hcard
  unfold recoveredColumnCount liftedColumnScore at hrecovered
  exact hrecovered.symm

end Residue

section Generated

variable {Row Column Equation : Type}

/-- One subset occurrence for a fixed monomial list: the exponent `j` (subset size
`j + 1`, native coefficient `(-2)^j`) and the subset of monomial positions. -/
abbrev SubsetOccurrence (monomials : List (List Equation)) : Type :=
  Σ _ : ℕ, Finset (Fin monomials.length)

/-- The input-independent subset family of A.12.1 for one live row: every subset of
size `j + 1` of the monomial positions, for `j < min Q N_mon`. -/
def subsetOccurrences (Q : ℕ) (monomials : List (List Equation)) :
    Finset (SubsetOccurrence monomials) :=
  (Finset.range (min Q monomials.length)).sigma fun j =>
    (Finset.univ : Finset (Fin monomials.length)).powersetCard (j + 1)

/-- "Hardwiring all \(2^K\) live assignments and retaining every subset occurrence":
the generated signed exact-threshold occurrences (paper.tex:2870–2872). -/
def generatedOccurrences [Fintype Row] (Q : ℕ) (monomials : List (List Equation)) :
    Finset (Row × SubsetOccurrence monomials) :=
  (Finset.univ : Finset Row) ×ˢ subsetOccurrences Q monomials

/-- The native signed value of one occurrence at residual column `z`: coefficient
`(-2)^j` on a size-`(j+1)` subset, times the indicator that every monomial of the
subset is true at `(y, z)`. -/
def signedOccurrenceValue
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (z : Column)
    (occurrence : Row × SubsetOccurrence monomials) : ℤ :=
  (-2 : ℤ) ^ occurrence.2.1 *
    (if occurrence.2.2 ⊆ trueMonomialOccurrences holds monomials occurrence.1 z
      then 1 else 0)

/-- One live row: `binLift` is the signed sum over its subset occurrences
(`binLift_eq_fullOccurrenceSubsetExpansion`, expanded to occurrences). -/
theorem binLift_eq_sum_subsetOccurrences (Q : ℕ)
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (y : Row) (z : Column) :
    binLift Q (polynomialOccurrenceCount holds monomials y z) =
      ∑ occurrence ∈ subsetOccurrences Q monomials,
        signedOccurrenceValue holds monomials z (y, occurrence) := by
  rw [binLift_eq_fullOccurrenceSubsetExpansion]
  unfold subsetOccurrences
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  unfold signedOccurrenceValue trueOccurrenceSubsetCount
  dsimp only
  rw [← Finset.mul_sum, Finset.sum_boole]

/-- All live rows: the printed row-sum is the signed sum over the generated occurrences. -/
theorem binLift_sum_eq_sum_generatedOccurrences [Fintype Row] (Q : ℕ)
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (z : Column) :
    (∑ y : Row, binLift Q (polynomialOccurrenceCount holds monomials y z)) =
      ∑ occurrence ∈ generatedOccurrences Q monomials,
        signedOccurrenceValue holds monomials z occurrence := by
  unfold generatedOccurrences
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y _
  exact binLift_eq_sum_subsetOccurrences Q holds monomials y z

theorem subsetOccurrences_card (Q : ℕ) (monomials : List (List Equation)) :
    (subsetOccurrences Q monomials).card =
      ∑ j ∈ Finset.range (min Q monomials.length), monomials.length.choose (j + 1) := by
  unfold subsetOccurrences
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- paper.tex:2872–2876: "produces exactly
\(s_{\mathrm{gen}} = 2^K\sum_{j=1}^{\min\{Q,N_{\mathrm{mon}}\}}\binom{N_{\mathrm{mon}}}j\)"
(the sum is reindexed by `j ↦ j + 1`; `Fintype.card Row = 2^K` on the live cube). -/
theorem generatedOccurrences_card [Fintype Row] (Q : ℕ)
    (monomials : List (List Equation)) :
    (generatedOccurrences (Row := Row) Q monomials).card =
      Fintype.card Row *
        ∑ j ∈ Finset.range (min Q monomials.length), monomials.length.choose (j + 1) := by
  unfold generatedOccurrences
  rw [Finset.card_product, Finset.card_univ, subsetOccurrences_card]

/-- paper.tex:2876–2878: \(\sum_{j=1}^{\min\{Q,N\}}\binom Nj \le Q\max\{1,N\}^Q\). -/
theorem sum_choose_le_mul_max_pow (Q N : ℕ) :
    ∑ j ∈ Finset.range (min Q N), N.choose (j + 1) ≤ Q * max 1 N ^ Q := by
  calc ∑ j ∈ Finset.range (min Q N), N.choose (j + 1)
      ≤ (Finset.range (min Q N)).card • (max 1 N ^ Q) := by
        apply Finset.sum_le_card_nsmul
        intro j hj
        have hj' : j + 1 ≤ Q := by
          have := Finset.mem_range.mp hj
          omega
        calc N.choose (j + 1) ≤ N ^ (j + 1) := Nat.choose_le_pow N (j + 1)
          _ ≤ max 1 N ^ (j + 1) := Nat.pow_le_pow_left (le_max_right 1 N) (j + 1)
          _ ≤ max 1 N ^ Q := Nat.pow_le_pow_right (by omega) hj'
    _ = min Q N * max 1 N ^ Q := by rw [Finset.card_range, smul_eq_mul]
    _ ≤ Q * max 1 N ^ Q := Nat.mul_le_mul_right _ (min_le_left Q N)

theorem generatedOccurrences_card_le [Fintype Row] {K : ℕ} (Q : ℕ)
    (monomials : List (List Equation)) (hK : Fintype.card Row ≤ 2 ^ K) :
    (generatedOccurrences (Row := Row) Q monomials).card ≤
      2 ^ K * Q * max 1 monomials.length ^ Q := by
  rw [generatedOccurrences_card, Nat.mul_assoc]
  exact Nat.mul_le_mul hK (sum_choose_le_mul_max_pow Q monomials.length)

/-- **S3b's ledger (A.12.1, paper.tex:2870–2878), fused to its duty.**  The printed
`binLift` row-sum is the signed sum over the generated occurrences, and there are
at most \(2^K Q \max\{1,N_{\mathrm{mon}}\}^Q\) of them. -/
theorem sgen_le [Fintype Row] {K : ℕ} (Q : ℕ)
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (z : Column)
    (hK : Fintype.card Row ≤ 2 ^ K) :
    ((∑ y : Row, binLift Q (polynomialOccurrenceCount holds monomials y z)) =
        ∑ occurrence ∈ generatedOccurrences Q monomials,
          signedOccurrenceValue holds monomials z occurrence) ∧
      (generatedOccurrences (Row := Row) Q monomials).card ≤
        2 ^ K * Q * max 1 monomials.length ^ Q :=
  ⟨binLift_sum_eq_sum_generatedOccurrences Q holds monomials z,
    generatedOccurrences_card_le Q monomials hK⟩

end Generated

section LiveCube

variable {Column Equation : Type}

theorem card_bitInput_eq (K : ℕ) : Fintype.card (BitInput K) = 2 ^ K := by
  rw [Fintype.card_fun]
  simp

/-- `exactColumnCount_eq_residue` on the paper's live cube \(\{0,1\}^K\). -/
theorem exactColumnCount_eq_residue_bitInput {K Q : ℕ}
    (holds : Equation → BitInput K → Column → Bool)
    (monomials : List (List Equation)) (z : Column) (hQ : K < Q) :
    exactColumnCount holds monomials z =
      Int.toNat
        ((∑ y : BitInput K, binLift Q (polynomialOccurrenceCount holds monomials y z)) %
          (2 : ℤ) ^ Q) :=
  exactColumnCount_eq_residue holds monomials z (card_bitInput_eq K).le hQ

/-- `sgen_le` on the paper's live cube \(\{0,1\}^K\). -/
theorem sgen_le_bitInput {K : ℕ} (Q : ℕ)
    (holds : Equation → BitInput K → Column → Bool)
    (monomials : List (List Equation)) (z : Column) :
    ((∑ y : BitInput K, binLift Q (polynomialOccurrenceCount holds monomials y z)) =
        ∑ occurrence ∈ generatedOccurrences Q monomials,
          signedOccurrenceValue holds monomials z occurrence) ∧
      (generatedOccurrences (Row := BitInput K) Q monomials).card ≤
        2 ^ K * Q * max 1 monomials.length ^ Q :=
  sgen_le Q holds monomials z (card_bitInput_eq K).le

end LiveCube

end NearCubicWires.RepairSource.CloseoutFinal.C10PrinterResidue
