import Proof.Hierarchy.CompetitorFinalTableLayout

/-! Final natural values are justified only after the full signed P/N
sum is present. The output projection keeps exact original row order. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFinalTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneTable CompetitorOddRowSlice
open SourceInterfaces WilliamsProductCertificate WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lowerColumn {u : ℕ} (j : Fin (u/2)) : Fin u :=
  ⟨j.val,lt_of_lt_of_le j.isLt (Nat.div_le_self u 2)⟩
def values {u : ℕ} (odd : Bool) (f : Fin u → Fin u → ℕ) : List ℕ :=
  if odd then rowMajorNatMatrix (fun i j => f i (lowerColumn j)) else rowMajorNatMatrix f
def word {u : ℕ} (q : ℕ) (odd : Bool) (f : Fin u → Fin u → ℕ) := (values odd f).flatMap (binary q)

theorem lower_first {u : ℕ} (he : u/2+u/2=u) (j : Fin (u/2)) : lowerColumn j=firstColumn he j := by
  apply Fin.ext
  rfl

theorem residue_counts {u : ℕ} (w q : ℕ) (state : State (u*u)) (f : Fin u → Fin u → ℕ)
    (hq : q≤w) (hfit : ∀ i,state.positive i<2^w ∧ state.negative i<2^w)
    (hcount : ∀ i : Fin (u*u),f i.divNat i.modNat<2^q)
    (hcongruent : ∀ i : Fin (u*u),Int.ModEq ((2:ℤ)^q)
      ((state.positive i:ℤ)-state.negative i) (f i.divNat i.modNat)) :
    CompetitorResidueTable.residueWords w q (canonical state)=(rowMajorNatMatrix f).flatMap (binary q) := by
  rw [← flat_matrix_values f]
  simp only [CompetitorResidueTable.residueWords,canonical,cells,List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact congrArg (binary q) (CompetitorSignedResidue.residue_eq_count w q (state.positive i)
    (state.negative i) (f i.divNat i.modNat) (hfit i).2 hq (hcount i) (hcongruent i))

theorem values_cardinality {u : ℕ} (odd : Bool) (f : Fin u → Fin u → ℕ) :
    (values odd f).length=if odd then u*(u/2) else u*u := by
  cases odd <;> simp [values,rowMajorNatMatrix_length]

theorem odd_factor_two {u : ℕ} (f : Fin u → Fin u → ℕ) (he : u/2+u/2=u) :
    2*(values true f).length=u*u := by
  rw [values_cardinality]
  simp only [ite_true]
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorFinalTable
