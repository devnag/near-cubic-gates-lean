import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomialRun
import Proof.CaseAnalysis.RowsRawOccurrenceBound

/-! The physical left accumulator is the paper's ordered raw structural product. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionMonomial
open LocalBitMultitape CloseoutRowsRawPairSeek
open NearCubicWires.CanonicalFourfoldRowProgram
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def atom (cs : List Pair) (i : ℕ) : StructuralGF2Polynomial:=
  let q:=cs[i]?.getD ([],[])
  q.1++q.2
theorem atom_eq (cs : List Pair) (i : ℕ) (hi : i<cs.length) : atom cs i=cs[i].1++cs[i].2 := by
  simp [atom,List.getElem?_eq_getElem hi]

theorem value_fold (cs : List Pair) (m : List ℕ) (valid : Valid cs m) (acc : StructuralGF2Polynomial) :
    value cs m valid acc=(m.map (atom cs)).foldl structuralGF2Mul acc := by
  induction m generalizing acc with
  | nil=>rfl
  | cons i m ih=>
    rw [value,ih,List.map_cons,List.foldl_cons,atom_eq cs i (valid i (by simp))]
    rfl

theorem mul_assoc (a b c : StructuralGF2Polynomial) :
    structuralGF2Mul (structuralGF2Mul a b) c=structuralGF2Mul a (structuralGF2Mul b c) := by
  unfold structuralGF2Mul
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro x _
  rw [List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro y _
  rw [List.map_map]
  apply List.map_congr_left
  intro z _
  simp [List.append_assoc]

theorem fold_product (ps : List StructuralGF2Polynomial) (acc : StructuralGF2Polynomial) :
    ps.foldl structuralGF2Mul acc=structuralGF2Mul acc (structuralGF2Product ps) := by
  induction ps generalizing acc with
  | nil=>simp [structuralGF2Product,structuralGF2Mul,structuralGF2One]
  | cons p ps ih=>
    rw [List.foldl_cons,ih,mul_assoc]
    rfl

theorem unit_value (cs : List Pair) (m : List ℕ) (valid : Valid cs m) :
    value cs m valid [[]]=structuralGF2Product (m.map (atom cs)) := by
  rw [value_fold,fold_product]
  simp [structuralGF2Mul]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionMonomial
