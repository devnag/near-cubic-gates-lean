import Proof.CaseAnalysis.RowsEnumeratedCuts
import Proof.CaseAnalysis.RowsCommonInput

/-! The native cache fixes the actual common coordinate width. Incidence
lists retain every monomial occurrence, including empty monomials. Native
coordinate order is exactly the signed cut order consumed by the row printer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCacheInput
open RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
open MatrixScoreBatch RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coordinates {l r : ℕ} (e : LabelledEquation (Fin (l+r))) : Equation l r :=
  ⟨Sum.elim (fun i => e.weights (i.castAdd r)) (fun i => e.weights (i.natAdd l)),e.target⟩

theorem coordinates_magnitude {l r : ℕ} (e : LabelledEquation (Fin (l+r))) :
    equationMagnitudeBound (coordinates e)=equationMagnitudeBound e := by
  simp [coordinates,equationMagnitudeBound,Fintype.sum_sum_type,Fin.sum_univ_add]

theorem cut_word {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (p : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (c : ℤ) :
    RowTupleCutBody.word gs p rows ds c=cutWord p
      (split c (coordinates (RowCoordinateLoop.equation gs
        (RowTupleCommonEquation.indices gs.length rows ds)))) := by
  simp [RowTupleCutBody.word,RowCoordinateLoop.equationWord,EquationWidenLoop.stream,
    cutWord,fields,split,coordinates,List.ofFn_add,List.flatMap_append,List.append_assoc]
  congr 1

def monomial {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (bits : List Bool) :=
  (RowCachedEquation.equations gs (RowTupleCommonEquation.one gs.length bits)).map coordinates
def polynomial {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (rows : List (List Bool)) :=
  rows.map (monomial gs)
def family {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (bank : List (List (List Bool))) :=
  bank.map (polynomial gs)

theorem family_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (bank : List (List (List Bool))) : (family gs bank).length=bank.length := by simp [family]

theorem one_length (N : ℕ) (bits : List Bool) :
    (RowTupleCommonEquation.one N bits).length≤N := by
  unfold RowTupleCommonEquation.one
  split_ifs with h
  · exact (RowMaskMeaning.typed_le N 0 bits (by omega)).trans h
  · simp

theorem monomial_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (bits : List Bool) :
    (monomial gs bits).length≤gs.length := by
  simpa only [monomial,RowCachedEquation.equations,List.length_map] using one_length gs.length bits

theorem monomial_fit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (bits : List Bool)
    (e : Equation l r) (he : e∈monomial gs bits) :
    equationMagnitudeBound e<2^(RowCachedCoordinateBounds.width gs) := by
  obtain ⟨native,hn,rfl⟩ := List.mem_map.mp he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hn
  rw [coordinates_magnitude]
  exact RowCachedEquation.cache_radix_safe gs i

theorem family_lengths {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (bank : List (List (List Bool))) (ms : List (List (Equation l r)))
    (hm : ms∈family gs bank) (m : List (Equation l r)) (hmem : m∈ms) : m.length≤gs.length := by
  obtain ⟨rows,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨bits,_,rfl⟩ := List.mem_map.mp hmem
  exact monomial_length gs bits

theorem family_fit {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (bank : List (List (List Bool))) (ms : List (List (Equation l r)))
    (hm : ms∈family gs bank) (e : Equation l r) (he : e∈ms.flatten) :
    equationMagnitudeBound e<2^(RowCachedCoordinateBounds.width gs) := by
  obtain ⟨rows,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨m,hm,he⟩ := List.mem_flatten.mp he
  obtain ⟨bits,_,rfl⟩ := List.mem_map.mp hm
  exact monomial_fit gs bits e he

def input (s Q : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2)))
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100≤2^s) : EquationRow.Input :=
  CloseoutRows.commonInput s (RowCachedCoordinateBounds.width gs) gs.length Q (family gs bank)
    hs hg (family_lengths gs bank) (family_fit gs bank)

theorem input_width (s Q : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2)))
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100≤2^s) :
    (EquationRow.request (input s Q gs bank hs hg)).p=
      ((exactListWord gs).length+1)*(gs.length*Q)+Q+1 := rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsCacheInput
