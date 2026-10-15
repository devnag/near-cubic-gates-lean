import Proof.CaseAnalysis.RowsOriginalMeaning
import Proof.CaseAnalysis.RowsEstimatorSubstitutionCapacity

/-! The at-most-four original factors use one expansion-count bound. No
residual input table enters a parser or Cartesian-product capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
open CloseoutRowsEstimator SubstitutionBounds CanonicalFourfoldRowProgram
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowN (W : ℕ) := 5*W+4
def rowR (W : ℕ) := rowCapacity (rowN W)
def rowC (cs : List (List (List ℕ))) (B W : ℕ) :=
  capacity (CloseoutRowsOriginalCache.capacity cs) (B^4) (rowN W)

theorem prefix_fits (cs : List (List (List ℕ))) (B W k : ℕ) (hB : 1 ≤ B)
    (hc : ∀ p∈cs,p.length ≤ B) (hw : ∀ p∈cs,(ExtIncidence.stream p).length ≤ W)
    (m : List ℕ) (valid : Valid cs m) (acc : List (List ℕ))
    (ha : Shape B W k acc) (hk : k+m.length ≤ 4) :
    Fits (rowC cs B W) (rowR W) cs m valid acc := by
  induction m generalizing k acc with
  | nil=>trivial
  | cons i m ih=>
    have hi : i < cs.length:=valid i (by simp)
    have mem:=List.getElem_mem hi
    have atomWidth:=width_of_stream cs[i] W (hw cs[i] mem)
    have hp:=shape_mul B W k acc cs[i] ha (hc cs[i] mem) atomWidth
    have ka : k ≤ 4:=by simp only [List.length_cons] at hk;omega
    have kp : k+1 ≤ 4:=by simp only [List.length_cons] at hk;omega
    have wa : Width acc (4*W):=fun l hl=>(ha.width l hl).trans (Nat.mul_le_mul_right W ka)
    have wp : Width (structuralGF2Mul acc cs[i]) (4*W):=
      fun l hl=>(hp.width l hl).trans (Nat.mul_le_mul_right W kp)
    have fit:=factor_fits (CloseoutRowsOriginalCache.capacity cs) (B^4) (rowN W) (4*W) W acc cs[i]
      (ha.count.trans (Nat.pow_le_pow_right hB ka)) (hp.count.trans (Nat.pow_le_pow_right hB kp))
      wa wp (hw cs[i] mem) (by unfold rowN;omega) (by unfold rowN;omega)
    exact ⟨fit,ih (k+1) (fun j hj=>valid j (by simp [hj])) _ hp (by
      simp only [List.length_cons] at hk;omega)⟩

theorem quartic_fits (cs : List (List (List ℕ))) (B W : ℕ) (hB : 1 ≤ B)
    (hc : ∀ p∈cs,p.length ≤ B) (hw : ∀ p∈cs,(ExtIncidence.stream p).length ≤ W)
    (m : List ℕ) (valid : Valid cs m) (hm : m.length ≤ 4) :
    Fits (rowC cs B W) (rowR W) cs m valid [[]] :=
  prefix_fits cs B W 0 hB hc hw m valid [[]] (unit_shape B W) (by simpa using hm)

theorem cache_capacity (cs : List (List (List ℕ))) (B W : ℕ) :
    CloseoutRowsOriginalCache.capacity cs ≤ rowC cs B W := by
  unfold rowC capacity
  omega

theorem factor_budget (C R : ℕ) (cs : List (List (List ℕ))) (i : ℕ) (hi : i < cs.length)
    (acc : List (List ℕ)) (hc : CloseoutRowsOriginalCache.capacity cs ≤ C)
    (hf : SubstitutionFactor.Fits C R acc cs[i]) :
    CloseoutRowsOriginalFactor.budget R cs i hi acc ≤ 12*C+17 := by
  have rd:=CloseoutRowsRawAtomReusable.read_budget cs i hi
  have cacheBound : CloseoutRowsOriginalCache.budget cs i hi ≤ 2*C+2 := by
    unfold CloseoutRowsOriginalCache.budget CloseoutRowsOriginalCache.capacity
      CloseoutRowsRawAtomReusable.budget CloseoutRowsRawAtomReusable.capacityBound at *
    omega
  have a:=hf.accLength
  have b:=hf.atomLength
  have c:=hf.productTime
  have d:=hf.copyTime
  have e:=hf.productLength
  unfold CloseoutRowsOriginalFactor.budget SubstitutionProduct.budget SubstitutionCopy.budget
  simp only [CloseoutRowsOriginalFactor.value]
  omega

theorem budget_bound (C R : ℕ) (cs : List (List (List ℕ))) (m : List ℕ) (valid : Valid cs m)
    (acc : List (List ℕ)) (hc : CloseoutRowsOriginalCache.capacity cs ≤ C)
    (hf : Fits C R cs m valid acc) : budget R cs m valid acc ≤ m.length*(12*C+19)+1 := by
  induction m generalizing acc with
  | nil=>simp [budget]
  | cons i m ih=>
    have h:=factor_budget C R cs i (valid i (by simp)) acc hc hf.1
    have ht:=ih (fun j hj=>valid j (by simp [hj])) _ hf.2
    simp only [budget,List.length_cons]
    nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
