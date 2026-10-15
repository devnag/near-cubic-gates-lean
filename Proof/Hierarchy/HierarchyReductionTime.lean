import Proof.Hierarchy.HierarchyReduction

/-! Explicit quasilinear payment for the complete padding producer. All
constants are fixed after the hierarchy machine, code, degree and independent
padding allocation coefficient have been selected. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shortCoefficient (D C : ℕ) := D+C.bits.length+4
theorem count_budget (x : List Bool) :
    HierarchyInputLength.budget x≤42*(x.length+1)*(PCPResourceLedger.ell x.length+1) := by
  dsimp [HierarchyInputLength.budget,HierarchyInputLength.rawBudget,ClockInputLength.cost]
  ring_nf
  omega
theorem width_budget (D C n : ℕ) :
    HierarchyWidth.budget D C n≤32*shortCoefficient D C*(PCPResourceLedger.ell n+1) := by
  dsimp [HierarchyWidth.budget,HierarchyWidth.productCost,HierarchyWidth.offset,HierarchyBinary.width,shortCoefficient]
  ring_nf
  omega
theorem bound_budget (D C n : ℕ) :
    HierarchyBound.budget D C n≤512*(shortCoefficient D C)^2*(PCPResourceLedger.ell n+1)^2 := by
  rw [HierarchyBound.budget_formula]
  dsimp [HierarchyBinary.width,shortCoefficient]
  ring_nf
  omega
theorem allocation_budget (a b : ℕ) (x : List Bool) :
    HierarchyAllocation.budget a b x≤32*(a+b+4)*(x.length+1) := by
  dsimp [HierarchyAllocation.budget,HierarchyAllocation.productCost,HierarchyAllocation.offset]
  ring_nf
  omega

def linearCoefficient (k C Cpad : ℕ) (code : List Bool) :=
  2*Cpad+1+HierarchyBinary.header code.length C+2^(k+2)
def runtimeCoefficient (k C Cpad : ℕ) (code : List Bool) :=
  42+32*shortCoefficient (k+2) C+512*(shortCoefficient (k+2) C)^2+
  32*(coefficient Cpad+constant C Cpad code+4)+4*linearCoefficient k C Cpad code+4*code.length+18

theorem budget_bound (k C Cpad : ℕ) (code x : List Bool) :
    budget k C Cpad code x≤runtimeCoefficient k C Cpad code*(x.length+1)*(PCPResourceLedger.ell x.length+1)^2 := by
  let X := x.length+1
  let L := PCPResourceLedger.ell x.length+1
  have hx : 1≤X := by dsimp [X]; omega
  have hl : 1≤L := by dsimp [L]; omega
  have hll : L≤L^2 := by nlinarith
  have h1 : 1≤X*L^2 := by nlinarith
  have hX : X≤X*L^2 := by nlinarith
  have hL : L≤X*L^2 := by nlinarith
  have hXL : X*L≤X*L^2 := Nat.mul_le_mul_left X hll
  have hL2 : L^2≤X*L^2 := by nlinarith
  have hcount := count_budget x
  have hwidth := width_budget (k+2) C x.length
  have hbound := bound_budget (k+2) C x.length
  have halloc := allocation_budget (coefficient Cpad) (constant C Cpad code) x
  have hN : length k C Cpad code x≤linearCoefficient k C Cpad code*X :=
    (PowerSlice.linear_length k (2*Cpad) (HierarchyBinary.header code.length C) x.length).2
  have hc : HierarchyInputLength.budget x≤42*(X*L^2) := by
    calc
      _ ≤ 42*(X*L) := by simpa only [X,L,Nat.mul_assoc] using hcount
      _ ≤ 42*(X*L^2) := Nat.mul_le_mul_left _ hXL
  have hw : HierarchyWidth.budget (k+2) C x.length≤(32*shortCoefficient (k+2) C)*(X*L^2) :=
    hwidth.trans (Nat.mul_le_mul_left _ hL)
  have hb : HierarchyBound.budget (k+2) C x.length≤(512*shortCoefficient (k+2) C^2)*(X*L^2) :=
    hbound.trans (Nat.mul_le_mul_left _ hL2)
  have ha : HierarchyAllocation.budget (coefficient Cpad) (constant C Cpad code) x≤
      (32*(coefficient Cpad+constant C Cpad code+4))*(X*L^2) :=
    halloc.trans (Nat.mul_le_mul_left _ hX)
  have hn : 4*length k C Cpad code x≤(4*linearCoefficient k C Cpad code)*(X*L^2) := by
    calc
      _ ≤ (4*linearCoefficient k C Cpad code)*X := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ hX
  have hcode : codeCost code=4*code.length+4 := by simp [codeCost,frame_length]; omega
  have hrest : 4*code.length+18≤(4*code.length+18)*(X*L^2) := by nlinarith
  unfold budget HierarchyFromInput.budget
  rw [hcode]
  change _ ≤ runtimeCoefficient k C Cpad code*X*L^2
  dsimp only [runtimeCoefficient]
  nlinarith

end NearCubicWires.RepairOrdinary.HierarchyReduction
