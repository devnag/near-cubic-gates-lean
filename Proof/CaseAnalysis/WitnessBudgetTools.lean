import Proof.CaseAnalysis.WitnessFamilyBudget

/-! Small algebraic tools for the actual cold preprocessing ledger.
Each rule preserves the existing existential degree before hierarchy choice. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BudgetTools
open PaddedRunnerBudgetClosure RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem comp {f g : ℕ→ℕ} (hf:SourcePoly f) (hg:SourcePoly g) : SourcePoly (fun n=>f (g n)) := by
  obtain ⟨d,K,h⟩:=hf
  exact ((sourcePoly_pow (hg.add (polyDominated_const 1)) d).const_mul K).mono (fun n=>h (g n))

theorem div {f : ℕ→ℕ} (hf:SourcePoly f) (g : ℕ→ℕ) : SourcePoly (fun n=>f n/g n) :=
  hf.mono (fun n=>Nat.div_le_self (f n) (g n))
theorem sub {f : ℕ→ℕ} (hf:SourcePoly f) (g : ℕ→ℕ) : SourcePoly (fun n=>f n-g n) :=
  hf.mono (fun n=>Nat.sub_le (f n) (g n))
theorem max {f g : ℕ→ℕ} (hf:SourcePoly f) (hg:SourcePoly g) : SourcePoly (fun n=>Nat.max (f n) (g n)) :=
  (hf.add hg).mono (fun n=>max_le (Nat.le_add_right (f n) (g n)) (Nat.le_add_left (g n) (f n)))
theorem bits {f : ℕ→ℕ} (hf:SourcePoly f) : SourcePoly (fun n=>natBitLength (f n)) :=
  (hf.add (polyDominated_const 1)).mono (fun n=>PCPPQueryCost.width_le (f n))

macro "budget_poly" : tactic => `(tactic|
  repeat first
  | assumption
  | exact sourcePoly_id
  | exact polyDominated_const _
  | apply PolyDominated.add
  | apply PolyDominated.mul
  | apply sourcePoly_pow
  | apply sourcePoly_logScale
  | apply bits
  | apply div
  | apply sub
  | apply max)

theorem power_cost {f : ℕ→ℕ} (hf:SourcePoly f) (C D : ℕ) :
    SourcePoly (fun n=>DimensionPower.cost C (f n) D) := by
  have upper:SourcePoly (fun n=>2*C+2+D*(6*C*(f n+1)^(D+1)+7)) := by budget_poly
  exact upper.mono (fun n=>DimensionPower.cost_bound D C (f n) D le_rfl)

theorem polynomial_cost {f : ℕ→ℕ} (hf:SourcePoly f) (C D : ℕ) :
    SourcePoly (fun n=>DimensionPolynomial.budget D C (f n)) := by
  have upper:SourcePoly (fun n=>DimensionPolynomial.coefficient D C*(f n+2)^(2*D+2)) := by budget_poly
  exact upper.mono (fun n=>DimensionPolynomial.budget_bound D C (f n))

end NearCubicWires.RepairOrdinary.CloseoutWitness.BudgetTools
