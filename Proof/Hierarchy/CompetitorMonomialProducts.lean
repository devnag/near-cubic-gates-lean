import Proof.Hierarchy.CompetitorValidityMidpoint

/-! Actual signed monomial contribution at the scalar fold. The exact
natural count and its paper denominator are multiplied by the guessed
rational coefficient's two sign parts and denominator. Only bounded scalar
words enter; the parent matrix tables are neither copied nor simulated. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialProducts
open LocalBitMultitape SignedSortKey CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positive (q : ℚ) := q.num.toNat
def negative (q : ℚ) := (-q.num).toNat
def operands (q : ℚ) : Fin 4 → ℕ := ![positive q,negative q,q.den,0]
def input (b : ℕ) (q : ℚ) (count denominator : ℕ) : Fin 67 → List Bool :=
  CompetitorRationalProducts.input (width b) b (operands q) denominator count
def contribution (q : ℚ) (count denominator : ℕ) : CompetitorValidity.Estimate :=
  ⟨positive q*count,negative q*count,q.den*denominator⟩

theorem sign_parts (q : ℚ) : (positive q : ℚ)-negative q=(q.num : ℚ) := by
  have he : ((positive q : ℕ) : ℤ)-((negative q : ℕ) : ℤ)=q.num := by
    unfold positive negative
    omega
  exact_mod_cast he

theorem contribution_value (q : ℚ) (count denominator : ℕ) :
    (contribution q count denominator).value=q*((count : ℚ)/denominator) := by
  change (((positive q*count : ℕ) : ℚ)-(negative q*count : ℕ))/(q.den*denominator : ℕ)=_
  push_cast
  rw [← sub_mul,sign_parts,← div_mul_div_comm,Rat.num_div_den]

theorem contribution_denominator_positive (q : ℚ) (count denominator : ℕ) (hd : 0<denominator) :
    0<(contribution q count denominator).denominator := Nat.mul_pos q.pos hd

theorem products_bound (b : ℕ) : productsCost (width b) b≤2000*(b+1)^2 := by
  unfold productsCost cost width
  nlinarith

theorem monomial_run (b : ℕ) (q : ℚ) (count denominator : ℕ)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) :
    ∃ out,ClockJoin.ReadyRun productsProgram (2000*(b+1)^2) (input b q count denominator) out ∧
      out 10=frame (binary (width b) (contribution q count denominator).positive) ∧
      out 24=frame (binary (width b) (contribution q count denominator).negative) ∧
      out 38=frame (binary (width b) (contribution q count denominator).denominator) ∧
      (∀ j : Fin 7,out (shared j)=input b q count denominator (shared j)) := by
  have hnums : ∀ i,operands q i<2^b := by
    intro i
    fin_cases i
    · exact hp
    · exact hn
    · exact hq
    · positivity
  obtain ⟨out,hr,hstore⟩ := products_run b (operands q) denominator count hnums hd hc
  refine ⟨out,ClockJoin.enlarge productsProgram _ _ _ _ hr (products_bound b),?_,?_,?_,hstore.shared⟩
  · exact hstore.products 0 (by decide)
  · exact hstore.products 1 (by decide)
  · exact hstore.products 2 (by decide)

end NearCubicWires.RepairOrdinary.CompetitorMonomialProducts
