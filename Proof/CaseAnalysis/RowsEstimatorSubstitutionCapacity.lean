import Proof.CaseAnalysis.RowsEstimatorSubstitutionWidths

/-! One linear expansion-count capacity covers every temporary prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
open CanonicalFourfoldRowProgram CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowCapacity (N : ℕ):=16*N*N
def capacity (K M N : ℕ):=K+128*(M+1)*(rowCapacity N+N+4)

theorem capacity_bounds (K M N : ℕ) (hn : 1 ≤ N) :
    rowCapacity N ≤ capacity K M N ∧
    M*(3*rowCapacity N+7)+3 ≤ capacity K M N ∧
    (M+1)*N ≤ capacity K M N ∧
    32*((M+1)*N+3) ≤ capacity K M N := by
  unfold capacity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem bounded_word (p : StructuralGF2Polynomial) (M L N : ℕ)
    (hc : p.length ≤ M) (hw : Width p L) (hn : L+2 < N) :
    (ExtIncidence.stream p).length ≤ (M+1)*N := by
  have h:=word_length p L hw
  have hm:=Nat.mul_le_mul hc (show L+2 ≤ N by omega)
  nlinarith

theorem factor_fits (K M N L W : ℕ) (acc atom : StructuralGF2Polynomial)
    (ha : acc.length ≤ M) (hp : (structuralGF2Mul acc atom).length ≤ M)
    (hwa : Width acc L) (hwp : Width (structuralGF2Mul acc atom) L)
    (hatom : (ExtIncidence.stream atom).length ≤ W) (hL : L+2 < N) (hW : W+1 ≤ N) :
    SubstitutionFactor.Fits (capacity K M N) (rowCapacity N) acc atom := by
  have hn : 1 ≤ N:=by omega
  obtain ⟨hR,hprod,hword,hcopy⟩:=capacity_bounds K M N hn
  have wa:=bounded_word acc M L N ha hwa hL
  have wp:=bounded_word (structuralGF2Mul acc atom) M L N hp hwp hL
  have hN : N ≤ (M+1)*N:=by nlinarith
  refine ⟨hR,?_,?_,?_,wa.trans hword,by omega,?_,wp.trans hword⟩
  · intro l hl
    have h:=hwa l hl
    unfold rowCapacity
    nlinarith
  · intro l hl
    have h:=CloseoutRowsRawProductBudget.row_bound l atom
    have hw:=hwa l hl
    have hm:=Nat.mul_le_mul (show (l.flatMap ExtIncidence.block).length+1 ≤ N by omega)
      (show (ExtIncidence.stream atom).length+1 ≤ N by omega)
    unfold rowCapacity
    nlinarith
  · have hm:=Nat.mul_le_mul_right (3*rowCapacity N+7) ha
    unfold CloseoutRowsRawProductLoop.budget
    omega
  · have h:=CloseoutRowsRawPolynomialAdd.budget_bound (structuralGF2Mul acc atom) []
    simp only [CloseoutRowsRawProductBudget.inputLength,ExtIncidence.stream,List.flatMap_nil,
      List.nil_append,List.length_singleton] at h
    change CloseoutRowsRawPolynomialAdd.budget (structuralGF2Mul acc atom) [] ≤ _
    simp only [ExtIncidence.stream] at wp
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
