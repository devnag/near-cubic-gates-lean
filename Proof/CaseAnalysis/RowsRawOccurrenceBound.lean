import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.MachineModel.CanonicalFourfoldRowProgram

/-! A bounded test of the paper's occurrence-preserving route. Literal raw
GF2 substitution needs no cancellation for BinLift correctness. Its actual
length supplies the row digit bound; final mode/onset instantiation remains
separate from this constructor-for-constructor calculation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawOccurrenceBound
open CanonicalFourfoldRowProgram
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem mul_length (left right : StructuralGF2Polynomial) :
    (structuralGF2Mul left right).length=left.length*right.length := by
  induction left with
  | nil => simp [structuralGF2Mul]
  | cons m left ih =>
    simp only [structuralGF2Mul,List.flatMap_cons,List.length_append,List.length_map,List.length_cons] at *
    nlinarith

theorem product_bound (A : ℕ) (ps : List StructuralGF2Polynomial)
    (hps : ∀ P∈ps,P.length ≤ A) : (structuralGF2Product ps).length ≤ A^ps.length := by
  induction ps with
  | nil => simp [structuralGF2Product,structuralGF2One]
  | cons P ps ih =>
    have hP:=hps P (by simp)
    have htail:=ih (fun Q hQ=>hps Q (by simp [hQ]))
    change (structuralGF2Mul P (structuralGF2Product ps)).length ≤ A^(ps.length+1)
    rw [mul_length,pow_succ']
    exact Nat.mul_le_mul hP htail

theorem substitute_bound (atom : ℕ→StructuralGF2Polynomial) (A d : ℕ)
    (hA : 1 ≤ A) (ha : ∀ code,(atom code).length ≤ A)
    (source : StructuralGF2Polynomial) (hd : ∀ m∈source,m.length ≤ d) :
    (structuralGF2Substitute atom source).length ≤ source.length*A^d := by
  induction source with
  | nil => simp [structuralGF2Substitute,structuralGF2Zero]
  | cons m source ih =>
    have hm:=product_bound A (m.map atom) (by
      intro P hP
      obtain ⟨code,_,rfl⟩:=List.mem_map.mp hP
      exact ha code)
    simp only [List.length_map] at hm
    have hpow:=Nat.pow_le_pow_right hA (hd m (by simp))
    have ht:=ih (fun m hm=>hd m (by simp [hm]))
    simp only [structuralGF2Substitute,structuralGF2Add,List.length_append,List.length_cons]
    nlinarith

theorem digit_fit (atom : ℕ→StructuralGF2Polynomial) (E a d : ℕ)
    (ha : ∀ code,(atom code).length ≤ 2^a)
    (source : StructuralGF2Polynomial) (hsource : source.length ≤ 2^E)
    (hd : ∀ m∈source,m.length ≤ d) :
    (structuralGF2Substitute atom source).length<2^(E+a*d+1) := by
  have hs:=substitute_bound atom (2^a) d (Nat.one_le_two_pow) ha source hd
  have hm:=Nat.mul_le_mul_right ((2^a)^d) hsource
  have he : 2^E*(2^a)^d=2^(E+a*d) := by rw [←pow_mul,←pow_add]
  rw [he] at hm
  have hp : 0<2^(E+a*d) := Nat.two_pow_pos _
  rw [pow_succ]
  omega

theorem substitution_value (atom : ℕ→StructuralGF2Polynomial)
    (source : StructuralGF2Polynomial) (assignment : ℕ→Bool) :
    evaluateStructuralGF2 assignment (structuralGF2Substitute atom source)=
      evaluateStructuralGF2 (fun code=>evaluateStructuralGF2 assignment (atom code)) source := by
  exact evaluateStructuralGF2_substitute assignment atom source

end NearCubicWires.RepairOrdinary.CloseoutRowsRawOccurrenceBound
