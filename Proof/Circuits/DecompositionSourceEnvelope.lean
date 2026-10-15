import Proof.Circuits.DecompositionRuntime
import Proof.Circuits.DecompositionSchemaRun

/-! The source's own fresh output bounds the complete local serializer.
The common polynomial includes arity, even when the source emits no child. -/
namespace NearCubicWires.RepairOrdinary.DecompositionResource
open LocalBitMultitape RepairRepresentation DecompositionSchema ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def parameter (r : ExactDecompositionRequest) := r.arity+r.gate.encodingBits+1
def sourceScale (a : DecompositionAlgorithm) := 8*(a.coefficient+2)
def sourceCoefficient (D C : ℕ) (a : DecompositionAlgorithm) :=
  (coefficient D C+53+a.coefficient+1)*(sourceScale a)^(D+2)
def sourceDegree (D : ℕ) (a : DecompositionAlgorithm) := (a.degree+1)*(D+2)

theorem measured_bound (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    r.arity+measured (a.output r).children+1 ≤
      sourceScale a*(parameter r)^(a.degree+1) := by
  let S := parameter r
  let B := DecompositionSource.sourceBudget a r
  have hS : 1 ≤ S := by dsimp [S,parameter]; omega
  have hA : r.arity+1 ≤ S := by dsimp [S,parameter]; omega
  have hout := DecompositionSource.output_length a r
  have hbit : natBitLength r.arity ≤ r.arity+1 := by
    unfold natBitLength
    have := Nat.log_le_self 2 r.arity
    omega
  have hm : measured (a.output r).children ≤ 4*r.arity+2*B+7 := by
    unfold measured payload
    rw [frame_length,List.length_append,DecompositionSource.natWord_length]
    change (exactListWord (a.output r).children).length ≤ B at hout
    omega
  have hpow : S^a.degree ≤ S^(a.degree+1) := Nat.pow_le_pow_right hS (by omega)
  have hlinear : S ≤ S^(a.degree+1) := by
    calc S=S^1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right hS (by omega)
  have hone : 1 ≤ S^(a.degree+1) := Nat.one_le_pow _ _ hS
  have hB : B ≤ a.coefficient*S^(a.degree+1) := Nat.mul_le_mul_left _ hpow
  change r.arity+measured (a.output r).children+1 ≤ 8*(a.coefficient+2)*S^(a.degree+1)
  nlinarith

theorem source_power (D : ℕ) (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    (r.arity+measured (a.output r).children+1)^(D+2) ≤
      (sourceScale a)^(D+2)*(parameter r)^sourceDegree D a := by
  calc
    _ ≤ (sourceScale a*(parameter r)^(a.degree+1))^(D+2) := Nat.pow_le_pow_left (measured_bound a r) _
    _ = _ := by rw [mul_pow,←pow_mul]; rfl

theorem sourceCoefficient_positive (D C : ℕ) (a : DecompositionAlgorithm) :
    0<sourceCoefficient D C a := by
  unfold sourceCoefficient sourceScale
  positivity

theorem children_bound (D C : ℕ) (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    (a.output r).children.length ≤ sourceCoefficient D C a*(parameter r)^sourceDegree D a := by
  have hS : 1 ≤ parameter r := by unfold parameter; omega
  have hd : a.degree ≤ sourceDegree D a := by unfold sourceDegree; nlinarith
  have hs : 1 ≤ (sourceScale a)^(D+2) := Nat.one_le_pow _ _ (by unfold sourceScale; omega)
  have hc : a.coefficient ≤ sourceCoefficient D C a := by unfold sourceCoefficient; nlinarith
  exact (DecompositionSource.children_bound a r).trans
    (Nat.mul_le_mul hc (Nat.pow_le_pow_right hS hd))

theorem bits_bound (D C : ℕ) (a : DecompositionAlgorithm) (r : ExactDecompositionRequest)
    (hD : 15 ≤ D+2) :
    natBitLength (output (a.output r).children) ≤
      sourceCoefficient D C a*(parameter r)^sourceDegree D a := by
  have hz : 1 ≤ r.arity+measured (a.output r).children+1 := by omega
  have hb := output_width (a.output r).children
  have hp : (measured (a.output r).children+1)^15 ≤
      (r.arity+measured (a.output r).children+1)^(D+2) := by
    exact (Nat.pow_le_pow_left (by omega) 15).trans (Nat.pow_le_pow_right hz hD)
  have hs := source_power D a r
  have hc : 53 ≤ coefficient D C+53+a.coefficient+1 := by omega
  calc
    _ ≤ 53*(r.arity+measured (a.output r).children+1)^(D+2) := hb.trans (Nat.mul_le_mul_left _ hp)
    _ ≤ (coefficient D C+53+a.coefficient+1)*
        ((sourceScale a)^(D+2)*(parameter r)^sourceDegree D a) := Nat.mul_le_mul hc hs
    _ = _ := by unfold sourceCoefficient; ring

theorem runtime_bound (D C : ℕ) (a : DecompositionAlgorithm) (r : ExactDecompositionRequest)
    (hC : 1 ≤ C)
    (ho : PCPTraversal.budget (PCPSerializerMass.mass (DecompositionCodeBounds.childFields
      (groups (a.output r).children))) ≤ C*(measured (a.output r).children+1)^D) :
    DecompositionSchema.budget D C (a.output r).children ≤
      sourceCoefficient D C a*(parameter r)^sourceDegree D a := by
  have hE : 1 ≤ C*(measured (a.output r).children+1)^D := by
    have hp := Nat.one_le_pow D (measured (a.output r).children+1) (by omega)
    nlinarith
  have hg := global_budget D C (C*(measured (a.output r).children+1)^D) r.arity
    (measured (a.output r).children) (groups (a.output r).children)
    (by rw [word_eq]; rfl) rfl hE (field_count_bound _) (child_count_bound _) ho
  have hs := source_power D a r
  have hc : coefficient D C ≤ coefficient D C+53+a.coefficient+1 := by omega
  calc
    _ ≤ coefficient D C*(r.arity+measured (a.output r).children+1)^(D+2) := hg
    _ ≤ (coefficient D C+53+a.coefficient+1)*
        ((sourceScale a)^(D+2)*(parameter r)^sourceDegree D a) := Nat.mul_le_mul hc hs
    _ = _ := by unfold sourceCoefficient; ring

end NearCubicWires.RepairOrdinary.DecompositionResource
