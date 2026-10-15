import Proof.PCP.PCPPSubstitutionRequest

/-! The agreed native descriptor has exactly three natural fields. The
canonical circuit codec still uses its literal two/three-field tagged list. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeSchema
open RepairRepresentation ExecutableInterfaces CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tag {n : ℕ} : BooleanNode n → Fin 5
  | .const _ => 0
  | .input _ => 1
  | .not _ => 2
  | .and _ _ => 3
  | .or _ _ => 4
def fields {n : ℕ} : BooleanNode n → Fin 3 → ℕ
  | .const b => ![0,b.toNat,0]
  | .input i => ![1,i.val,0]
  | .not j => ![2,j,0]
  | .and j k => ![3,j,k]
  | .or j k => ![4,j,k]
def native {n : ℕ} (node : BooleanNode n) : List Bool :=
  natWord (fields node 0)++natWord (fields node 1)++natWord (fields node 2)
def binaryNode {n : ℕ} (node : BooleanNode n) := decide (3 ≤ (tag node).val)

theorem first_tag {n : ℕ} (node : BooleanNode n) : fields node 0=(tag node).val := by
  cases node <;> rfl

theorem code_eq {n : ℕ} (node : BooleanNode n) :
    encodeBooleanNode node=if binaryNode node then
      encodeTaggedList [encodeNat (fields node 0),encodeNat (fields node 1),encodeNat (fields node 2)]
    else encodeTaggedList [encodeNat (fields node 0),encodeNat (fields node 1)] := by
  cases node <;> rfl

theorem unused_zero {n : ℕ} (node : BooleanNode n) (h : binaryNode node=false) : fields node 2=0 := by
  cases node <;> first | rfl | contradiction

theorem field_bound {n : ℕ} (node : BooleanNode n) (index : ℕ)
    (hwf : node.WellFormedAt index) (i : Fin 3) : fields node i≤n+index+4 := by
  cases node with
  | const b => cases b <;> fin_cases i <;> dsimp [fields] <;> omega
  | input j => have hj := j.isLt; fin_cases i <;> dsimp [fields] <;> omega
  | not j => change j < index at hwf; fin_cases i <;> dsimp [fields] <;> omega
  | and j k => rcases hwf with ⟨hj,hk⟩; fin_cases i <;> dsimp [fields] <;> omega
  | or j k => rcases hwf with ⟨hj,hk⟩; fin_cases i <;> dsimp [fields] <;> omega

end NearCubicWires.RepairOrdinary.PCPPRequestNodeSchema
