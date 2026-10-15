import Proof.PCP.PCPPRequestNode
import Proof.PCP.PCPPRequestNodeDispatchBounds

/-! The complete physical node call is polynomial in the native descriptor
width, including all natural encoders, classification and tagged cons calls. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeCold
open LocalBitMultitape RepairRepresentation ExecutableInterfaces CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (node : BooleanNode n) :=
  natBitLength (PCPPRequestNodeSchema.fields node 0)+
  natBitLength (PCPPRequestNodeSchema.fields node 1)+natBitLength (PCPPRequestNodeSchema.fields node 2)

theorem atom_mass {n : ℕ} (node : BooleanNode n) :
    (atom node 0).bits.length+(atom node 1).bits.length+(atom node 2).bits.length+1 ≤
      10*(width node+1)^5 := by
  have ha := DecompositionAtom.magnitude_bits (PCPPRequestNodeSchema.fields node 0)
  have hb := DecompositionAtom.magnitude_bits (PCPPRequestNodeSchema.fields node 1)
  have hc := DecompositionAtom.magnitude_bits (PCPPRequestNodeSchema.fields node 2)
  have pw (i : Fin 3) : (natBitLength (PCPPRequestNodeSchema.fields node i)+1)^5 ≤ (width node+1)^5 := by
    apply Nat.pow_le_pow_left
    fin_cases i
    · change natBitLength (PCPPRequestNodeSchema.fields node 0)+1 ≤ width node+1
      unfold width; omega
    · change natBitLength (PCPPRequestNodeSchema.fields node 1)+1 ≤ width node+1
      unfold width; omega
    · change natBitLength (PCPPRequestNodeSchema.fields node 2)+1 ≤ width node+1
      unfold width; omega
  have p0 := pw 0
  have p1 := pw 1
  have p2 := pw 2
  have hp : 1 ≤ (width node+1)^5 := Nat.one_le_pow 5 _ (by omega)
  unfold atom
  omega

theorem budget_envelope {n : ℕ} (node : BooleanNode n) :
    budget node ≤ 5000000000000000000*(width node+1)^12 := by
  have hf := PCPPRequestNodeFields.budget_envelope (PCPPRequestNodeSchema.fields node 0)
    (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)
  have hmass := atom_mass node
  have hd := PCPPRequestNodeDispatch.budget_quadratic
    (atom node 0) (atom node 1) (atom node 2) (PCPPRequestNodeSchema.binaryNode node)
  have hd' : PCPPRequestNodeDispatch.budget
      (atom node 0) (atom node 1) (atom node 2) (PCPPRequestNodeSchema.binaryNode node) ≤
      429496729600*(width node+1)^10 := by
    calc
      _ ≤ 4294967296*((atom node 0).bits.length+(atom node 1).bits.length+(atom node 2).bits.length+1)^2 := hd
      _ ≤ 4294967296*(10*(width node+1)^5)^2 := by gcongr
      _ = _ := by ring
  have hp : (width node+1)^10 ≤ (width node+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  have hone : 1 ≤ (width node+1)^12 := Nat.one_le_pow 12 _ (by omega)
  change PCPPRequestNodeFields.budget _ _ _ ≤ 4000000000000000000*(width node+1)^12 at hf
  unfold budget PCPPRequestNodePrepare.budget
  omega

end NearCubicWires.RepairOrdinary.PCPPRequestNodeCold
