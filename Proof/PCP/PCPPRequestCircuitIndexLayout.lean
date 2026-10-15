import Proof.PCP.PCPPRequestCircuitNodes
import Proof.PCP.PCPPRequestNaturalFocus

/-! The output-index field is parsed at the cursor left by the actual node
list. The retained balanced node code is outside the fresh natural bank. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestCircuitIndex
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes := PCPPRequestCircuitNodes.tapes+136
def slots (j : Fin 136) : Fin tapes :=
  if j.val=0 then PCPPRequestCircuitNodes.nativeSource.castAdd 136
  else j.natAdd PCPPRequestCircuitNodes.tapes
def nodeField := PCPPRequestCircuitNodes.framedSlot.castAdd 136
def nativeSource := slots 0
def indexField := slots 85
def indexRaw := slots 86

theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv := congrArg Fin.val he
  have hs := PCPPRequestCircuitNodes.nativeSource.isLt
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega

theorem slots_ne_node (j : Fin 136) : slots j≠nodeField := by
  intro he
  have hv := congrArg Fin.val he
  by_cases hj : j.val=0
  · rw [slots,if_pos hj] at hv
    have h : PCPPRequestCircuitNodes.framedSlot=PCPPRequestCircuitNodes.nativeSource :=
      Fin.ext hv.symm
    exact PCPPRequestCircuitNodes.slots_ne_native 77 h
  · have hnode := PCPPRequestCircuitNodes.framedSlot.isLt
    simp only [slots,hj,ite_false,nodeField,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

noncomputable def first := TapeEmbedding.machine 136 PCPPRequestCircuitNodes.machine
noncomputable def second := RecoveryFocus.machine slots PCPPRequestNatural.machine
noncomputable def machine := Composition.machine first second
def input {n : ℕ} (c : BooleanCircuit n) : Fin tapes → List Bool :=
  Fin.addCases (m:=PCPPRequestCircuitNodes.tapes) (n:=136)
    (PCPPRequestCircuitNodes.input c.nodes (natWord c.output.val)) (fun _ => [])
def budget {n : ℕ} (c : BooleanCircuit n) :=
  PCPPRequestCircuitNodes.budget c.nodes (natWord c.output.val)+1+PCPPRequestNatural.budget c.output.val

end NearCubicWires.RepairOrdinary.PCPPRequestCircuitIndex
