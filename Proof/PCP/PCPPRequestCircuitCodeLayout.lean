import Proof.PCP.PCPPRequestCircuitIndex
import Proof.PCP.PCPPRequestCircuitTag

/-! The literal circuit wrapper shares the two physically produced canonical
operands with the checked fixed two-element encoder. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestCircuitCode
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes := PCPPRequestCircuitIndex.tapes+234
def slots (j : Fin 234) : Fin tapes :=
  if j.val=0 then PCPPRequestCircuitIndex.nodeField.castAdd 234
  else if j.val=1 then PCPPRequestCircuitIndex.indexField.castAdd 234
  else j.natAdd PCPPRequestCircuitIndex.tapes
def rawSlot := slots 232
def framedSlot := slots 222
def nativeSource := PCPPRequestCircuitIndex.nativeSource.castAdd 234

theorem fields_distinct : PCPPRequestCircuitIndex.nodeField≠PCPPRequestCircuitIndex.indexField :=
  (PCPPRequestCircuitIndex.slots_ne_node 85).symm
theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv := congrArg Fin.val he
  have hleft := PCPPRequestCircuitIndex.nodeField.isLt
  have hright := PCPPRequestCircuitIndex.indexField.isLt
  change PCPPRequestCircuitIndex.nodeField.val < PCPPRequestCircuitIndex.tapes at hleft
  change PCPPRequestCircuitIndex.indexField.val < PCPPRequestCircuitIndex.tapes at hright
  have hne : PCPPRequestCircuitIndex.nodeField.val≠PCPPRequestCircuitIndex.indexField.val :=
    fun h => fields_distinct (Fin.ext h)
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega

theorem slots_ne_native (j : Fin 234) : slots j≠nativeSource := by
  intro he
  have hv := congrArg Fin.val he
  by_cases h0 : j.val=0
  · rw [slots,if_pos h0] at hv
    exact PCPPRequestCircuitIndex.slots_ne_node 0 (Fin.ext hv.symm)
  by_cases h1 : j.val=1
  · rw [slots,if_neg h0,if_pos h1] at hv
    have h : PCPPRequestCircuitIndex.slots 85=PCPPRequestCircuitIndex.slots 0 := Fin.ext hv
    have hn := congrArg Fin.val (PCPPRequestCircuitIndex.slots_injective h)
    contradiction
  have hn := PCPPRequestCircuitIndex.nativeSource.isLt
  simp only [slots,h0,h1,ite_false,nativeSource,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

noncomputable def first := TapeEmbedding.machine 234 PCPPRequestCircuitIndex.machine
noncomputable def second := RecoveryFocus.machine slots PCPPRequestCircuitTag.machine
noncomputable def machine := Composition.machine first second
def input {n : ℕ} (c : BooleanCircuit n) : Fin tapes → List Bool :=
  Fin.addCases (m:=PCPPRequestCircuitIndex.tapes) (n:=234) (PCPPRequestCircuitIndex.input c) (fun _ => [])
def budget {n : ℕ} (c : BooleanCircuit n) := PCPPRequestCircuitIndex.budget c+1+
  PCPPRequestCircuitTag.budget (CanonicalBinary.encodeBalancedList (c.nodes.map ExecutableInterfaces.encodeBooleanNode))
    (CanonicalBinary.encodeNat c.output.val)

end NearCubicWires.RepairOrdinary.PCPPRequestCircuitCode
