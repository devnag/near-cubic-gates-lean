import Proof.PCP.PCPPRequestCircuitReady
import Proof.PCP.PCPPRequestWordFramed

/-! The final PCPP request assembler shares its two real producer fields. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestInput
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes := PCPPRequestCircuitReady.tapes+9
def slots (j : Fin 9) : Fin tapes :=
  if j.val=0 then PCPPRequestCircuitReady.nativeSource.castAdd 9
  else if j.val=1 then PCPPRequestCircuitReady.framedSlot.castAdd 9
  else j.natAdd PCPPRequestCircuitReady.tapes
def outputSlot := slots 7
theorem fields_distinct : PCPPRequestCircuitReady.nativeSource≠PCPPRequestCircuitReady.framedSlot := by
  intro he
  have hv := congrArg Fin.val he
  exact PCPPRequestCircuitCode.slots_ne_native 222 (Fin.ext hv.symm)
theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv := congrArg Fin.val he
  have ha : PCPPRequestCircuitReady.nativeSource.val < PCPPRequestCircuitReady.tapes :=
    PCPPRequestCircuitReady.nativeSource.isLt
  have hb : PCPPRequestCircuitReady.framedSlot.val < PCPPRequestCircuitReady.tapes :=
    PCPPRequestCircuitReady.framedSlot.isLt
  have hn : PCPPRequestCircuitReady.nativeSource.val≠PCPPRequestCircuitReady.framedSlot.val :=
    fun h => fields_distinct (Fin.ext h)
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega
noncomputable def first := TapeEmbedding.machine 9 PCPPRequestCircuitReady.machine
noncomputable def second := RecoveryFocus.machine slots PCPPRequestWordFramed.machine
noncomputable def machine := Composition.machine first second
def input {n : ℕ} (c : BooleanCircuit n) : Fin tapes → List Bool :=
  Fin.addCases (m:=PCPPRequestCircuitReady.tapes) (n:=9) (PCPPRequestCircuitReady.input c) (fun _ => [])
def budget {n : ℕ} (c : BooleanCircuit n) := PCPPRequestCircuitReady.budget c+1+
  PCPPRequestWordFramed.budget n (ExecutableInterfaces.encodeBooleanCircuit c).bits

end NearCubicWires.RepairOrdinary.PCPPRequestInput
