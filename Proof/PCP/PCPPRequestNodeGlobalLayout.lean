import Proof.PCP.PCPPRequestNodeListEntry
import Proof.Circuits.DecompositionPrepare

/-! Reuse the existing cold native header and measured capacity producer.
Only source, capacity and the already-correct count overlap the node bank. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeGlobal
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := DecompositionColdPrepare.tapes D+647
def rawSource (D : ℕ) := DecompositionColdPrepare.headerSlot D 1
def nodeCount (D : ℕ) := DecompositionColdPrepare.headerSlot D (DecompositionInputDrivers.slots 6)
def slots (D : ℕ) (j : Fin 647) : Fin (tapes D) :=
  if j.val=0 then (rawSource D).castAdd 647
  else if j.val=644 then (DecompositionColdPrepare.capacitySlot D).castAdd 647
  else if j.val=646 then (nodeCount D).castAdd 647
  else j.natAdd (DecompositionColdPrepare.tapes D)
def outputSlot (D : ℕ) := slots D 643

theorem raw_val (D : ℕ) : (rawSource D).val=PCPSerializerCapacity.tapes D := by
  simp [rawSource,DecompositionColdPrepare.headerSlot,DecompositionColdPrepare.extra]
theorem count_val (D : ℕ) : (nodeCount D).val=PCPSerializerCapacity.tapes D+26 := rfl

theorem slots_injective (D : ℕ) : Function.Injective (slots D) := by
  intro i j he
  have hv := congrArg Fin.val he
  have hcap : (DecompositionColdPrepare.capacitySlot D).val < PCPSerializerCapacity.tapes D :=
    (PCPSerializerCapacity.capacitySlot D).isLt
  have hT : DecompositionColdPrepare.tapes D=PCPSerializerCapacity.tapes D+34 := rfl
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv
  all_goals try simp only [Fin.val_castAdd,Fin.val_natAdd,raw_val,count_val] at hv
  all_goals omega

noncomputable def first (D C : ℕ) := TapeEmbedding.machine 647 (DecompositionColdPrepare.machine D C)
noncomputable def second (D : ℕ) := RecoveryFocus.machine (slots D) PCPPRequestNodeList.machine
noncomputable def machine (D C : ℕ) := Composition.machine (first D C) (second D)
def input (D : ℕ) (payload : List Bool) : Fin (tapes D) → List Bool :=
  Fin.addCases (DecompositionColdPrepare.input D payload) (fun _ : Fin 647 => [])
def budget {n : ℕ} (D C E a : ℕ) (nodes : List (BooleanNode n)) (suffix : List Bool) :=
  DecompositionColdPrepare.budget D C a nodes.length (PCPPRequestNodeLoop.stream nodes++suffix)+
    1+PCPPRequestNodeList.budget E nodes.length

end NearCubicWires.RepairOrdinary.PCPPRequestNodeGlobal
