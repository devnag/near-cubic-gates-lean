import Proof.PCP.PCPPRequestNodeGlobal

/-! The balanced node-list call uses the actual rewound node stream and its
retained count. All other serializer tapes are fresh, with no stream copy. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestCircuitNodes
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prefixTapes := PCPPRequestNodeGlobal.tapes 12+1
def tapes := prefixTapes+128
def nodeStream : Fin prefixTapes := (PCPPRequestNodeGlobal.outputSlot 12).castAdd 1
def nodeCount : Fin prefixTapes := (PCPPRequestNodeGlobal.slots 12 646).castAdd 1
def slots (j : Fin 128) : Fin tapes :=
  if j.val=0 then nodeStream.castAdd 128
  else if j.val=2 then nodeCount.castAdd 128
  else j.natAdd prefixTapes
def outputSlot := slots 78
def framedSlot := slots 77

theorem stream_ne_count : nodeStream≠nodeCount := by
  intro he
  have hv : PCPPRequestNodeGlobal.slots 12 643=PCPPRequestNodeGlobal.slots 12 646 :=
    Fin.ext (congrArg (fun j : Fin prefixTapes => j.val) he)
  have h := congrArg Fin.val (PCPPRequestNodeGlobal.slots_injective 12 hv)
  contradiction

theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv := congrArg Fin.val he
  have hs := nodeStream.isLt
  have hc := nodeCount.isLt
  have hne : nodeStream.val≠nodeCount.val := fun h => stream_ne_count (Fin.ext h)
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega

def fields {n : ℕ} (nodes : List (BooleanNode n)) :=
  nodes.map (fun node => (ExecutableInterfaces.encodeBooleanNode node).bits)
noncomputable def first := TapeEmbedding.machine 128 PCPPRequestNodeGlobal.readyMachine
noncomputable def second := RecoveryFocus.machine slots PCPTraversal.machine
noncomputable def machine := Composition.machine first second
def input {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) : Fin tapes → List Bool :=
  Fin.addCases (m:=prefixTapes) (n:=128) (PCPPRequestNodeGlobal.readyInput nodes suffix) (fun _ => [])
def budget {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :=
  (2*PCPPRequestNodeGlobal.coldBudget nodes suffix+2)+1+
    PCPTraversal.budget (PCPSerializerMass.mass (fields nodes))

theorem literal_code {n : ℕ} (nodes : List (BooleanNode n)) :
    PCPTraversal.code (fields nodes)=
      CanonicalBinary.encodeBalancedList (nodes.map ExecutableInterfaces.encodeBooleanNode) := by
  simp only [PCPTraversal.code,PCPSerializerMass.values,fields,List.map_map,
    Function.comp_def,CanonicalPositiveOutput.nat_bits_value]

end NearCubicWires.RepairOrdinary.PCPPRequestCircuitNodes
