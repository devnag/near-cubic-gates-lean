import Proof.PCP.PCPPNativeNodeClassify
import Proof.PCP.PCPPNativeTemplateRawWord
import Proof.PCP.PCPPNativeProjectionTyped
import Proof.PCP.PCPPNativeNotNode
import Proof.PCP.PCPPNativeBinaryNode
import Proof.PCP.PCPPNativeInputNode

/-! One fixed finite controller for the native oracle-node substitution.
Every choice is made from an executed classifier. All five native tags and
all three projection kinds select actual parsers, conversions and emitters. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readSlots (i : Fin 31) : Fin 119 :=
  if i=0 then 0 else if i=10 then 6 else if i=20 then 7 else if i=30 then 8
  else ⟨i.val+20,by omega⟩
def lookupSlots (i : Fin 28) : Fin 119 :=
  if i=0 then 1 else if i=2 then 7 else if i=22 then 14 else if i=26 then 15
  else ⟨i.val+60,by omega⟩
def argSlots (right : Bool) : Fin 5 → Fin 119 :=
  if right then ![8,10,54,55,56] else ![7,9,51,52,53]
def valueSlots : Fin 5 → Fin 119 := ![15,11,57,58,59]
def fieldSlots (projected : Bool) (i : Fin 24) : Fin 119 :=
  if i=0 then (if projected then 13 else 2)
  else if i=1 then (if projected then 11 else 9)
  else if h20 : i=20 then 5 else if h21 : i=21 then 118 else if h22 : i=22 then 4 else if h23 : i=23 then 12
  else ⟨i.val+98,by
    have hv20 : i.val≠20 := fun h => h20 (Fin.ext h)
    have hv21 : i.val≠21 := fun h => h21 (Fin.ext h)
    have hv22 : i.val≠22 := fun h => h22 (Fin.ext h)
    have hv23 : i.val≠23 := fun h => h23 (Fin.ext h)
    omega⟩
def binarySlots : Fin 25 → Fin 119 :=
  Fin.addCases (motive := fun _ : Fin 25 => Fin 119) (fieldSlots false) (fun _ : Fin 1 => 10)
def inputSlots : Fin 25 → Fin 119 :=
  Fin.addCases (motive := fun _ : Fin 25 => Fin 119) (fieldSlots true) (fun _ : Fin 1 => 3)

theorem read_injective : Function.Injective readSlots := by decide
theorem lookup_injective : Function.Injective lookupSlots := by decide
theorem arg_injective (right : Bool) : Function.Injective (argSlots right) := by cases right <;> decide
theorem value_injective : Function.Injective valueSlots := by decide
theorem field_injective (projected : Bool) : Function.Injective (fieldSlots projected) := by cases projected <;> decide
theorem binary_injective : Function.Injective binarySlots := by decide
theorem input_injective : Function.Injective inputSlots := by decide

def constBits (first second : Bool) : List Bool :=
  PCPPRequestNodeSchema.native (.const first : BooleanNode 0)++
    PCPPRequestNodeSchema.native (.const second : BooleanNode 0)
noncomputable def readProgram := RecoveryFocus.machine readSlots PCPPNativeNodeClassify.machine
noncomputable def tagProgram (slot : Fin 119) := RecoveryFocus.machine (fun _ : Fin 1 => slot) PCPPNativeTag.machine
noncomputable def literalProgram (bits : List Bool) :=
  RecoveryFocus.machine (fun _ : Fin 1 => (5 : Fin 119)) (HierarchyFixedWord.raw bits)
noncomputable def argProgram (right : Bool) := RecoveryFocus.machine (argSlots right) PCPPNativeTemplateRaw.machine
noncomputable def valueProgram := RecoveryFocus.machine valueSlots PCPPNativeTemplateRaw.machine
noncomputable def lookupProgram := RecoveryFocus.machine lookupSlots PCPPNativeProjectionLookup.machine
noncomputable def notProgram := RecoveryFocus.machine (fieldSlots false) PCPPNativeNotNode.machine
noncomputable def binaryProgram (isOr : Bool) := RecoveryFocus.machine binarySlots (PCPPNativeBinary.machine isOr)
noncomputable def inputProgram (negative : Bool) := RecoveryFocus.machine inputSlots (PCPPNativeInput.machine negative)

private abbrev stateCount {t s : ℕ} (_ : Machine t s) := s
noncomputable def sizes : Fin 21 → ℕ :=
  ![stateCount readProgram,10,stateCount (literalProgram (constBits false false)),
    stateCount (literalProgram (constBits false true)),stateCount (argProgram false),stateCount notProgram,
    stateCount (argProgram false),stateCount (argProgram true),stateCount (binaryProgram false),
    stateCount (argProgram false),stateCount (argProgram true),stateCount (binaryProgram true),
    stateCount lookupProgram,10,stateCount valueProgram,stateCount (inputProgram false),
    stateCount valueProgram,stateCount (inputProgram true),10,
    stateCount (literalProgram (constBits false false)),stateCount (literalProgram (constBits true true))]
noncomputable def programs : (j : Fin 21) → Machine 119 (sizes j)
  | ⟨0,_⟩ => readProgram
  | ⟨1,_⟩ => tagProgram 7
  | ⟨2,_⟩ => literalProgram (constBits false false)
  | ⟨3,_⟩ => literalProgram (constBits false true)
  | ⟨4,_⟩ => argProgram false
  | ⟨5,_⟩ => notProgram
  | ⟨6,_⟩ => argProgram false
  | ⟨7,_⟩ => argProgram true
  | ⟨8,_⟩ => binaryProgram false
  | ⟨9,_⟩ => argProgram false
  | ⟨10,_⟩ => argProgram true
  | ⟨11,_⟩ => binaryProgram true
  | ⟨12,_⟩ => lookupProgram
  | ⟨13,_⟩ => tagProgram 14
  | ⟨14,_⟩ => valueProgram
  | ⟨15,_⟩ => inputProgram false
  | ⟨16,_⟩ => valueProgram
  | ⟨17,_⟩ => inputProgram true
  | ⟨18,_⟩ => tagProgram 15
  | ⟨19,_⟩ => literalProgram (constBits false false)
  | ⟨20,_⟩ => literalProgram (constBits true true)
  | ⟨n+21,h⟩ => False.elim (by omega)
def next (j : Fin 21) (q : Fin (sizes j)) (_ : Fin 119 → Bool) : Option (Fin 21) :=
  match j.val with
  | 0 => if q.val=PCPPNativeNodeClassify.readerStates+5 then some 1
      else if q.val=PCPPNativeNodeClassify.readerStates+6 then some 12
      else if q.val=PCPPNativeNodeClassify.readerStates+7 then some 4
      else if q.val=PCPPNativeNodeClassify.readerStates+8 then some 6
      else if q.val=PCPPNativeNodeClassify.readerStates+9 then some 9 else none
  | 1 => if q.val=5 then some 2 else if q.val=6 then some 3 else none
  | 4 => some 5
  | 6 => some 7
  | 7 => some 8
  | 9 => some 10
  | 10 => some 11
  | 12 => some 13
  | 13 => if q.val=5 then some 14 else if q.val=6 then some 16 else if q.val=7 then some 18 else none
  | 14 => some 15
  | 16 => some 17
  | 18 => if q.val=5 then some 19 else if q.val=6 then some 20 else none
  | _ => none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem parsed_next (tag : Fin 5) (q : Fin (sizes 0)) (bits : Fin 119 → Bool)
    (hq : q.val=PCPPNativeNodeClassify.readerStates+(tag.val+5)) :
    next 0 q bits=some (![1,12,4,6,9] tag) := by
  fin_cases tag <;> simp [next,hq,PCPPNativeNodeClassify.readerStates,PCPPQueryNatural.states]

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
