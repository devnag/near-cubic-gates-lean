import Proof.Circuits.DecompositionPrepare
import Proof.Circuits.DecompositionNativeEntry
import Proof.Circuits.DecompositionSchema

/-! The original-input prefix shares its five actual native fields with
the fixed nesting program; every other nesting tape is fresh. -/
namespace NearCubicWires.RepairOrdinary.DecompositionGlobal
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := DecompositionColdPrepare.tapes D+443
def rawSource (D : ℕ) := DecompositionColdPrepare.headerSlot D 1
def fieldCount (D : ℕ) := DecompositionColdPrepare.headerSlot D (DecompositionInputDrivers.slots 12)
def childArity (D : ℕ) := DecompositionColdPrepare.headerSlot D (DecompositionInputDrivers.slots 4)
def childCount (D : ℕ) := DecompositionColdPrepare.headerSlot D (DecompositionInputDrivers.slots 6)
def slots (D : ℕ) (j : Fin 443) : Fin (tapes D) :=
  if j.val=0 then (rawSource D).castAdd 443
  else if j.val=177 then (DecompositionColdPrepare.capacitySlot D).castAdd 443
  else if j.val=179 then (fieldCount D).castAdd 443
  else if j.val=181 then (childArity D).castAdd 443
  else if j.val=182 then (childCount D).castAdd 443
  else j.natAdd (DecompositionColdPrepare.tapes D)
def outputSlot (D : ℕ) := slots D 393

theorem raw_val (D : ℕ) : (rawSource D).val=PCPSerializerCapacity.tapes D := by
  simp [rawSource,DecompositionColdPrepare.headerSlot,DecompositionColdPrepare.extra]
theorem field_val (D : ℕ) : (fieldCount D).val=PCPSerializerCapacity.tapes D+32 := rfl
theorem arity_val (D : ℕ) : (childArity D).val=PCPSerializerCapacity.tapes D+24 := rfl
theorem count_val (D : ℕ) : (childCount D).val=PCPSerializerCapacity.tapes D+26 := rfl

theorem slots_injective (D : ℕ) : Function.Injective (slots D) := by
  intro i j he
  have hv := congrArg Fin.val he
  have hcap : (DecompositionColdPrepare.capacitySlot D).val<PCPSerializerCapacity.tapes D :=
    (PCPSerializerCapacity.capacitySlot D).isLt
  have hT : DecompositionColdPrepare.tapes D=PCPSerializerCapacity.tapes D+34 := rfl
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv
  all_goals try simp only [Fin.val_castAdd,Fin.val_natAdd,raw_val,field_val,arity_val,count_val] at hv
  all_goals omega

noncomputable def first (D C : ℕ) := TapeEmbedding.machine 443 (DecompositionColdPrepare.machine D C)
noncomputable def second (D : ℕ) := RecoveryFocus.machine (slots D) DecompositionNesting.machine
noncomputable def machine (D C : ℕ) := Composition.machine (first D C) (second D)
def input (D : ℕ) (payload : List Bool) : Fin (tapes D) → List Bool :=
  Fin.addCases (DecompositionColdPrepare.input D payload) (fun _ : Fin 443 => [])
def budget (D C E a : ℕ) (groups : List (List ℤ)) :=
  DecompositionColdPrepare.budget D C a groups.length (DecompositionAtomLoop.stream groups.flatten)+
    1+DecompositionNesting.budget E groups

end NearCubicWires.RepairOrdinary.DecompositionGlobal
