import Proof.PCP.PCPPNativeClausePadded
import Proof.PCP.PCPUnaryCopy
import Proof.Amplification.RecoveryScratchErase

/-! One reusable literal bank: retain a raw reference outside the parser,
then erase all fifteen work tapes using the actual capacity driver. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReusable
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots (j : Fin 19) : Fin 23 := j.castAdd 4
def copySlots : Fin 3→Fin 23 := ![11,19,20]
def workSlots : Fin 15→Fin 19 := ![0,1,2,3,7,8,9,10,11,12,14,15,16,17,18]
def eraseSlots : Fin 17→Fin 23 := ![0,1,2,3,7,8,9,10,11,12,14,15,16,17,18,21,22]
theorem field_injective : Function.Injective fieldSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 23=>k.val) h)
theorem copy_injective : Function.Injective copySlots := by decide
theorem erase_injective : Function.Injective eraseSlots := by decide
theorem work_classify (j : Fin 15) : PCPPNativeClauseField.work (workSlots j) := by
  fin_cases j <;> decide
theorem erase_work (j : Fin 15) : eraseSlots (j.castAdd 2)=fieldSlots (workSlots j) := by
  fin_cases j <;> rfl

noncomputable def first := RecoveryFocus.machine fieldSlots PCPPNativeClauseField.machine
noncomputable def copyMachine := RecoveryFocus.machine copySlots PCPUnaryCopy.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 15)
noncomputable def machine := Composition.machine (Composition.machine first copyMachine) last
def heads (pos : ℕ) (i : Fin 23) := if i=13 then pos else 0
def data (source : List Bool) (stride p n C : ℕ) (result : List Bool) (i : Fin 23) :=
  if i=4 then UnaryTemplate.tape stride else if i=5 then List.replicate p true
  else if i=6 then List.replicate n true else if i=13 then source
  else if i=19 then result else if i=20 ∨ i=22 then List.replicate (C+1) false
  else if i=21 then List.replicate C true else List.replicate C false
def entry {s : ℕ} (p : Machine 23 s) (pos : ℕ) (data : Fin 23→List Bool) : Configuration 23 s :=
  ⟨p.start,heads pos,data⟩

theorem field_input (source : List Bool) (stride p n C pos : ℕ) (j : Fin 19) :
    heads pos (fieldSlots j)=PCPPNativeClauseField.heads pos j ∧
      data source stride p n C [] (fieldSlots j)=
        PCPPNativeClauseField.paddedInput source stride p n C j := by
  fin_cases j <;> simp [heads,data,fieldSlots,PCPPNativeClauseField.heads,
    PCPPNativeClauseField.paddedInput,PCPPNativeClauseField.caps,
    PCPPNativeClauseField.work,PCPPNativeClauseField.input,ZeroPadding.pad]

theorem erase_away (i : Fin 23)
    (hi : i=4 ∨ i=5 ∨ i=6 ∨ i=13 ∨ i=19 ∨ i=20) :
    ∀ j,eraseSlots j≠i := by
  intro j
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> fin_cases j <;> decide

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReusable
