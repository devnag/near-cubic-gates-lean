import Proof.PCP.PCPPNativeQueryRowLoad

/-! One fixed outer query iteration: load the next physical projection
row, execute the reusable original-query emitter, and retain its two outer
source/count cursors. The Q driver will belong to the enclosing Repeat. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryIteration
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loadSlots : Fin 4 → Fin 173 := ![171,1,172,6]
def querySlots (i : Fin 171) : Fin 173 := i.castAdd 2
theorem load_injective : Function.Injective loadSlots := by decide
theorem query_injective : Function.Injective querySlots := by
  intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 173 => k.val) h
noncomputable def load := RecoveryFocus.machine loadSlots PCPPNativeQueryRowLoad.machine
noncomputable def query := RecoveryFocus.machine querySlots PCPPNativeQueryReusable.machine
noncomputable def machine := Composition.machine load query
def heads (cursor : ℕ) (out : List Bool) : Fin 173 → ℕ :=
  Fin.addCases (m := 171) (n := 2) (PCPPNativeQueryReusable.heads out) ![cursor,1]
def data (bits cache stream : List Bool) (base C F G : ℕ) (out : List Bool) (width : ℕ) : Fin 173 → List Bool :=
  Fin.addCases (m := 171) (n := 2) (PCPPNativeQueryReusable.data bits cache base C F G out)
    ![stream,UnaryTemplate.tape width]
noncomputable def entry (bits stream : List Bool) (cursor base C F G : ℕ) (out : List Bool) (width : ℕ) :=
  (⟨machine.start,heads cursor out,data bits [] stream base C F G out width⟩ : Configuration 173 _)

theorem load_input (bits stream : List Bool) (cursor base C F G : ℕ) (out : List Bool) (width : ℕ) (j : Fin 4) :
    heads cursor out (loadSlots j)=PCPPNativeQueryRowLoad.heads cursor j ∧
      data bits [] stream base C F G out width (loadSlots j)=PCPPNativeQueryRowLoad.input stream width G j := by
  fin_cases j
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,PCPPNativeNodeReusable.pad_empty G⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
theorem load_low_away (i : Fin 171) (h1 : i≠1) (h6 : i≠6) (j : Fin 4) : loadSlots j≠querySlots i := by
  fin_cases j
  · apply Fin.ne_of_val_ne; change 171≠i.val; omega
  · intro h; apply h1; apply Fin.ext; exact (congrArg (fun k : Fin 173 => k.val) h).symm
  · apply Fin.ne_of_val_ne; change 172≠i.val; omega
  · intro h; apply h6; apply Fin.ext; exact (congrArg (fun k : Fin 173 => k.val) h).symm

end NearCubicWires.RepairOrdinary.PCPPNativeQueryIteration
