import Proof.PCP.PCPPNativeClauseTriple
import Proof.PCP.PCPPNativeClauseBlock

/-! The actual clause reader and three-node printer share retained references.
Both live cursors and the two enclosing clause counters have fixed ports. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseBody
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tripleSlots (i : Fin 25) : Fin 51 := i.castAdd 26
def blockSlots : Fin 29→Fin 51 :=
  ![25,19,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,23,24,26,27,28]
theorem triple_injective : Function.Injective tripleSlots := by
  intro i j h; exact Fin.ext (congrArg (fun a : Fin 51=>a.val) h)
theorem block_injective : Function.Injective blockSlots := by decide
def heads (pos : ℕ) (out : List Bool) (i : Fin 51) : ℕ :=
  if i=13 then pos else if i=47 then out.length else 0
def data (source : List Bool) (stride p n C base accumulator : ℕ) (refs : Fin 3→ℕ)
    (out : List Bool) (i : Fin 51) : List Bool :=
  if hi : i.val<25 then PCPPNativeClauseTriple.data source stride p n C
    (fun j=>List.replicate (refs j) true) ⟨i.val,hi⟩
  else if i=25 then [] else if i=26 then List.replicate base true
  else if i=27 then List.replicate accumulator true else if i=28 then [true]
  else if i=47 then out else if i=49 then List.replicate C true
  else if i=50 then List.replicate (C+1) false else List.replicate C false
def entry {s : ℕ} (m : Machine 51 s) (source : List Bool) (pos stride p n C base accumulator : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) : Configuration 51 s :=
  ⟨m.start,heads pos out,data source stride p n C base accumulator refs out⟩
noncomputable def first := RecoveryFocus.machine tripleSlots PCPPNativeClauseTriple.machine
noncomputable def last := RecoveryFocus.machine blockSlots PCPPNativeClauseBank.machine
noncomputable def machine := Composition.machine first last

theorem triple_input (source : List Bool) (pos stride p n C base accumulator : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) (j : Fin 25) :
    heads pos out (tripleSlots j)=PCPPNativeClauseTriple.heads pos j ∧
      data source stride p n C base accumulator refs out (tripleSlots j)=
        PCPPNativeClauseTriple.data source stride p n C (fun k=>List.replicate (refs k) true) j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem block_input (source : List Bool) (pos stride p n C base accumulator : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) (j : Fin 29) :
    heads pos out (blockSlots j)=PCPPNativeClauseBank.heads out j ∧
      data source stride p n C base accumulator refs out (blockSlots j)=
        PCPPNativeClauseBank.data (PCPPNativeClauseBank.values base accumulator refs) C out j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

end NearCubicWires.RepairOrdinary.PCPPNativeClauseBody
