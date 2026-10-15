import Proof.PCP.PCPPNativeClauseCounter

/-! The repeating original-clause bank keeps the literal references and the
counter temporary zero-padded. All four are erased after each actual clause. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReuse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (C : ℕ) (i : Fin 51) : ℕ := if i=19 ∨ i=23 ∨ i=24 ∨ i=25 then C else 0
def data (source : List Bool) (stride p n C base accumulator temporary : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) (i : Fin 51) : List Bool :=
  ZeroPadding.pad (padding C i)
    (if i=25 then List.replicate temporary true else
      PCPPNativeClauseBody.data source stride p n C base accumulator refs out i)
def entry {s : ℕ} (m : Machine 51 s) (source : List Bool) (pos stride p n C base accumulator temporary : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) : Configuration 51 s :=
  ⟨m.start,PCPPNativeClauseBody.heads pos out,data source stride p n C base accumulator temporary refs out⟩
def counterSlots : Fin 4→Fin 51 := ![26,27,25,50]
def counterPadding (C : ℕ) (j : Fin 4) := if j=2 then C else 0
def eraseSlots : Fin 6→Fin 51 := ![19,23,24,25,49,50]
theorem counter_injective : Function.Injective counterSlots := by decide
theorem erase_injective : Function.Injective eraseSlots := by decide
noncomputable def counter := RecoveryFocus.machine counterSlots PCPPNativeClauseCounter.machine
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 4)
noncomputable def beforeErase := Composition.machine PCPPNativeClauseBody.machine counter
noncomputable def machine := Composition.machine beforeErase erase

theorem zero_data (source : List Bool) (stride p n C base accumulator : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) :
    data source stride p n C base accumulator 0 refs out=
      fun i=>ZeroPadding.pad (padding C i) (PCPPNativeClauseBody.data source stride p n C base accumulator refs out i) := by
  funext i
  by_cases h : i=25
  · subst i; rfl
  · simp only [data,if_neg h]

theorem counter_input (source : List Bool) (pos stride p n C base accumulator temporary : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) (j : Fin 4) :
    PCPPNativeClauseBody.heads pos out (counterSlots j)=0 ∧
      data source stride p n C base accumulator temporary refs out (counterSlots j)=
        ZeroPadding.pad (counterPadding C j) (PCPPNativeClauseCounter.data base accumulator temporary (C+1) j) := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

theorem counter_outside (source : List Bool) (stride p n C base accumulator temporary b a t : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) (i : Fin 51) (hi : ∀ j,counterSlots j≠i) :
    data source stride p n C base accumulator temporary refs out i=data source stride p n C b a t refs out i := by
  have h25:=hi 2; have h26:=hi 0; have h27:=hi 1
  fin_cases i
  all_goals first | rfl | exact False.elim (h25 rfl) | exact False.elim (h26 rfl) | exact False.elim (h27 rfl)

theorem erase_outside (source : List Bool) (stride p n C base accumulator temporary : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) (i : Fin 51) (hi : ∀ j,eraseSlots j≠i) :
    data source stride p n C base accumulator temporary refs out i=
      data source stride p n C base accumulator 0 (fun _=>0) out i := by
  have h19:=hi 0; have h23:=hi 1; have h24:=hi 2; have h25:=hi 3
  fin_cases i
  all_goals first | rfl | exact False.elim (h19 rfl) | exact False.elim (h23 rfl) | exact False.elim (h24 rfl) | exact False.elim (h25 rfl)

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReuse
