import Proof.PCP.PCPSerializerCapacityFocus
import Proof.MachineModel.UWalkUnary

/-! Physical serializer entry: move the existing count sentinel to its
origin, initialize the continuation bottom, copy the count into the raw
current-count register, then restore the original count cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerCountEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (boot : Bool) : Action 128 2 :=
  ⟨1,fun i => if boot ∧ i=81 then some false else none,
    fun i => if i=2 then if boot then .left else .right else if boot ∧ i=81 then .right else .stay⟩
def command (boot : Bool) : Machine 128 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q=0 then some (action boot) else none

def bootHeads (heads : Fin 128 → ℕ) : Fin 128 → ℕ :=
  fun i => if i=2 then 0 else if i=81 then 1 else heads i
def bootTapes (tapes : Fin 128 → List Bool) : Fin 128 → List Bool :=
  fun i => if i=81 then [false] else tapes i
def finalHeads (heads : Fin 128 → ℕ) : Fin 128 → ℕ := fun i => if i=81 then 1 else heads i

theorem command_run (boot : Bool) (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool) :
    ∃ r,runFrom (command boot) 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=applyAction (⟨0,heads,tapes⟩ : Configuration 128 2) (action boot) ∧ r.steps=1 :=
  (Timed.single (by rfl : (command boot).halted (0 : Fin 2)=false)
    (by rfl : step (command boot) ⟨0,heads,tapes⟩=some (applyAction ⟨0,heads,tapes⟩ (action boot)))).run (by rfl)

theorem boot_config (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (h2 : heads 2=1) (h81 : heads 81=0) (t81 : tapes 81=[]) :
    applyAction (⟨0,heads,tapes⟩ : Configuration 128 2) (action true)=
      ⟨1,bootHeads heads,bootTapes tapes⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i=2
    · subst i; simp [applyAction,action,bootHeads,HeadMove.apply,h2]
    by_cases hj : i=81
    · subst i; simp [applyAction,action,bootHeads,HeadMove.apply,h81]
    · simp [applyAction,action,bootHeads,HeadMove.apply,hi,hj]
  · funext i
    by_cases hi : i=81
    · subst i; simp [applyAction,action,bootTapes,h81,t81,writeTapeBit]
    · simp [applyAction,action,bootTapes,hi]

theorem finish_config (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool) (h2 : heads 2=1) :
    applyAction (⟨0,bootHeads heads,tapes⟩ : Configuration 128 2) (action false)=
      ⟨1,finalHeads heads,tapes⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i=2
    · subst i; simp [applyAction,action,bootHeads,finalHeads,HeadMove.apply,h2]
    by_cases hj : i=81
    · subst i; simp [applyAction,action,bootHeads,finalHeads,HeadMove.apply]
    · simp [applyAction,action,bootHeads,finalHeads,HeadMove.apply,hi,hj]
  · funext i; simp [applyAction,action]

def slots : Fin 3 → Fin 128 := ![2,79,88]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def copy := RecoveryFocus.machine slots (UWalkUnary.machine false false)
noncomputable def machine := Composition.machine (Composition.machine (command true) copy) (command false)

end NearCubicWires.RepairOrdinary.PCPSerializerCountEntry
