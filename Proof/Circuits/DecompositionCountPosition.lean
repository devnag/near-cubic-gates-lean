import Proof.Circuits.DecompositionInputCounts

/-! Fixed one-step head positioning for the actual native header drivers and
the later integer/child loop drivers. Tape contents are retained exactly. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCountPosition
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def move {t : ℕ} (directions : Fin t → HeadMove) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,directions⟩ else none

theorem move_run {t : ℕ} (directions : Fin t → HeadMove)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) :
    ∃ r,runFrom (move directions) 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=(⟨1,fun i => (directions i).apply (heads i),tapes⟩ : Configuration t 2) ∧
      r.steps=1 := by
  have h : step (move directions) ⟨0,heads,tapes⟩=
      some (⟨1,fun i => (directions i).apply (heads i),tapes⟩ : Configuration t 2) := by
    rfl
  exact (Timed.single (by rfl) h).run (by rfl)

def nativeHeads (i : Fin 14) : ℕ := if i=0 ∨ i=1 then 1 else 0
def loopHeads (i : Fin 14) : ℕ := if i=4 ∨ i=6 ∨ i=12 then 1 else 0
def retreat (i : Fin 14) : HeadMove := if i=0 ∨ i=1 then .left else .stay
def advance (i : Fin 14) : HeadMove := if i=4 ∨ i=6 ∨ i=12 then .right else .stay

theorem retreat_run (tapes : Fin 14 → List Bool) :
    ∃ r,runFrom (move retreat) 1 ⟨0,nativeHeads,tapes⟩=some r ∧
      r.final=(⟨1,fun _ => 0,tapes⟩ : Configuration 14 2) ∧ r.steps=1 := by
  obtain ⟨r,hr,hf,hs⟩ := move_run retreat nativeHeads tapes
  refine ⟨r,hr,?_,hs⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem advance_run (tapes : Fin 14 → List Bool) :
    ∃ r,run (move advance) 1 tapes=some r ∧
      r.final=(⟨1,loopHeads,tapes⟩ : Configuration 14 2) ∧ r.steps=1 := by
  obtain ⟨r,hr,hf,hs⟩ := move_run advance (fun _ => 0) tapes
  refine ⟨r,hr,?_,hs⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

end NearCubicWires.RepairOrdinary.DecompositionCountPosition
