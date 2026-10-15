import Proof.Hierarchy.CompetitorSelectedRequestCountLayout

namespace NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
open LocalBitMultitape CompetitorSelectedCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

set_option pp.fullNames true in

theorem heads_projection {t u s : ℕ} (pickSlots : Fin t → Fin u)
    (ah : Fin u → ℕ) (atapes : Fin u → List Bool) (child : Configuration t s) :
    (RecoveryFocus.config pickSlots ah atapes child).heads=
      fun i => match RecoveryFocus.pick pickSlots i with | some j => child.heads j | none => ah i := rfl

theorem focus_heads {s : ℕ} (Q N : ℕ) (ah : Fin 91 → ℕ)
    (atapes : Fin 91 → List Bool) (child : Configuration 20 s)
    (ph : ∀ i,ah i=0) (ch : child.heads=finalHeads Q N) :
    (RecoveryFocus.config slots ah atapes child).heads=outputHeads Q N := by
  rw [heads_projection]
  funext i
  unfold outputHeads
  cases hp : RecoveryFocus.pick CompetitorSelectedRequestCount.slots i with
  | none => exact ph i
  | some j => exact congrFun ch j

end NearCubicWires.RepairOrdinary.CompetitorSelectedRequestCount
