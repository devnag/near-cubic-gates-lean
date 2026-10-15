import Proof.Amplification.RecoveryTapeSupport
import Proof.MachineModel.Runs

/-! A scratch tape's support bound depends on its own cursor, not on the
unbounded append cursor of another tape. This is the bound consumed by the
hardwiring scratch erase/reload wrapper. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.LocalSupport
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch

theorem step_bound {t s : Nat} (p : Machine t s) (c d : Configuration t s)
    (hs : step p c=some d) (i : Fin t) :
    (d.tapes i).length ≤ max (c.tapes i).length (c.heads i+1) := by
  unfold step at hs
  obtain ⟨action,_,he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  simp only [applyAction]
  cases hw : action.write i
  · exact Nat.le_max_left _ _
  · simp only [RecoveryTapeSupport.write_length,le_refl]

theorem run_bound {t s : Nat} (p : Machine t s) (fuel : Nat)
    (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c=some r) (i : Fin t) :
    (r.final.tapes i).length ≤ max (c.tapes i).length (c.heads i+r.steps+1) := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact Nat.le_max_left _ _
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact Nat.le_max_left _ _
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs,ht] at hr
        | some tail =>
          simp only [hs,ht,Option.some.injEq] at hr
          subst r
          have length := step_bound p c d hs i
          have head := SelectiveReset.step_head p c d i hs
          have bound := ih d tail ht
          change (tail.final.tapes i).length ≤
            max (c.tapes i).length (c.heads i+(tail.steps+1)+1)
          omega

theorem step_fits {t s : Nat} {p : Machine t s} {n : Nat}
    {H J : Fin t → Nat} {A B : Fin t → List Bool}
    (run : Step p n H A J B) (i : Fin t) (R : Nat)
    (ha : (A i).length≤R) (hh : H i+n+1≤R) : (B i).length≤R := by
  obtain ⟨r,hr,_rh,rt,rs⟩ := run
  have h := run_bound p n ⟨p.start,H,A⟩ r hr i
  rw [rt] at h
  change (B i).length ≤ max (A i).length (H i+r.steps+1) at h
  omega

end NearCubicWires.P1Closure.LocalSupport
