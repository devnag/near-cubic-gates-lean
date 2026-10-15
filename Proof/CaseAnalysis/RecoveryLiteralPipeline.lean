import Proof.CaseAnalysis.RecoveryLiteralPrepared

/-! The literal's fixed three-stage composition, with definitions and the
receipt join checked before instantiating its actual controller sizes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralPipeline
open LocalBitMultitape Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {a b c : ℕ} (first : Machine 71 a) (middle : Machine 71 b) (last : Machine 71 c)
def prepare:=Composition.machine first middle
def machine:=Composition.machine (prepare first middle) last

theorem pipeline_run (H : Fin 71→ℕ) (A : Fin 71→List Bool) (u v w : ℕ)
    (p : ExecutionReceipt 71 a) (q : ExecutionReceipt 71 b) (s : ExecutionReceipt 71 c)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom middle v (restart p.final middle.start)=some q)
    (hs : runFrom last w (restart (joinedReceipt p q).final last.start)=some s) :
    ∃ r,runFrom (machine first middle last) (u+1+v+1+w)
      ⟨(machine first middle last).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps+1+s.steps ∧
      r.final.heads=s.final.heads ∧ r.final.tapes=s.final.tapes := by
  have pq:=Composition.run_join first middle _ _ _ p q hp hq
  have full:=Composition.run_join (prepare first middle) last _ _ _ (joinedReceipt p q) s pq hs
  exact ⟨joinedReceipt (joinedReceipt p q) s,full,rfl,rfl,rfl⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralPipeline
