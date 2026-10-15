import Proof.CaseAnalysis.RecoveryClauseOrRun

/-! Original five-stage clause composition, reusing the checked three-stage
literal pipeline twice. Definitions and joins stay symbolic in state counts. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClausePipeline
open LocalBitMultitape Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {a b c : ℕ} (first : Machine 71 a) (second : Machine 71 b) (join : Machine 71 c)
def prepare:=RecoveryBoundedLiteralPipeline.machine first second join
def machine:=RecoveryBoundedLiteralPipeline.machine (prepare first second join) second join

theorem clause_run (H : Fin 71→ℕ) (A : Fin 71→List Bool) (B : ℕ)
    (p : ExecutionReceipt 71 a) (q : ExecutionReceipt 71 b) (r : ExecutionReceipt 71 c)
    (s : ExecutionReceipt 71 b) (t : ExecutionReceipt 71 c)
    (hp : runFrom first B ⟨first.start,H,A⟩=some p)
    (hq : runFrom second B (restart p.final second.start)=some q)
    (hr : runFrom join B (restart (joinedReceipt p q).final join.start)=some r)
    (hs : runFrom second B (restart r.final second.start)=some s)
    (ht : runFrom join B (restart s.final join.start)=some t) :
    ∃ result,runFrom (machine first second join) (5*B+4)
      ⟨(machine first second join).start,H,A⟩=some result ∧
      result.steps=p.steps+1+q.steps+1+r.steps+1+s.steps+1+t.steps ∧
      result.final.heads=t.final.heads ∧ result.final.tapes=t.final.tapes := by
  obtain ⟨u,ur,us,uh,ut⟩:=RecoveryBoundedLiteralPipeline.pipeline_run first second join H A B B B p q r hp hq hr
  have hs' : runFrom second B (restart u.final second.start)=some s := by
    change runFrom _ _ ⟨_,u.final.heads,u.final.tapes⟩=some s
    rw [uh,ut]
    exact hs
  obtain ⟨result,rr,rs,rh,rt⟩:=RecoveryBoundedLiteralPipeline.pipeline_run (prepare first second join) second join H A
    (B+1+B+1+B) B B u s t ur hs' ht
  have hc : B+1+B+1+B+1+B+1+B=5*B+4:=by omega
  rw [hc] at rr
  refine ⟨result,rr,?_,rh,rt⟩
  rw [rs,us]

end NearCubicWires.RepairOrdinary.RecoveryBoundedClausePipeline
