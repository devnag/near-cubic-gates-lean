import Proof.CaseAnalysis.RowsSupportSumPrepared
import Proof.CaseAnalysis.WitnessSumWorkRun

/-! The old single driver move enters the actual extended sum worker;
its new support head and tape are outside that move. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
open LocalBitMultitape CloseoutWitness
open CloseoutWitness.SupportDock (lift)
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def enter {s : ℕ} (p : Machine 3062 s):=
  Composition.machine (TapeEmbedding.machine 1 (SumCursor.move .right)) p

theorem enter_run {s : ℕ} (p : Machine 3062 s) (fuel position : ℕ)
    (out native counts supports : List Bool) (input : Fin 3061→List Bool) (last : ExecutionReceipt 3062 s)
    (hr : runFrom p fuel ⟨p.start,lift (CloseoutWitness.SumWork.heads position 1 out native counts) supports.length,
      lift input supports⟩=some last) (hs : last.steps ≤ fuel) :
    ∃ r,runFrom (enter p) (fuel+2)
      ⟨(enter p).start,lift (CloseoutWitness.SumWork.heads position 0 out native counts) supports.length,
        lift input supports⟩=some r ∧ r.steps ≤ fuel+2 ∧
      r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes:=by
  obtain ⟨base,br,bs,bh,bt⟩:=SumCursor.move_run .right (CloseoutWitness.SumWork.heads position 0 out native counts) input
  let first:=TapeEmbedding.receipt (fun _ : Fin 1=>supports.length) (fun _=>supports) base
  have firstRun:=TapeEmbedding.run_embed (SumCursor.move .right) (fun _ : Fin 1=>supports.length)
    (fun _=>supports) _ _ base br
  have fh:first.final.heads=lift (CloseoutWitness.SumWork.heads position 1 out native counts) supports.length:=by
    change lift base.final.heads supports.length=_
    rw [bh,CloseoutWitness.SumWork.driver_update]
    rfl
  have ft:first.final.tapes=lift input supports:=by
    change lift base.final.tapes supports=_
    rw [bt]
  have lastRun:runFrom p fuel ⟨p.start,first.final.heads,first.final.tapes⟩=some last:=by
    rw [fh,ft];exact hr
  obtain ⟨r,run,rs,rh,rt⟩:=joined (TapeEmbedding.machine 1 (SumCursor.move .right)) p 1 fuel _ _
    first last firstRun lastRun (by exact bs.le) hs
  have eq:1+1+fuel=fuel+2:=by omega
  rw [eq] at run rs
  exact ⟨r,run,rs,rh,rt⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
