import Proof.CaseAnalysis.RowsSupportTermSupplier

/-! The three actual prefix calls reach the existing term exit with
their produced heads and tapes. Both circuit verdicts share this prefix;
only the final accepted branch will restore the private circuit bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_to_exit {s : ℕ} (circuit : Machine 1704 s) (readFuel circuitFuel : ℕ)
    (source : Configuration 2533 (sizes s 0))
    (reader : ExecutionReceipt 2533 (sizes s 0))
    (worker : ExecutionReceipt 2533 (sizes s 1))
    (flag : ExecutionReceipt 2533 (sizes s 2))
    (hr : runFrom (programs circuit 0) readFuel source=some reader)
    (hc : runFrom (programs circuit 1) circuitFuel
      (RecoveryCalls.restarted (programs circuit 1) reader.final.heads reader.final.tapes)=some worker)
    (hf : runFrom (programs circuit 2) 1
      (RecoveryCalls.restarted (programs circuit 2) worker.final.heads worker.final.tapes)=some flag)
    (hgood : reader.final.scanned 719=true) :
    ∃ n ≤ readFuel+circuitFuel+4,Timed (machine circuit) n
      (controlConfig (RecoveryCalls.code (sizes s) 0) source)
      (controlConfig (RecoveryCalls.code (sizes s) 3)
        (RecoveryCalls.restarted (programs circuit 3) flag.final.heads flag.final.tapes)) := by
  obtain ⟨a,ha,first⟩ := call_receipt (sizes s) (programs circuit) 0 next 0 1 readFuel _ reader hr (by
    change (if reader.final.scanned 719 then some (1 : Fin 5) else some 3)=some 1
    rw [hgood];rfl)
  obtain ⟨b,hb,second⟩ := call_receipt (sizes s) (programs circuit) 0 next 1 2 circuitFuel _ worker hc (by rfl)
  obtain ⟨c,hc,last⟩ := call_receipt (sizes s) (programs circuit) 0 next 2 3 1 _ flag hf (by rfl)
  exact ⟨a+b+c,by omega,(first.trans second).trans last⟩

theorem rejected_exit {s : ℕ} (circuit : Machine 1704 s) (fuel : ℕ)
    (source : Configuration 2533 (sizes s 3)) (last : ExecutionReceipt 2533 (sizes s 3))
    (hr : runFrom (programs circuit 3) fuel source=some last)
    (hfalse : last.final.scanned 724=false) :
    ∃ n ≤ fuel+1,Timed (machine circuit) n
      (controlConfig (RecoveryCalls.code (sizes s) 3) source)
      (RecoveryCalls.stopped (sizes s) last.final.heads last.final.tapes) := by
  exact stop_receipt (sizes s) (programs circuit) 0 next 3 fuel source last hr (by
    change (if last.final.scanned 724 then some (4 : Fin 5) else none)=none
    rw [hfalse];rfl)

theorem accepted_exit {s : ℕ} (circuit : Machine 1704 s) (exitFuel resetFuel : ℕ)
    (source : Configuration 2533 (sizes s 3))
    (committed : ExecutionReceipt 2533 (sizes s 3)) (cleared : ExecutionReceipt 2533 (sizes s 4))
    (he : runFrom (programs circuit 3) exitFuel source=some committed)
    (hr : runFrom (programs circuit 4) resetFuel
      (RecoveryCalls.restarted (programs circuit 4) committed.final.heads committed.final.tapes)=some cleared)
    (htrue : committed.final.scanned 724=true) :
    ∃ n ≤ exitFuel+resetFuel+2,Timed (machine circuit) n
      (controlConfig (RecoveryCalls.code (sizes s) 3) source)
      (RecoveryCalls.stopped (sizes s) cleared.final.heads cleared.final.tapes) := by
  obtain ⟨a,ha,first⟩ := call_receipt (sizes s) (programs circuit) 0 next 3 4 exitFuel source committed he (by
    change (if committed.final.scanned 724 then some (4 : Fin 5) else none)=some 4
    rw [htrue];rfl)
  obtain ⟨b,hb,last⟩ := stop_receipt (sizes s) (programs circuit) 0 next 4 resetFuel _ cleared hr (by rfl)
  exact ⟨a+b,by omega,first.trans last⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
