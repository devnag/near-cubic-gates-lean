import Proof.Amplification.RecoveryRawClauseState

/-! The clause tail is tested by an already verified actual literal body,
followed by the physical negation used as the clause's answer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RecoveryRawLiteralBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem tail_trace (x : State) (total : Nat) (hx : x.Valid) :
    ∃ n,n ≤ cost x+3 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 1) (cfg x total tailMachine.start))
      (RecoveryCalls.stopped sizes (cfg (inverted (output x)) total (0 : Fin 1)).heads
        (cfg (inverted (output x)) total (0 : Fin 1)).tapes) := by
  obtain ⟨first,hr,hf,_⟩ := tail_run x total hx
  have hn : next 1 first.final.control first.final.scanned=some 2 := rfl
  obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 1 2 (cost x) _ first hr hn
  obtain ⟨last,hr1,hf1,_⟩ := invert_run (output x) total
  obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 2 1 _ last hr1 (by rfl)
  rw [hf] at h0
  have h := h0.trans h1
  rw [hf1] at h
  exact ⟨n0+n1,by omega,h⟩

theorem inverted_valid (x : State) (hx : x.Valid) : (inverted x).Valid := hx

theorem inverted_output_bit (x : State) :
    (inverted (output x)).stream.data.present=decide (code x=0) := by
  change (!(output x).stream.data.present)=_
  rw [output_present]
  by_cases hz : code x=0 <;> simp [hz]

theorem inverted_width (x : State) : (inverted x).stream.width=x.stream.width := rfl

end NearCubicWires.RepairOrdinary.RecoveryRawClause
