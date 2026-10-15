import Proof.MachineModel.ClockTotal

/-! The total clock's physical output is the literal canonical `.bits` field
required by the selected source constructor, including at empty input. -/
namespace NearCubicWires.RepairOrdinary.ClockTotal
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem power_bits (r : ℕ) : (2^r).bits=List.replicate r false++[true] := by
  induction r with
  | zero => simp [Nat.one_bits]
  | succ r ih =>
    rw [pow_succ,Nat.mul_comm, Nat.bit0_bits _ (by positivity),ih,List.replicate_succ]
    rfl

theorem clock_binary_bits (k c N : ℕ) :
    SignedSortKey.binary (ClockEnvelope.exponent k c N+1) (ClockEnvelope.clock k c N)=
      (ClockEnvelope.clock k c N).bits := by
  rw [← ClockFromInput.clock_word_binary]
  exact (power_bits _).symm

theorem canonical_run (k c : ℕ) (bits : List Bool) :
    ∃ r : ExecutionReceipt 34 (Fintype.card (RecoveryCalls.Control (sizes k c))),
      run (machine k c) (budget k c bits) (ClockFromInput.input bits)=some r ∧
      r.final.tapes 29=frame (ClockEnvelope.clock k c bits.length).bits ∧
      r.final.tapes 27=List.replicate (ClockEnvelope.exponent k c bits.length) true ∧
      r.final.tapes 12=frame bits ∧ (∀ i,r.final.heads i=0) ∧ r.steps≤budget k c bits := by
  simpa only [clock_binary_bits] using entry_run k c bits

end NearCubicWires.RepairOrdinary.ClockTotal
