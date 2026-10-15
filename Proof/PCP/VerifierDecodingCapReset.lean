import Proof.PCP.VerifierDecodingCap
import Proof.MachineModel.OrdinaryUnaryTemplate

/-! Paid cursor return on a capped unary counter. The count and its explicit
backing are retained; the entry cursor may be anywhere in its true region. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.CapMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counter_zero (cap value : ℕ) : readTapeBit (counter cap value) 0 = false := by
  rw [counter, ZeroPadding.read_pad]
  rfl

theorem reset_run (cap value position : ℕ) (hv : value ≤ cap) (hp : position ≤ value) :
    ∃ receipt : ExecutionReceipt 1 3,
      runFrom UnaryTemplate.machine (position+2)
        (UnaryTemplate.config 0 (counter cap value) (position+1)) = some receipt ∧
      receipt.final = UnaryTemplate.config 2 (counter cap value) 1 ∧
      receipt.steps = position+2 ∧ receipt.peakTapeCells ≤ cap+2 := by
  have hl : (counter cap value).length = cap+2 := counter_length cap value hv
  have h := UnaryTemplate.return_prefix (counter cap value) position (counter_zero cap value)
    (by intro k hk; rw [counter_read]; simp only [decide_eq_true_eq]; omega)
  rw [hl] at h
  have prefixRun := Prefix.step (by rw [UnaryTemplate.config_cells, hl]) (by rfl)
    (UnaryTemplate.start_step (counter cap value) position) h
  obtain ⟨receipt, hr, hf, hs, hb⟩ := prefixRun.run (by rfl) (by rw [UnaryTemplate.config_cells, hl])
  exact ⟨receipt, by simpa [Nat.add_assoc] using hr, hf, by omega, hb⟩

end NearCubicWires.RepairSource.VerifierDecoding.CapMachine
