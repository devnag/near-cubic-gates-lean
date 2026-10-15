import Proof.Foundations.OrdinaryStreaming
import Proof.Foundations.OperationalWilliamsSourceCore

/-!
The paid copy-and-rewind applied to the real corrected Williams input format.
This consumes a generated framed stream. Constructing that stream from the
row generator, and linking the published multiplication machine, remain
separate producer/composition obligations; neither is hidden in this receipt.
-/
namespace NearCubicWires.RepairOrdinary.WilliamsLoader
open LocalBitMultitape SourceInterfaces WilliamsLoaderForms
open WilliamsPublishedForm
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem matrix_length {r c : ℕ} (a : BitMatrix r c) :
    (rowMajorBitMatrix a).length = r * c := by
  simp [rowMajorBitMatrix, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.ofFn_const]

@[simp] theorem nat_frame_length (u : ℕ) :
    (framedNatBits u).length = 2 * natBitLength u + 1 := by
  simp [framedNatBits, WilliamsPublishedForm.fixedWidthNatBits]
  omega

def payload (u : ℕ) (a : BitMatrix u (integerCeilRoot 10 u)) : List Bool :=
  framedNatBits u ++ rowMajorBitMatrix a

@[simp] theorem payload_length (u : ℕ) (a : BitMatrix u (integerCeilRoot 10 u)) :
    (payload u a).length = 2 * natBitLength u + 1 + u * integerCeilRoot 10 u := by
  simp [payload]

theorem copy_rewind_consumer (u R q : ℕ)
    (a : BitMatrix u (integerCeilRoot 10 u))
    (hcell : u * u ≤ 2 * R) (hbits : natBitLength u ≤ q + 2) :
    ∃ receipt : ExecutionReceipt 3 5,
      run Streaming.machine (4 * (payload u a).length + 2)
        (fun t => if t.val = 0 then frame (payload u a) else []) = some receipt ∧
      receipt.final.tapes 1 = payload u a ∧
      (∀ t, receipt.final.heads t = 0) ∧
      receipt.steps ≤ 8 * R + 8 * q + 22 ∧
      receipt.peakTapeCells ≤ 8 * R + 8 * q + 21 := by
  obtain ⟨receipt, hrun, hfinal, hsteps, hpeak⟩ := Streaming.copy_run (payload u a)
  have hc : integerCeilRoot 10 u ≤ u :=
    integerCeilRoot_le (by decide) (Nat.le_self_pow (by decide) u)
  have hm : u * integerCeilRoot 10 u ≤ 2 * R :=
    (Nat.mul_le_mul_left u hc).trans hcell
  refine ⟨receipt, hrun, ?_, ?_, ?_, ?_⟩
  · simp [hfinal, Streaming.finished, Streaming.config]
  · intro t
    simp [hfinal, Streaming.finished, Streaming.config]
  · rw [payload_length] at hsteps
    omega
  · rw [payload_length] at hpeak
    omega

end NearCubicWires.RepairOrdinary.WilliamsLoader
