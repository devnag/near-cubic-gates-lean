import Proof.Foundations.OrdinaryComposition
import Proof.Foundations.OrdinaryWilliamsLoader

/-! Apply the generic linker to the actual copy/rewind machine. The second
machine receives the exact tapes left by the first, including its retained
zero-filled counter. This does not silently replace scratch tapes by `[]`. -/
namespace NearCubicWires.RepairOrdinary.CopyComposition
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def afterCopyTapes (bs : List Bool) : Fin 3 → List Bool :=
  fun t => if t.val = 0 then frame bs
    else if t.val = 1 then bs else List.replicate bs.length false

theorem copy_then {s : ℕ} (q : Machine 3 s) (bs : List Bool) (fuel : ℕ)
    (next : ExecutionReceipt 3 s) (hq : run q fuel (afterCopyTapes bs) = some next) :
    ∃ receipt : ExecutionReceipt 3 (5 + s),
      run (Composition.machine Streaming.machine q) (4 * bs.length + 3 + fuel)
        (fun t => if t.val = 0 then frame bs else []) = some receipt ∧
      receipt.final.tapes = next.final.tapes ∧
      receipt.final.heads = next.final.heads ∧
      receipt.steps = 4 * bs.length + 3 + next.steps ∧
      receipt.peakTapeCells ≤ max (4 * bs.length + 1) next.peakTapeCells := by
  obtain ⟨copied, hc, hf, hs, hp⟩ := Streaming.copy_run bs
  have hnext : runFrom q fuel (Composition.restart copied.final q.start) = some next := by
    rw [hf]
    have hconfig : Composition.restart (Streaming.finished (frame bs) bs bs.length) q.start =
        initialConfiguration q (afterCopyTapes bs) := by
      apply configuration_ext
      · rfl
      · funext t
        simp [Composition.restart, Streaming.finished, Streaming.config, initialConfiguration]
      · rfl
    rw [hconfig]
    exact hq
  have hjoin := Composition.run_join Streaming.machine q (4 * bs.length + 2) fuel
    _ copied next hc hnext
  refine ⟨Composition.joinedReceipt copied next, ?_, rfl, rfl, ?_, ?_⟩
  · simpa [run, initialConfiguration, Composition.machine, Composition.leftConfig,
      Nat.add_assoc] using hjoin
  · simp [Composition.joinedReceipt, hs, Nat.add_assoc]
  · exact max_le_max_right _ hp

/-- The enclosing matrix-source application retains additive execution costs.
    `hq` is the actual callee receipt, not an invented time annotation. -/
theorem williams_copy_then {s : ℕ} (q : Machine 3 s) (u R width : ℕ)
    (a : SourceInterfaces.BitMatrix u (SourceInterfaces.integerCeilRoot 10 u))
    (hcell : u * u ≤ 2 * R) (hbits : natBitLength u ≤ width + 2)
    (fuel : ℕ) (next : ExecutionReceipt 3 s)
    (hq : run q fuel (afterCopyTapes (WilliamsLoader.payload u a)) = some next) :
    ∃ receipt : ExecutionReceipt 3 (5 + s),
      run (Composition.machine Streaming.machine q)
        (4 * (WilliamsLoader.payload u a).length + 3 + fuel)
        (fun t => if t.val = 0 then frame (WilliamsLoader.payload u a) else []) = some receipt ∧
      receipt.final.tapes = next.final.tapes ∧
      receipt.final.heads = next.final.heads ∧
      receipt.steps ≤ 8 * R + 8 * width + 23 + next.steps ∧
      receipt.peakTapeCells ≤ max (8 * R + 8 * width + 21) next.peakTapeCells := by
  obtain ⟨receipt, hr, ht, hh, hs, hp⟩ := copy_then q (WilliamsLoader.payload u a) fuel next hq
  have hc : SourceInterfaces.integerCeilRoot 10 u ≤ u :=
    SourceInterfaces.integerCeilRoot_le (by decide) (Nat.le_self_pow (by decide) u)
  have hm : u * SourceInterfaces.integerCeilRoot 10 u ≤ 2 * R :=
    (Nat.mul_le_mul_left u hc).trans hcell
  refine ⟨receipt, hr, ht, hh, ?_, ?_⟩
  · rw [WilliamsLoader.payload_length] at hs
    omega
  · apply hp.trans
    apply max_le_max_right
    rw [WilliamsLoader.payload_length]
    omega

end NearCubicWires.RepairOrdinary.CopyComposition
