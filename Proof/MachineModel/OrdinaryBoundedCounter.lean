import Proof.MachineModel.OrdinaryBinaryIncrement

/-! Binary increment at the actual bounded rank-counter interface. The output
is the encoded next integer, with reset heads and retained bounded scratch. -/
namespace NearCubicWires.RepairOrdinary.BoundedCounter
open LocalBitMultitape RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem binary_of_value (bits : List Bool) : binary bits.length (value bits) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases bit <;> simp [binary, value, ih, Nat.add_mul_div_left]

theorem true_value (width : ℕ) : value (List.replicate width true) + 1 = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [List.replicate_succ, value, Bool.toNat_true, pow_succ]
    omega

theorem carry_split (bits : List Bool) :
    (∃ count tail, bits = List.replicate count true ++ false :: tail) ∨
      bits = List.replicate bits.length true := by
  induction bits with
  | nil => exact Or.inr rfl
  | cons bit bits ih =>
    cases bit
    · exact Or.inl ⟨0, bits, rfl⟩
    · rcases ih with ⟨count, tail, he⟩ | he
      · exact Or.inl ⟨count + 1, tail, by simp [List.replicate_succ, he]⟩
      · exact Or.inr (by simpa [List.replicate_succ] using congrArg (List.cons true) he)

theorem increment_run (width n capacity : ℕ) (hn : n + 1 < 2 ^ width) (hc : capacity ≤ width) :
    ∃ nextCapacity : ℕ, ∃ r : ExecutionReceipt 2 4,
      nextCapacity ≤ width ∧
      run (Rewind.machine BinaryIncrement.machine) (2 * width + 2)
        (Fin.addCases (motive := fun _ : Fin (1 + 1) => List Bool)
          (fun _ : Fin 1 => binary width n)
          (fun _ : Fin 1 => List.replicate capacity false)) = some r ∧
      r.final.tapes 0 = binary width (n + 1) ∧
      r.final.tapes 1 = List.replicate nextCapacity false ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps ≤ 2 * width + 2 ∧ r.peakTapeCells ≤ 3 * width := by
  have hn' : n < 2 ^ width := by omega
  have split : ∃ count tail, binary width n = List.replicate count true ++ false :: tail := by
    rcases carry_split (binary width n) with h | h
    · exact h
    · have hv := congrArg value h
      rw [binary_value _ _ hn', binary_length] at hv
      have ht := true_value width
      omega
  obtain ⟨count, tail, he⟩ := split
  have hlen : count + 1 + tail.length = width := by
    have hl := congrArg List.length he
    simp only [binary_length, List.length_append, List.length_replicate, List.length_cons] at hl
    omega
  obtain ⟨r, hr, hout, hcounter, hh, hs, hp⟩ := BinaryIncrement.workspace_run count capacity tail (by omega)
  have hvalue : value (List.replicate count false ++ true :: tail) = n + 1 := by
    rw [BinaryIncrement.increment_value, ← he, binary_value _ _ hn']
  have houtput : List.replicate count false ++ true :: tail = binary width (n + 1) := by
    have h := binary_of_value (List.replicate count false ++ true :: tail)
    have hl : (List.replicate count false ++ true :: tail).length = width := by simp; omega
    rw [hl, hvalue] at h
    exact h.symm
  have hbound : 2 * count + 4 ≤ 2 * width + 2 := by omega
  refine ⟨max capacity (count + 1), r, by omega, ?_, hout.trans houtput, hcounter, hh,
    by omega, by omega⟩
  rw [← he] at hr
  have hmore := run_moreFuel (Rewind.machine BinaryIncrement.machine) (2 * count + 4)
    (2 * width + 2 - (2 * count + 4)) _ r hr
  rw [Nat.add_sub_of_le hbound] at hmore
  exact hmore

end NearCubicWires.RepairOrdinary.BoundedCounter
