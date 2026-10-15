import Proof.Gates.Worker.Format

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Worker NearCubicGates.Close.Worker.Format NearCubicGates.Close.Interfaces
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem countWord_length (k : ℕ) : (countWord k).length = k + 1 := by simp [countWord]

theorem fieldWord_length (b : List Bool) : (fieldWord b).length = 2 * b.length + 1 := by
  simp [fieldWord, countWord_length]; omega

theorem numWord_length (x : ℕ) : (numWord x).length = 2 * natBitLength x + 1 := by
  simp [numWord, fieldWord_length, SignedSortKey.binary_length]

theorem nbl_le_of_lt {v B : ℕ} (hB : 1 ≤ B) (hv : v < 2 ^ B) : natBitLength v ≤ B := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hv
    omega

theorem nbl_le_self (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 v
  omega

theorem intWordF_length (z : ℤ) : (intWordF z).length = 2 * natBitLength z.natAbs + 2 := by
  simp [intWordF, numWord_length]

theorem intWordF_le_of_lt {z : ℤ} {B : ℕ} (hB : 1 ≤ B) (hz : z.natAbs < 2 ^ B) : (intWordF z).length ≤ 2 * B + 2 := by
  rw [intWordF_length]; have := nbl_le_of_lt hB hz; omega

theorem intWordF_le_abs (z : ℤ) : (intWordF z).length ≤ 2 * z.natAbs + 4 := by
  rw [intWordF_length]; have := nbl_le_self z.natAbs; omega

theorem gateWordF_le {q B : ℕ} (hB : 1 ≤ B) (G : NormalizedThresholdGate q)
    (hG : (∀ i, (G.weight i).natAbs < 2 ^ B) ∧ G.threshold.natAbs < 2 ^ B) :
    (gateWordF G).length ≤ (q + 1) * (2 * B + 2) := by
  unfold gateWordF
  rw [List.length_append, List.length_flatMap]
  have h1 : ((List.ofFn G.weight).map fun z => (intWordF z).length).sum ≤ q * (2 * B + 2) := by
    have := List.sum_le_card_nsmul ((List.ofFn G.weight).map fun z => (intWordF z).length) (2 * B + 2) (by
      intro a ha
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact intWordF_le_of_lt hB (hG.1 i))
    simpa using this
  have h2 := intWordF_le_of_lt hB hG.2
  nlinarith

theorem coeffs_length_le {q : ℕ} (C : NCircuit q) (h0 : ∀ a ∈ C.coeffs, a ≠ 0) : C.coeffs.length ≤ C.topWeight := by
  unfold NCircuit.topWeight
  have : ∀ a ∈ C.coeffs.map Int.natAbs, 1 ≤ a := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact Int.natAbs_pos.mpr (h0 z hz)
  have := List.length_le_sum_of_one_le _ this
  simpa using this

theorem coeffWords_le {q : ℕ} (C : NCircuit q) :
    (C.coeffs.flatMap intWordF).length ≤ 2 * C.topWeight + 4 * C.coeffs.length := by
  unfold NCircuit.topWeight
  induction C.coeffs with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have := intWordF_le_abs a
    omega

/-- **One circuit's word.** -/
theorem circuitWordF_le {q B : ℕ} (hB : 1 ≤ B) (C : NCircuit q) (hC : C.WellFormed B) :
    (circuitWordF C).length ≤ (C.topWeight + 1) * ((q + 1) * (2 * B + 2) + 12) := by
  obtain ⟨hgc, h0, htab, hg⟩ := hC
  have hc := coeffs_length_le C h0
  have hgl : C.gates.length ≤ C.topWeight := hgc ▸ hc
  unfold circuitWordF
  simp only [List.length_append, countWord_length, fieldWord_length, List.length_flatMap]
  have hgates : (C.gates.map fun G => (gateWordF G).length).sum ≤ C.gates.length * ((q + 1) * (2 * B + 2)) := by
    have := List.sum_le_card_nsmul (C.gates.map fun G => (gateWordF G).length) ((q + 1) * (2 * B + 2)) (by
      intro a ha
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp ha
      exact gateWordF_le hB G (hg G hG))
    simpa using this
  have hcw := coeffWords_le C
  rw [List.length_flatMap] at hcw
  rw [htab]
  have hm : C.gates.length * ((q + 1) * (2 * B + 2)) ≤ C.topWeight * ((q + 1) * (2 * B + 2)) :=
    Nat.mul_le_mul_right _ hgl
  nlinarith

end NearCubicGates.Close.WorkerArith.WorkerBounds
