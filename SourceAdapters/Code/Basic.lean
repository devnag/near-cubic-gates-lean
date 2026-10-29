import NineInputs

/-! Elementary source-code consequences for `app:sources`, "Uniform three-query PCPP and code interfaces". -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code

theorem relativeHamming_self {n : ℕ} (x : BitInput n) : relativeHamming x x = 0 := by
  simp [relativeHamming]

theorem relativeHamming_nonneg {n : ℕ} (x y : BitInput n) : 0 ≤ relativeHamming x y := by
  unfold relativeHamming
  positivity

theorem relativeHamming_eq_zero_iff {n : ℕ} (hn : 0 < n) (x y : BitInput n) :
    relativeHamming x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hc : (Finset.univ.filter fun i => x i ≠ y i).card = 0 := by
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simpa [relativeHamming, hn'] using h
    have he := Finset.card_eq_zero.mp hc
    funext i
    by_contra hi
    have : i ∈ Finset.univ.filter fun j => x j ≠ y j := by simp [hi]
    rw [he] at this
    exact Finset.notMem_empty _ this
  · rintro rfl
    exact relativeHamming_self x

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the identity code's nonzero distance at a finite length. -/
theorem inverse_length_le_relativeHamming {n : ℕ} (hn : 0 < n)
    (x y : BitInput n) (hxy : x ≠ y) : 1 / (n : ℝ) ≤ relativeHamming x y := by
  have hc : 0 < (Finset.univ.filter fun i => x i ≠ y i).card := by
    rw [Finset.card_pos]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact ⟨i, by simp [hi]⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold relativeHamming
  apply (div_le_div_iff_of_pos_right hn').2
  exact_mod_cast hc

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": positive minimum distance makes every source encoder injective. -/
theorem source_encode_injective (F : BinaryFamily) (onset : ℕ) (distance : ℝ)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance)
    (n : ℕ) (hn : onset ≤ n) : Function.Injective (F.encode n) := by
  intro x y hxy
  by_contra hne
  have h := hmin n hn x y hne
  rw [hxy, relativeHamming_self] at h
  exact (not_le_of_gt hd) h

/-- Cardinality argument used in released `Proof/Gates/Gadget/ThreeQuery.lean`:
`app:sources`, "Uniform three-query PCPP and code interfaces" needs a positive lower block-length ratio. -/
theorem source_length_lower (F : BinaryFamily) (onset : ℕ) (distance : ℝ)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance)
    (n : ℕ) (hn : onset ≤ n) : n ≤ F.length n := by
  have h := Fintype.card_le_of_injective _ (source_encode_injective F onset distance hd hmin n hn)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": run the promised decoder for its fixed polynomial budget;
on timeout return the zero word. On malformed output, missing bits are zero.
This definition asserts totality, but does not itself specify a machine realization. -/
def totalDecoder (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (n : ℕ) (y : BitInput (F.length n)) : BitInput n :=
  match run D.program.machine (D.coefficient * (n + F.length n + 1) ^ D.exponent)
      (D.program.inputTapes (decoderInput F n y)) with
  | none => fun _ => false
  | some receipt => fun i => (receipt.final.tapes D.program.outputTape)[i.val]?.getD false

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": clocking preserves every promised decoder answer. -/
theorem totalDecoder_correct (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (n : ℕ) (hn : onset ≤ n)
    (x : BitInput n) (y : BitInput (F.length n))
    (hnear : relativeHamming (F.encode n x) y ≤ radius) : totalDecoder F D n y = x := by
  obtain ⟨receipt, hrun, hout⟩ := D.decodes n hn x y hnear
  funext i
  simp [totalDecoder, hrun, hout, i.isLt]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": balanced block sizes, in order from longest to shortest. -/
def blockSize (n : ℕ) (i : Fin 3) : ℕ := (n + 2 - i.val) / 3

theorem blockSize_sum (n : ℕ) : blockSize n 0 + blockSize n 1 + blockSize n 2 = n := by
  simp only [blockSize, Fin.val_zero, Fin.val_one]
  omega

theorem blockSize_bounds (n : ℕ) (i : Fin 3) :
    n / 3 ≤ blockSize n i ∧ blockSize n i ≤ (n + 2) / 3 := by
  have hi := i.isLt
  unfold blockSize
  omega

theorem blockSize_le_half (n : ℕ) (hn : 2 ≤ n) (i : Fin 3) : blockSize n i ≤ n / 2 := by
  have h := (blockSize_bounds n i).2
  omega

/-- Beyond this cutoff every source block is past the source onset and has
at least one sixth of the original message length (`app:sources`, "Uniform three-query PCPP and code interfaces"). -/
theorem blockSize_large (onset n : ℕ) (hn : 6 * (onset + 1) ≤ n) (i : Fin 3) :
    onset ≤ blockSize n i ∧ n ≤ 6 * blockSize n i := by
  have h := (blockSize_bounds n i).1
  omega

end NearCubicGates.Adapters.Code
