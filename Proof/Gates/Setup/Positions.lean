import Proof.Gates.TermLoop.Defs
import Proof.Gates.Setup.Words

/-!
# Field positions on a guess word `prefix ++ blanks` (for `TermLoop.LoopFit.phys`)

The guess word is `u ++ false^pad` with `|u| = D = ⌊N/16⌋` (`Setup.guessWord`). Every reader of the codec advances by
at most a multiple of `D` while it is inside `u`, and by a constant per item in the blank region (a blank count is one
`false`). With `T = 2D`: a field end is `≤ max p T + 1`, an integer end `≤ max p T + 2`, a circuit end
`≤ max p T + 2 + 2D (q + 2)`, so after the oracle field, `aux` circuits and `k` witness fields the position is at most
`2D + 1 + aux (2 + 2D (q+2)) + k` (`fieldPos_fields_le`): a padding of that length makes every field physical.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close NearCubicGates.Close.Codec NearCubicGates.Close.TermLoop
open NearCubicGates.Close.Worker.Format (readCount)

theorem readCount_pad (l : List Bool) (m : ℕ) : (readCount (l ++ List.replicate m false)).1 ≤ l.length := by
  induction l with
  | nil => cases m <;> simp [readCount, List.replicate_succ]
  | cons b l ih =>
    cases b with
    | false => simp [readCount]
    | true => simp [readCount]; omega

theorem fieldLen_pad (u : List Bool) (pad p : ℕ) : fieldLen (u ++ List.replicate pad false) p ≤ u.length - p := by
  unfold fieldLen
  rw [List.drop_append, List.drop_replicate]
  have := readCount_pad (u.drop p) (pad - (p - u.length))
  simpa using this

theorem iter_le (f : ℕ → ℕ) (T a : ℕ) (hf : ∀ r, f r ≤ max r T + a) (p : ℕ) :
    ∀ k, iter f p k ≤ max p T + k * a
  | 0 => by simp [iter]
  | k + 1 => by
    rw [iter_succ']
    have h1 := hf (iter f p k)
    have h2 := iter_le f T a hf p k
    have : max (iter f p k) T ≤ max p T + k * a := max_le h2 (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
    rw [Nat.succ_mul]
    omega

section Word
variable (u : List Bool) (pad : ℕ)

theorem fieldEnd_le (r : ℕ) :
    fieldEnd (u ++ List.replicate pad false) r ≤ max r (2 * u.length) + 1 := by
  have := fieldLen_pad u pad r
  unfold fieldEnd
  omega

theorem intEnd_le (r : ℕ) : intEnd (u ++ List.replicate pad false) r ≤ max r (2 * u.length) + 2 := by
  have := fieldLen_pad u pad (r + 1)
  unfold intEnd
  omega

theorem gateEnd_le (q r : ℕ) :
    gateEnd (u ++ List.replicate pad false) r q ≤ max r (2 * u.length) + 2 * (q + 1) := by
  have h := iter_le (intEnd (u ++ List.replicate pad false)) (2 * u.length) 2 (intEnd_le u pad) r q
  have h2 := intEnd_le u pad (iter (intEnd (u ++ List.replicate pad false)) r q)
  unfold gateEnd
  have : max (iter (intEnd (u ++ List.replicate pad false)) r q) (2 * u.length) ≤ max r (2 * u.length) + q * 2 :=
    max_le h (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
  omega

theorem circuitEnd_le (q p : ℕ) :
    circuitEnd (u ++ List.replicate pad false) p q ≤ max p (2 * u.length) + (2 + 2 * u.length * (q + 2)) := by
  set w := u ++ List.replicate pad false with hw
  set D := u.length with hD
  have hK : cK w p ≤ D - p := fieldLen_pad u pad p
  have hP1 : cP1 w p ≤ max p (2 * D) + 1 := by unfold cP1; omega
  have hPg : cPg w p q ≤ max p (2 * D) + 1 + cK w p * (2 * (q + 1)) := by
    have h := iter_le (fun r => gateEnd w r q) (2 * D) (2 * (q + 1)) (gateEnd_le u pad q) (cP1 w p) (cK w p)
    unfold cPg
    have : max (cP1 w p) (2 * D) ≤ max p (2 * D) + 1 := max_le hP1 (by omega)
    omega
  have hPc : cPc w p q ≤ max p (2 * D) + 1 + cK w p * (2 * (q + 1)) + cK w p * 2 := by
    have h := iter_le (intEnd w) (2 * D) 2 (intEnd_le u pad) (cPg w p q) (cK w p)
    unfold cPc
    have : max (cPg w p q) (2 * D) ≤ max p (2 * D) + 1 + cK w p * (2 * (q + 1)) :=
      max_le hPg (by omega)
    omega
  have hL : cL w p q ≤ D - cPc w p q := fieldLen_pad u pad _
  have hKD : cK w p * (2 * (q + 1)) + cK w p * 2 ≤ 2 * D * (q + 2) := by
    have : cK w p ≤ D := by omega
    have e : cK w p * (2 * (q + 1)) + cK w p * 2 = 2 * cK w p * (q + 2) := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ (by omega)
  unfold circuitEnd cP2
  omega

/-- **Positions after the two circuit fields of the pair, `aux` circuits and `k` witness fields.** -/
theorem fieldPos_fields_le (q p0 aux k : ℕ) (hp0 : p0 ≤ 2 * u.length + 2) :
    fieldPos (u ++ List.replicate pad false) (circPos (u ++ List.replicate pad false) q p0 aux) k ≤
      2 * u.length + 2 + aux * (2 + 2 * u.length * (q + 2)) + k := by
  have h1 := iter_le (fun p => circuitEnd (u ++ List.replicate pad false) p q) (2 * u.length)
    (2 + 2 * u.length * (q + 2)) (fun r => circuitEnd_le u pad q r) p0 aux
  have h2 := iter_le (fieldEnd (u ++ List.replicate pad false)) (2 * u.length) 1 (fieldEnd_le u pad)
    (circPos (u ++ List.replicate pad false) q p0 aux) k
  unfold circPos at h2 ⊢
  unfold fieldPos
  have : max (iter (fun p => circuitEnd (u ++ List.replicate pad false) p q) p0 aux) (2 * u.length) ≤
      2 * u.length + 2 + aux * (2 + 2 * u.length * (q + 2)) := by
    refine max_le (h1.trans ?_) (by omega)
    have : max p0 (2 * u.length) ≤ 2 * u.length + 2 := max_le hp0 (by omega)
    omega
  omega

end Word

/-- The oracle field ends within `2⌊N/16⌋ + 1`. -/
theorem oracleEnd_le (N : ℕ) (bits : List Bool) (pad : ℕ) (hpad : N / 16 + 1 ≤ pad) :
    oracleEnd (guessWord N bits pad) ≤ 2 * (N / 16) + 1 := by
  obtain ⟨-, -, hl, -⟩ := guessWord_split N bits pad hpad
  unfold oracleEnd; omega

/-- The two circuit fields of the pair end within `2⌊N/16⌋ + 2`. -/
theorem pairEnd_le (N : ℕ) (bits : List Bool) (pad : ℕ) (hpad : N / 16 + 1 ≤ pad) :
    pairEnd (guessWord N bits pad) ≤ 2 * (N / 16) + 2 := by
  have h1 := oracleEnd_le N bits pad hpad
  have hu : (Codec.prefixBits bits (N / 16)).length = N / 16 := prefixBits_length _ _
  have h2 := fieldEnd_le (Codec.prefixBits bits (N / 16)) pad (oracleEnd (guessWord N bits pad))
  have hfe : fieldEnd (guessWord N bits pad) (oracleEnd (guessWord N bits pad)) = pairEnd (guessWord N bits pad) := by
    unfold fieldEnd pairEnd oracleEnd Codec.fieldLen
    omega
  rw [hu] at h2
  rw [← hfe]
  exact h2.trans (by omega)

/-- **`LoopFit.phys`**: with the padding at least `⌊N/16⌋ + 2 + aux (2 + 2⌊N/16⌋(q+2)) + 10 M`, every witness field
is physical. -/
theorem phys_of_pad (N : ℕ) (bits : List Bool) (pad q aux M : ℕ) (hpad : N / 16 + 1 ≤ pad)
    (hbig : N / 16 + 2 + aux * (2 + 2 * (N / 16) * (q + 2)) + 10 * M ≤ pad) :
    fieldPos (guessWord N bits pad) (circPos (guessWord N bits pad) q (pairEnd (guessWord N bits pad)) aux)
      (10 * M) ≤ (guessWord N bits pad).length := by
  have hu : (Codec.prefixBits bits (N / 16)).length = N / 16 := prefixBits_length _ _
  have h := fieldPos_fields_le (Codec.prefixBits bits (N / 16)) pad q (pairEnd (guessWord N bits pad)) aux (10 * M)
    (by rw [hu]; exact pairEnd_le N bits pad hpad)
  rw [hu] at h
  have hw : (guessWord N bits pad).length = N / 16 + pad := by simp [guessWord, prefixBits_length]
  rw [hw]
  exact h.trans (by omega)

end NearCubicGates.Close.Setup
