import SourceAdapters.Code.CappedInput
import SourceAdapters.Code.ResultParsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": complete paid capped source calls. X8 is the only open
machine join consumed here; no target-shaped implementation premise is added. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Adapters.Joins
open NearCubicGates.Published.CW19Code

/-- A fixed polynomial clock can be supplied, executed and its framed result
parsed by actual ordinary programs, with a polynomial total clock. -/
theorem clocked_wordFunction (hX8 : CappedWordRun) (p : Program) (K offset e : ℕ) :
    ∃ C d : ℕ, Nonempty (WordFunction (List Bool) id
      (fun word => frame (cappedOutput p (K * (word.length + offset) ^ e, word)))
      (fun word => C * (word.length + 1) ^ d)) := by
  obtain ⟨C, Q⟩ := Parsing.framedCapped_of_X8 hX8 p
  obtain ⟨Q⟩ := Q
  let P := CappedInput.wordFunction K offset e
  let R : WordFunction (List Bool)
      (fun word => cappedRequestWord (K * (word.length + offset) ^ e, word))
      (fun word => frame (cappedOutput p (K * (word.length + offset) ^ e, word)))
      (fun word => C * (K * (word.length + offset) ^ e + word.length + 1)) :=
    { program := Q.program
      realizes := fun word => Q.realizes (K * (word.length + offset) ^ e, word) }
  let W := composeFramed P R
  have hR : ∃ A d : ℕ, ∀ word : List Bool,
      C * (K * (word.length + offset) ^ e + word.length + 1) ≤ A * (word.length + 1) ^ d := by
    refine ⟨C * (K * (offset + 1) ^ e + 1), e + 1, fun word => ?_⟩
    let n := word.length
    have hb : n + offset ≤ (offset + 1) * (n + 1) := by nlinarith
    have hp := Nat.pow_le_pow_left hb e
    rw [mul_pow] at hp
    have he := Nat.pow_le_pow_right (show 1 ≤ n + 1 by omega) (show e ≤ e + 1 by omega)
    have hm := Nat.mul_le_mul_left ((offset + 1) ^ e) he
    have hclock := Nat.mul_le_mul_left K (le_trans hp hm)
    have hn : n + 1 ≤ (n + 1) ^ (e + 1) := Nat.le_self_pow (by omega) _
    have ht : K * (n + offset) ^ e + n + 1 ≤ (K * (offset + 1) ^ e + 1) * (n + 1) ^ (e + 1) := by
      nlinarith
    exact (Nat.mul_le_mul_left C ht).trans_eq (by ring)
  obtain ⟨A, d, hA⟩ := composeFramed_budget_poly (id : List Bool → List Bool)
    (CappedInput.budget K offset e) (fun word => C * (K * (word.length + offset) ^ e + word.length + 1))
    (CappedInput.budget_poly K offset e) hR
  exact ⟨A, d, ⟨W.enlargeBudget hA⟩⟩

/-- A source encoder callable by the code construction: raw source input,
exact framed output, and a paid polynomial clock. -/
theorem framed_encoder_wordFunction (hX8 : CappedWordRun) (F : BinaryFamily) {onset : ℕ}
    (A : EfficientEncoder F onset) :
    ∃ C d : ℕ, Nonempty (WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => frame (List.ofFn (F.encode p.1 p.2.val))) (fun p => C * (p.1 + 1) ^ d)) := by
  obtain ⟨C, d, W⟩ := clocked_wordFunction hX8 A.program A.coefficient 1 A.exponent
  obtain ⟨W⟩ := W
  refine ⟨C, d, ⟨{ program := W.program, realizes := ?_ }⟩⟩
  intro p
  obtain ⟨r, hr, ho⟩ := W.realizes (sourceMessageWord p)
  obtain ⟨s, hs, hout⟩ := A.encodes p.1 p.2.property p.2.val
  refine ⟨r, by simpa [sourceMessageWord] using hr, ?_⟩
  simpa [cappedOutput, sourceMessageWord, hs, hout] using ho

/-- Every source decoder request has an actual capped run. Its framed
payload is the one used in `totalDecoder_capped_output`, even off promise. -/
theorem framed_decoder_wordFunction (hX8 : CappedWordRun) (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) :
    ∃ C d : ℕ, Nonempty (WordFunction (TotalSourceRequest F)
      (fun p => decoderInput F p.1 p.2)
      (fun p => frame (cappedOutput D.program (decoderCappedRequest F D p)))
      (fun p => C * ((decoderInput F p.1 p.2).length + 1) ^ d)) := by
  obtain ⟨C, d, W⟩ := clocked_wordFunction hX8 D.program D.coefficient 0 D.exponent
  obtain ⟨W⟩ := W
  refine ⟨C, d, ⟨{ program := W.program, realizes := ?_ }⟩⟩
  intro p
  obtain ⟨r, hr, ho⟩ := W.realizes (decoderInput F p.1 p.2)
  refine ⟨r, hr, ?_⟩
  have hl : (decoderInput F p.1 p.2).length = p.1 + F.length p.1 + 1 := by
    simp [decoderInput]; omega
  simpa only [Nat.add_zero, hl, decoderCappedRequest] using ho

end NearCubicGates.Adapters.Code
