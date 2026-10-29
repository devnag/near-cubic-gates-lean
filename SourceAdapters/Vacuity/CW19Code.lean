import SourceAdapters.Code.Basic
import Proof.Foundations.OrdinaryStreaming

/-!
# CW19 source-model checks

The threefold repetition family witnesses binary linearity at every length;
the one-bit, three-coordinate instance has distance one and corrects one
error. This is a finite model check, not an assertion that coordinatewise
repetition has constant relative distance at unbounded message lengths.
The ordinary identity-copy construction separately checks that the source ordinary
program semantics admits an actual input-reading, output-writing program.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Vacuity.CW19Code

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code

def repetition : BinaryFamily where
  length n := 3 * n
  encode n x j := x ⟨j.val / 3, by have h := j.isLt; omega⟩

theorem repetition_linear : IsLinear repetition := by
  constructor
  · intro n; rfl
  · intro n x y; rfl

theorem repetition_rate (n : ℕ) : repetition.length n = 3 * n := rfl

theorem repetition_one_apply (x : BitInput 1) (j : Fin (repetition.length 1)) :
    repetition.encode 1 x j = x 0 := by
  apply congrArg x
  exact Subsingleton.elim _ _

theorem repetition_one_eq (x : BitInput 1) :
    repetition.encode 1 x = (fun _ : Fin 3 => x 0) := by
  funext j
  exact repetition_one_apply x j

theorem repetition_one_distance (x y : BitInput 1) (hxy : x ≠ y) :
    relativeHamming (repetition.encode 1 x) (repetition.encode 1 y) = 1 := by
  have h0 : x 0 ≠ y 0 := by
    intro h
    apply hxy
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using h
  rw [repetition_one_eq, repetition_one_eq]
  change ((Finset.univ.filter fun _ : Fin 3 => x 0 ≠ y 0).card : ℝ) / 3 = 1
  have hf : (Finset.univ.filter fun _ : Fin 3 => x 0 ≠ y 0) = Finset.univ := by simp [h0]
  rw [hf]
  have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := by decide
  rw [hcard]
  norm_num

def majority (y : BitInput 3) : BitInput 1 :=
  fun _ => (y 0 && y 1) || (y 0 && y 2) || (y 1 && y 2)

private theorem card_errors_three (x y : BitInput 3) :
    (Finset.univ.filter fun i => x i ≠ y i).card =
      (if x 0 ≠ y 0 then 1 else 0) + (if x 1 ≠ y 1 then 1 else 0) +
        (if x 2 ≠ y 2 then 1 else 0) := by
  rw [Finset.card_filter]
  simp [Fin.sum_univ_succ, Nat.add_assoc]
  rfl

/-- One-bit repetition really corrects one arbitrary error in three bits. -/
theorem repetition_one_decodes (x : BitInput 1) (y : BitInput 3)
    (hnear : relativeHamming (repetition.encode 1 x) y ≤ (1 : ℝ) / 3) :
    majority y = x := by
  rw [repetition_one_eq] at hnear
  have hc : (Finset.univ.filter fun i : Fin 3 => x 0 ≠ y i).card ≤ 1 := by
    have h : ((Finset.univ.filter fun i : Fin 3 => x 0 ≠ y i).card : ℝ) / 3 ≤ 1 / 3 := hnear
    have h' := (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).mp h
    exact_mod_cast h'
  rw [card_errors_three] at hc
  have hmaj : ((y 0 && y 1) || (y 0 && y 2) || (y 1 && y 2)) = x 0 := by
    cases hx : x 0 <;> cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;>
      simp_all
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [majority, hi] using hmaj

/-- The distance conclusion is substantive: a zero encoder does not have
positive minimum distance even at message length one. -/
theorem zero_encoder_not_positive_distance (distance : ℝ) (hd : 0 < distance) :
    ¬ (∀ x y : BitInput 1, x ≠ y →
      distance ≤ relativeHamming (fun _ : Fin 3 => false) (fun _ => false)) := by
  intro h
  have hne : (fun _ : Fin 1 => false) ≠ (fun _ => true) := by
    intro heq
    have he := congrFun heq 0
    contradiction
  have hz := h (fun _ => false) (fun _ => true) hne
  rw [NearCubicGates.Adapters.Code.relativeHamming_self] at hz
  exact (not_le_of_gt hd) hz

/-- Existing proved construction, no new machine premise: ordinary source programs
can copy an arbitrary bit word with an explicit linear bound. -/
theorem ordinary_copy_inhabited :
    Nonempty (WordFunction (List Bool) id id (fun bs => 4 * bs.length + 2)) :=
  ⟨Streaming.rewoundIdentityCopy.toWordFunction⟩

/-- The chosen outer framing convention has exactly linear overhead. The
proof is the existing ordinary-machine construction, not a source hypothesis. -/
theorem source_frame_length (word : List Bool) : (frame word).length = 2 * word.length + 1 :=
  frame_length word

/-- The independent unary source tuple accounts for every input bit. -/
theorem source_decoder_input_length (F : BinaryFamily) (n : ℕ) (y : BitInput (F.length n)) :
    (decoderInput F n y).length = n + F.length n + 1 := by
  simp [decoderInput]
  omega

theorem source_decoder_framed_length (F : BinaryFamily) (n : ℕ) (y : BitInput (F.length n)) :
    (frame (decoderInput F n y)).length = 2 * (n + F.length n + 1) + 1 := by
  rw [frame_length, source_decoder_input_length]

/-- Actual exact-output copy runs preserve arbitrarily many trailing zeros. -/
theorem ordinary_copy_trailing_zeros (word : List Bool) (zeros : ℕ) :
    ∃ receipt,
      LocalBitMultitape.run Streaming.copyProgram.machine
        (4 * (word ++ List.replicate zeros false).length + 2)
        (Streaming.copyProgram.inputTapes (word ++ List.replicate zeros false)) = some receipt ∧
      receipt.final.tapes Streaming.copyProgram.outputTape = word ++ List.replicate zeros false :=
  Streaming.rewoundIdentityCopy.realizes _

end NearCubicGates.Adapters.Vacuity.CW19Code
