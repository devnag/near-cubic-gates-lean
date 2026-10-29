import SourceAdapters.Code.FinitePatch
import Proof.Foundations.OrdinaryRewindCarrier

/-!
`app:sources`, "Uniform three-query PCPP and code interfaces": source program carriers and exact word identities used by the
ordinary encoder/decoder composition. Source programs here retain their own
input encoding; the target parsing and assembly are separate constructions.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code

abbrev SourceMessage (onset : ℕ) := Σ n : ℕ, {_x : BitInput n // onset ≤ n}

def sourceMessageWord {onset : ℕ} (p : SourceMessage onset) : List Bool := List.ofFn p.2.val

def sourceEncoderBudget (F : BinaryFamily) {onset : ℕ} (A : EfficientEncoder F onset)
    (p : SourceMessage onset) : ℕ := A.coefficient * (p.1 + 1) ^ A.exponent

/-- The actual source encoder as the platform's ordinary carrier. -/
def sourceEncoderWordFunction (F : BinaryFamily) {onset : ℕ} (A : EfficientEncoder F onset) :
    WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => List.ofFn (F.encode p.1 p.2.val)) (sourceEncoderBudget F A) where
  program := A.program
  realizes p := A.encodes p.1 p.2.property p.2.val

theorem sourceEncoder_budget_poly (F : BinaryFamily) {onset : ℕ} (A : EfficientEncoder F onset) :
    ∃ K e : ℕ, ∀ p : SourceMessage onset,
      sourceEncoderBudget F A p ≤ K * ((sourceMessageWord p).length + 1) ^ e := by
  refine ⟨A.coefficient, A.exponent, fun p => ?_⟩
  simp [sourceEncoderBudget, sourceMessageWord]

/-- Paid rewind is available before ordinary source calls are composed. -/
def sourceEncoderRewound (F : BinaryFamily) {onset : ℕ} (A : EfficientEncoder F onset) :
    RewoundWordFunction (SourceMessage onset) sourceMessageWord
      (fun p => List.ofFn (F.encode p.1 p.2.val)) (fun p => 2 * sourceEncoderBudget F A p + 2) :=
  (sourceEncoderWordFunction F A).reset

/-- A proof-indexed source request; the true message is not in the input word.
The promised decoder must recover it from the received word alone. -/
structure SourceDecodingRequest (F : BinaryFamily) (onset : ℕ) (radius : ℝ) where
  length : ℕ
  message : BitInput length
  received : BitInput (F.length length)
  large : onset ≤ length
  near : relativeHamming (F.encode length message) received ≤ radius

def sourceDecodingWord (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (p : SourceDecodingRequest F onset radius) : List Bool := decoderInput F p.length p.received

def sourceDecoderBudget (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (p : SourceDecodingRequest F onset radius) : ℕ :=
  D.coefficient * (p.length + F.length p.length + 1) ^ D.exponent

/-- This carrier is only on promised requests; it does not discharge the total
target decoder's algorithm condition. -/
def sourceDecoderWordFunction (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) :
    WordFunction (SourceDecodingRequest F onset radius) (sourceDecodingWord F)
      (fun p => List.ofFn p.message) (sourceDecoderBudget F D) where
  program := D.program
  realizes p := D.decodes p.length p.large p.message p.received p.near

theorem sourceDecodingWord_length (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (p : SourceDecodingRequest F onset radius) :
    (sourceDecodingWord F p).length = p.length + F.length p.length + 1 := by
  simp [sourceDecodingWord, decoderInput]
  omega

theorem sourceDecoder_budget_poly (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) :
    ∃ K e : ℕ, ∀ p : SourceDecodingRequest F onset radius,
      sourceDecoderBudget F D p ≤ K * ((sourceDecodingWord F p).length + 1) ^ e := by
  refine ⟨D.coefficient, D.exponent, fun p => ?_⟩
  rw [sourceDecodingWord_length]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem ofFn_joinWord {a b : ℕ} (x : BitInput a) (y : BitInput b) :
    List.ofFn (joinWord x y) = List.ofFn x ++ List.ofFn y :=
  List.ofFn_fin_append x y

theorem ofFn_joinMessage (n : ℕ) (x0 : BitInput (blockSize n 0))
    (x1 : BitInput (blockSize n 1)) (x2 : BitInput (blockSize n 2)) :
    List.ofFn (joinMessage n x0 x1 x2) = List.ofFn x0 ++ List.ofFn x1 ++ List.ofFn x2 := by
  change List.ofFn (fun i => joinWord (joinWord x0 x1) x2 (Fin.cast (blockSize_sum n).symm i)) = _
  rw [← List.ofFn_congr (blockSize_sum n), ofFn_joinWord, ofFn_joinWord]

theorem threeBlock_encoder_word (F : BinaryFamily) (n : ℕ) (x : BitInput n) :
    List.ofFn ((threeBlock F).encode n x) =
      List.ofFn (F.encode (blockSize n 0) (x ∘ firstIndex n)) ++
      List.ofFn (F.encode (blockSize n 1) (x ∘ secondIndex n)) ++
      List.ofFn (F.encode (blockSize n 2) (x ∘ thirdIndex n)) := by
  change List.ofFn (joinWord (joinWord _ _) _) = _
  rw [ofFn_joinWord, ofFn_joinWord]

theorem threeBlock_decoder_word (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (n : ℕ) (y : BitInput ((threeBlock F).length n)) :
    List.ofFn (threeDecoder F D n y) =
      List.ofFn (totalDecoder F D (blockSize n 0) (y ∘ firstOutputIndex F n)) ++
      List.ofFn (totalDecoder F D (blockSize n 1) (y ∘ secondOutputIndex F n)) ++
      List.ofFn (totalDecoder F D (blockSize n 2) (y ∘ thirdOutputIndex F n)) :=
  ofFn_joinMessage n _ _ _

theorem messageWord_length (p : MessageRequest) :
    (messageWord p).length = 2 * p.1.bits.length + 2 * p.1 + 2 := by
  simp only [messageWord, List.length_append, frame_length, List.length_ofFn]
  omega

theorem message_length_le_word (p : MessageRequest) : p.1 ≤ (messageWord p).length := by
  rw [messageWord_length]
  omega

theorem codewordWord_length (E : LinearCodeFamily) (p : CodewordRequest E) :
    (codewordWord E p).length = 2 * p.1.bits.length + 2 * E.length p.1 + 2 := by
  simp only [codewordWord, List.length_append, frame_length, List.length_ofFn]
  omega

/-- The source-block computation agrees exactly with the support-defined
target encoder; building supports is not part of its execution. -/
theorem patched_encoder_word_large (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (hlinear : IsLinear F)
    (n : ℕ) (hn : cutoff onset ≤ n) (x : BitInput n) :
    List.ofFn ((patchedFamily F D).enc n x) =
      List.ofFn (F.encode (blockSize n 0) (x ∘ firstIndex n)) ++
      List.ofFn (F.encode (blockSize n 1) (x ∘ secondIndex n)) ++
      List.ofFn (F.encode (blockSize n 2) (x ∘ thirdIndex n)) := by
  change List.ofFn ((patchedAt F D n).encode x) = _
  rw [patchedAt, if_pos hn]
  change List.ofFn (fun j => NearCubicWires.SourceInterfaces.parityOn (sourceSupport (threeBlock F) n j) x) = _
  simp only [← sourceSupport_enc (threeBlock F) (threeBlock_linear F hlinear)]
  exact threeBlock_encoder_word F n x

theorem patched_encoder_word_small (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (n : ℕ) (hn : n < cutoff onset) (x : BitInput n) :
    List.ofFn ((patchedFamily F D).enc n x) = List.ofFn x := by
  change List.ofFn ((patchedAt F D n).encode x) = _
  rw [patchedAt, if_neg (not_le_of_gt hn)]
  change List.ofFn (fun j => NearCubicWires.SourceInterfaces.parityOn {j} x) = _
  simp [NearCubicWires.SourceInterfaces.parityOn]

theorem codeword_message_length_le (F : BinaryFamily) (onset : ℕ) (distance radius : ℝ)
    (D : PromisedDecoder F onset radius) (hd : 0 < distance)
    (hmin : MinimumDistance F onset distance) (p : CodewordRequest (patchedFamily F D)) :
    p.1 ≤ (codewordWord (patchedFamily F D) p).length := by
  have h := patched_length_lower F onset distance radius D hd hmin p.1
  rw [codewordWord_length]
  omega

/-- Each source call's unary clock is polynomial in the entire message length. -/
theorem source_encoder_block_clock (F : BinaryFamily) {onset : ℕ}
    (A : EfficientEncoder F onset) (n : ℕ) (i : Fin 3) :
    A.coefficient * (blockSize n i + 1) ^ A.exponent ≤ A.coefficient * (n + 1) ^ A.exponent := by
  have hb : blockSize n i ≤ n := by
    have h := (blockSize_bounds n i).2
    omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem source_decoder_block_clock (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (rate : ℕ)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k)
    (n : ℕ) (hn : cutoff onset ≤ n) (i : Fin 3) :
    D.coefficient * (blockSize n i + F.length (blockSize n i) + 1) ^ D.exponent ≤
      (D.coefficient * (rate + 2) ^ D.exponent) * (n + 1) ^ D.exponent := by
  have hb : blockSize n i ≤ n := by
    have h := (blockSize_bounds n i).2
    omega
  have hrate' := hrate _ (blockSize_large onset n hn i).1
  have hrn := Nat.mul_le_mul_left rate hb
  have hbase : blockSize n i + F.length (blockSize n i) + 1 ≤ (rate + 2) * (n + 1) := by
    nlinarith
  have h := Nat.mul_le_mul_left D.coefficient (Nat.pow_le_pow_left hbase D.exponent)
  simpa only [Nat.mul_pow, Nat.mul_assoc] using h

end NearCubicGates.Adapters.Code
