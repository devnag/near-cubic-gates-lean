import SourceAdapters.Code.Algorithms
import SourceAdapters.Joins.CappedRun

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": consumer dock for the shared capped ordinary run.
The source leaf remains promise-only. The paid caller construction and the
framed-result parser are separate ordinary programs. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicGates.Adapters.Joins NearCubicGates.Published.CW19Code

/-- The exact bounded output; a failed run supplies the default empty word. -/
def cappedOutput (p : Program) (r : CappedRequest) : List Bool :=
  match run p.machine r.1 (p.inputTapes r.2) with
  | none => []
  | some receipt => receipt.final.tapes p.outputTape

theorem capped_result_payload (p : Program) (r : CappedRequest) :
    ∃ success : Bool, cappedResultWord p r = success :: frame (cappedOutput p r) := by
  cases hr : run p.machine r.1 (p.inputTapes r.2)
  · exact ⟨false, by simp [cappedResultWord, cappedOutput, hr]⟩
  · exact ⟨true, by simp [cappedResultWord, cappedOutput, hr]⟩

/-- This request is still in the capped simulator's encoding. The code
algorithm must construct it from the target message encoding. -/
def encoderCappedRequest (F : BinaryFamily) {onset : ℕ} (A : EfficientEncoder F onset)
    (p : SourceMessage onset) : CappedRequest :=
  (sourceEncoderBudget F A p, sourceMessageWord p)

theorem encoder_capped_result (F : BinaryFamily) {onset : ℕ} (A : EfficientEncoder F onset)
    (p : SourceMessage onset) :
    cappedResultWord A.program (encoderCappedRequest F A p) = true :: frame (List.ofFn (F.encode p.1 p.2.val)) := by
  obtain ⟨receipt, hr, ho⟩ := A.encodes p.1 p.2.property p.2.val
  simp [cappedResultWord, encoderCappedRequest, sourceEncoderBudget, sourceMessageWord, hr, ho]

theorem encoder_capped_output_length (F : BinaryFamily) {onset : ℕ} (A : EfficientEncoder F onset)
    (p : SourceMessage onset) :
    (cappedOutput A.program (encoderCappedRequest F A p)).length = F.length p.1 := by
  obtain ⟨receipt, hr, ho⟩ := A.encodes p.1 p.2.property p.2.val
  simp [cappedOutput, encoderCappedRequest, sourceEncoderBudget, sourceMessageWord, hr, ho]

/-- X8 supplies an actual capped encoder call, including the additional
output frame consumed by ordinary-program composition. -/
theorem encoder_capped_wordFunction (hX8 : CappedWordRun) (F : BinaryFamily) {onset : ℕ}
    (A : EfficientEncoder F onset) :
    ∃ C : ℕ, 1 ≤ C ∧ Nonempty (WordFunction (SourceMessage onset)
      (fun p => cappedRequestWord (encoderCappedRequest F A p))
      (fun p => frame (true :: frame (List.ofFn (F.encode p.1 p.2.val))))
      (fun p => C * (sourceEncoderBudget F A p + p.1 + 1))) := by
  obtain ⟨C, hC, W⟩ := hX8 A.program
  obtain ⟨W⟩ := W
  refine ⟨C, hC, ⟨{ program := W.program, realizes := ?_ }⟩⟩
  intro p
  obtain ⟨r, hr, ho⟩ := W.realizes (encoderCappedRequest F A p)
  refine ⟨r, ?_, ?_⟩
  · simpa [encoderCappedRequest, sourceMessageWord] using hr
  · rw [encoder_capped_result] at ho
    exact ho

abbrev TotalSourceRequest (F : BinaryFamily) := Σ n : ℕ, BitInput (F.length n)

def decoderCappedRequest (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (p : TotalSourceRequest F) : CappedRequest :=
  (D.coefficient * (p.1 + F.length p.1 + 1) ^ D.exponent, decoderInput F p.1 p.2)

/-- The exact mathematical totalization already used by the code family is
obtained by taking/padding the capped output to the requested message length. -/
theorem totalDecoder_capped_output (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (p : TotalSourceRequest F) :
    List.ofFn (totalDecoder F D p.1 p.2) =
      List.ofFn (fun i : Fin p.1 => (cappedOutput D.program (decoderCappedRequest F D p)).getD i.val false) := by
  unfold totalDecoder cappedOutput decoderCappedRequest
  split <;> simp_all [List.getD_eq_getElem?_getD]

/-- X8 runs on every received word, including words outside the source
promise. No decoder runtime hypothesis outside the promise is used. -/
theorem decoder_capped_wordFunction (hX8 : CappedWordRun) (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) :
    ∃ C : ℕ, 1 ≤ C ∧ Nonempty (WordFunction (TotalSourceRequest F)
      (fun p => cappedRequestWord (decoderCappedRequest F D p))
      (fun p => frame (cappedResultWord D.program (decoderCappedRequest F D p)))
      (fun p => C * (D.coefficient * (p.1 + F.length p.1 + 1) ^ D.exponent +
        (decoderInput F p.1 p.2).length + 1))) := by
  obtain ⟨C, hC, W⟩ := hX8 D.program
  obtain ⟨W⟩ := W
  exact ⟨C, hC, ⟨{ program := W.program, realizes := fun p => W.realizes (decoderCappedRequest F D p) }⟩⟩

end NearCubicGates.Adapters.Code
