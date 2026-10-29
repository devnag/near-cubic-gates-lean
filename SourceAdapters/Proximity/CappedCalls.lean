import SourceAdapters.Code.ResultParsing
import NineInputs

/-!
Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": conditional dock for the shared X8 capped caller.
Each source algorithm's own proved polynomial budget is a successful cap.
The paid X8/result-parser combination returns its exact raw output with the
framing required for another ordinary call. Constructing the unary cap from
the original source input word remains an explicit hypothesis on the caller.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity

/-- The request contains the paid unary clock, not only a binary integer. -/
def sourceCapRequest {Request : Type} (input : Request → List Bool) (budget : Request → ℕ)
    (r : Request) : CappedRequest := (budget r, input r)

theorem source_cap_output {Request : Type} {input output : Request → List Bool}
    {budget : Request → ℕ} (W : WordFunction Request input output budget) (r : Request) :
    cappedOutput W.program (sourceCapRequest input budget r) = output r := by
  obtain ⟨receipt, hr, ho⟩ := W.realizes r
  simp only [cappedOutput, sourceCapRequest, hr]
  exact ho

/-- Exact source dock: X8 and the shared paid parser frame an actual source output. -/
theorem source_capped_wordFunction (hX8 : CappedWordRun) {Request : Type}
    {input output : Request → List Bool} {budget : Request → ℕ}
    (W : WordFunction Request input output budget) :
    ∃ C : ℕ, Nonempty (WordFunction Request
      (fun r => cappedRequestWord (sourceCapRequest input budget r))
      (fun r => frame (output r)) (fun r => C * (budget r + (input r).length + 1))) := by
  obtain ⟨C, ⟨caller⟩⟩ := Parsing.framedCapped_of_X8 hX8 W.program
  refine ⟨C, ⟨{ program := caller.program, realizes := ?_ }⟩⟩
  intro r
  obtain ⟨receipt, hr, ho⟩ := caller.realizes (sourceCapRequest input budget r)
  refine ⟨receipt, hr, ?_⟩
  rw [source_cap_output W] at ho
  exact ho

theorem sourceCapRequest_length {Request : Type} (input : Request → List Bool)
    (budget : Request → ℕ) (r : Request) :
    (cappedRequestWord (sourceCapRequest input budget r)).length =
      2 * budget r + 2 * (input r).length + 2 := by
  simp only [cappedRequestWord, sourceCapRequest, List.length_append, frame_length, List.length_replicate]
  omega

/-- The serialized cap has polynomial length in the original source request. -/
theorem sourceCapRequest_polynomial {Request : Type} (input : Request → List Bool) (K e : ℕ) :
    ∀ r, (cappedRequestWord (sourceCapRequest input
      (fun r => K * ((input r).length + 1) ^ e) r)).length ≤
        (2 * K + 2) * ((input r).length + 1) ^ max e 1 := by
  intro r
  rw [sourceCapRequest_length]
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (input r).length + 1) (le_max_left e 1)
  have hl : (input r).length + 1 ≤ ((input r).length + 1) ^ max e 1 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (input r).length + 1) (le_max_right e 1)
  have hb := Nat.mul_le_mul_left K hp
  nlinarith

/-- Polynomial framed source output, on the explicitly cap-prepared encoding.
This conclusion does not claim that the request loader has been implemented. -/
theorem source_capped_polytime (hX8 : CappedWordRun) {Request : Type}
    (input output : Request → List Bool) (source : SourcePolyTime input output) :
    ∃ K e : ℕ, SourcePolyTime
      (fun r => cappedRequestWord (sourceCapRequest input (fun r => K * ((input r).length + 1) ^ e) r))
      (fun r => frame (output r)) := by
  obtain ⟨K, e, ⟨W⟩⟩ := source
  obtain ⟨C, ⟨caller⟩⟩ := source_capped_wordFunction hX8 W
  refine ⟨K, e, C, 1, ⟨caller.enlargeBudget (fun r => ?_)⟩⟩
  apply Nat.mul_le_mul_left
  rw [sourceCapRequest_length, pow_one]
  omega

end NearCubicGates.Adapters.Proximity
