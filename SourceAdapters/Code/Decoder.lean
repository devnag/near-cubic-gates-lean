import SourceAdapters.Code.DecoderMachine

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": complete total ordinary decoder on the exact target
codeword serialization, with both preparation stages and all framing paid. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.Decoder

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Code NearCubicGates.PublishedSources.PCPP
open DecoderTypes DecoderBounds DecoderMachine

/-- The complete decoder on internal jobs. Every actual ordinary program is
constructed from the literal source algorithms and the shared capped-run join. -/
theorem jobWordFunction_of_source (hX8 : NearCubicGates.Adapters.Joins.CappedWordRun)
    (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (A : EfficientEncoder F onset) (distance : ℝ) (hd : 0 < distance) (hmin : MinimumDistance F onset distance) :
    ∃ K e : ℕ, Nonempty (WordFunction (Job F onset) (jobWord F) (jobOutput F D)
      (fun j => K * ((jobWord F j).length + 1) ^ e)) := by
  obtain ⟨CE, dE, WE⟩ := framed_encoder_wordFunction hX8 F A
  obtain ⟨CD, dD, WD⟩ := framed_decoder_wordFunction hX8 F D
  obtain ⟨WE⟩ := WE
  obtain ⟨WD⟩ := WD
  have hmessage : ∀ j : Job F onset, jobLength F j ≤ (jobBits F j).length :=
    message_le_bits F onset distance hd hmin
  let P : WordFunction (Job F onset) (jobWord F) (fun j => frame (firstInput F j))
      (fun j => LengthPreparation.budget (jobWord F j)) :=
    { program := LengthPreparation.wordFunction.program
      realizes := fun j => LengthPreparation.wordFunction.realizes (jobWord F j) }
  let Q := DecoderMachine.preparationWordFunction F onset CE dE WE hmessage
  let R := executionWordFunction F D CD dD WD hmessage
  let PQ := composeFramed P Q
  let U := composeFramed PQ R
  have hP : ∃ K e : ℕ, ∀ j : Job F onset,
      LengthPreparation.budget (jobWord F j) ≤ K * ((jobWord F j).length + 1) ^ e := by
    obtain ⟨K, e, h⟩ := LengthPreparation.budget_poly
    exact ⟨K, e, fun j => h (jobWord F j)⟩
  have hPQ := composeFramed_budget_poly (jobWord F (onset := onset)) _ _ hP
    (preparationBudget_poly F onset CE dE WE hmessage)
  obtain ⟨K, e, hU⟩ := composeFramed_budget_poly (jobWord F (onset := onset)) _ _ hPQ
    (executionBudget_poly F D CD dD WD hmessage)
  exact ⟨K, e, ⟨U.enlargeBudget hU⟩⟩

/-- The full ordinary decoder on `codewordWord`: all inputs terminate because
each source call is capped, and its output is explicitly normalized. -/
theorem wordFunction_of_source (hX8 : NearCubicGates.Adapters.Joins.CappedWordRun)
    (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (A : EfficientEncoder F onset) (distance : ℝ) (hd : 0 < distance) (hmin : MinimumDistance F onset distance) :
    ∃ K e : ℕ, Nonempty (WordFunction (CodewordRequest (patchedFamily F D)) (codewordWord (patchedFamily F D))
      (fun p => List.ofFn ((patchedFamily F D).decoder p.1 p.2.val))
      (fun p => K * ((codewordWord (patchedFamily F D) p).length + 1) ^ e)) := by
  obtain ⟨K, e, U⟩ := jobWordFunction_of_source hX8 F D A distance hd hmin
  obtain ⟨U⟩ := U
  refine ⟨K, e, ⟨{ program := U.program, realizes := ?_ }⟩⟩
  intro p
  obtain ⟨receipt, hr, ho⟩ := U.realizes (jobOf F D p)
  exact ⟨receipt, by simpa only [jobOf_word] using hr, by simpa only [jobOf_output] using ho⟩

end NearCubicGates.Adapters.Code.Decoder
