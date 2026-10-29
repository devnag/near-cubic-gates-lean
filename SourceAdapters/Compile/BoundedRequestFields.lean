import SourceAdapters.Compile.BoundedCNFBounds
import Proof.MachineModel.OrdinaryVerifierInputFields
import Proof.Foundations.OrdinaryFramedSource

/-!
proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`: the physical compiler reads the verifier code as
runtime input. This first ordinary stage copies the first three literal
framed request fields, retaining the fuel/high tail and advancing the actual
source cursor. The 12-state loader includes all rewinds and the transfer of the source.
-/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
  NearCubicWires.LocalBitMultitape
set_option autoImplicit false

def requestTail (r : CNFCompilationRequest) : List Bool :=
  RepairOrdinary.frame (List.replicate r.fuel true) ++ RepairOrdinary.frame r.high.bits

def requestFieldsBudget (r : CNFCompilationRequest) : ℕ :=
  VerifierInputFields.budget (VerifierEncoding.code r.verifier) r.input
    (List.replicate r.witnessLength true)

def requestFieldsCursor (r : CNFCompilationRequest) : ℕ :=
  (RepairOrdinary.frame (VerifierEncoding.code r.verifier)).length + (RepairOrdinary.frame r.input).length +
    (RepairOrdinary.frame (List.replicate r.witnessLength true)).length

def requestFieldsFinal (r : CNFCompilationRequest) : Configuration 7 12 :=
  VerifierFieldLoad.config 11 r.word (requestFieldsCursor r)
    (RepairOrdinary.frame (VerifierEncoding.code r.verifier)) (RepairOrdinary.frame r.input)
    (RepairOrdinary.frame (List.replicate r.witnessLength true))
    (RepairOrdinary.frame (VerifierEncoding.code r.verifier)).length (RepairOrdinary.frame r.input).length
    (RepairOrdinary.frame (List.replicate r.witnessLength true)).length

/-- Actual source transitions loading code/input/witness length; fuel/high
remain literally in the retained source, immediately after the final cursor. -/
theorem requestFields_run (r : CNFCompilationRequest) :
    ∃ receipt : ExecutionReceipt 7 12,
      run VerifierFieldLoad.machine (requestFieldsBudget r)
        (SourceHandoff.sourceTapes r.word) = some receipt ∧ receipt.final = requestFieldsFinal r := by
  have he : VerifierInputFields.source (VerifierEncoding.code r.verifier) r.input
      (List.replicate r.witnessLength true) (requestTail r) = r.word := by
    simp [VerifierInputFields.source, requestTail, CNFCompilationRequest.word, List.append_assoc]
  obtain ⟨receipt, hr, hf⟩ := VerifierInputFields.fields_run (VerifierEncoding.code r.verifier) r.input
    (List.replicate r.witnessLength true) (requestTail r)
  rw [he] at hr hf
  exact ⟨receipt, hr, hf⟩

theorem requestWord_length (r : CNFCompilationRequest) : r.word.length ≤ 2*r.measure+3 := by
  have hbits : r.high.bits.length ≤ natBitLength r.high := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    simpa [natBitLength, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (b := 2) (by omega) r.high)
  simp only [CNFCompilationRequest.word, List.length_append, frame_length,
    List.length_replicate, CNFCompilationRequest.measure]
  omega

theorem requestFieldsBudget_linear (r : CNFCompilationRequest) : requestFieldsBudget r ≤ 15*r.measure := by
  have hm := request_measure_positive r
  simp only [requestFieldsBudget, VerifierInputFields.budget, List.length_replicate,
    CNFCompilationRequest.measure] at *
  omega

/-- A concrete fixed ordinary WordFunction for the first loader stage.
This deliberately outputs only the extracted verifier code; it is not the
missing whole request-to-CNF generator. -/
def requestCodeWordFunction : WordFunction CNFCompilationRequest CNFCompilationRequest.word
    (fun r => RepairOrdinary.frame (VerifierEncoding.code r.verifier)) (fun r => 64*r.measure) :=
  (FramedSource.ofRaw (by decide : 0 < 7) VerifierFieldLoad.machine (1 : Fin 7)
    CNFCompilationRequest.word (fun r => RepairOrdinary.frame (VerifierEncoding.code r.verifier))
    requestFieldsBudget (by
      intro r
      obtain ⟨receipt, hr, hf⟩ := requestFields_run r
      exact ⟨receipt, hr, by rw [hf]; rfl⟩)).enlargeBudget (by
        intro r
        have hl := requestWord_length r
        have hb := requestFieldsBudget_linear r
        have hm := request_measure_positive r
        omega)

end NearCubicGates.Adapters.Compile
