import Proof.CaseAnalysis.FinalSupplierRowInput
import Proof.MachineModel.NativeFamily

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.ThresholdCompiler
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowWriter

noncomputable section

section Writer
variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)
  (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
  (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
  (hpos : 1 ≤ w) (hload : 200 * (live.card + w * (live.card + 2)) ≤ s)

/-- The writer iterates once per hardwired live assignment: `2^K` rounds (`paper.tex:2870`). -/
theorem ps_length : (ps a live occ s harity P).length = 2 ^ live.card := by
  have h := bank_length a live occ s harity P
  rw [bank, ExtIncidence.NativeRowInput.bank, List.length_map] at h
  exact h

theorem ps_length_eq_bank_length :
    (ps a live occ s harity P).length = (bank a live occ s harity P).length := by
  rw [ps_length, bank_length]

/-- **The T_prep writer, instantiated.** `ExtIncidence.NativeFamily.family_run` at S3c-1's pool and
occurrence-index bank leaves exactly `CloseoutRowsEstimator.Header.stream (rowInput …)` appended to
the output tape, in `NativeFamily.budget (pool …) (live.card+1) w (ps …)` steps. -/
theorem writer_run (out pre tail : List Bool)
    (H : Fin 277 → ℕ) (A : Fin 277 → List Bool)
    (mh : ∀ j, H (ExtIncidence.NativeFanoutLayout.sources j) = 0)
    (ma : ∀ j, A (ExtIncidence.NativeFanoutLayout.sources j) =
      ExtIncidence.NativeMaster.words (pool a live occ s harity) (live.card + 1) w j) :
    ∃ actual,
      runFrom ExtIncidence.NativeFamily.machine
        (ExtIncidence.NativeFamily.budget (pool a live occ s harity) (live.card + 1) w
          (ps a live occ s harity P))
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0
          (ExtIncidence.NativeFamily.entry (pool a live occ s harity) (live.card + 1) w
            (ps a live occ s harity P) pre tail H A 0 out)
          (bank a live occ s harity P).length 1) = some actual ∧
      actual.final = RepairSource.VerifierDecoding.RepeatMachine.cfg 3
        (ExtIncidence.NativeFamily.entry (pool a live occ s harity) (live.card + 1) w
          (ps a live occ s harity P) pre tail H A (ps a live occ s harity P).length
          (out ++ CloseoutRowsEstimator.Header.stream
            (rowInput a live occ s harity P w hs hmon hpos hload)))
        (bank a live occ s harity P).length 1 ∧
      actual.steps ≤ ExtIncidence.NativeFamily.budget (pool a live occ s harity)
        (live.card + 1) w (ps a live occ s harity P) := by
  have hstream : CloseoutRowsEstimator.Header.stream
      (rowInput a live occ s harity P w hs hmon hpos hload) =
      (ps a live occ s harity P).flatMap
        (ExtIncidence.NativeFamily.emit (pool a live occ s harity) (live.card + 1) w) :=
    ExtIncidence.NativeRowInput.stream_eq s (live.card + 1) w (pool a live occ s harity)
      (ps a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
      (ps_rows_lt a live occ s harity P w hmon)
  rw [hstream, ← ps_length_eq_bank_length]
  exact ExtIncidence.NativeFamily.family_run (pool a live occ s harity) (live.card + 1) w
    (ps a live occ s harity P) out pre tail
    (ps_rows_lt a live occ s harity P w hmon) (Nat.succ_le_succ (Nat.zero_le _)) H A mh ma

/-- **`hC` of `WholeRetained.run`**: the header word of the supplier row fits the emitter's
declared output allowance (`ExtIncidence.NativeRowInput.stream_fits`). -/
theorem headerStream_le :
    (CloseoutRowsEstimator.Header.stream
        (rowInput a live occ s harity P w hs hmon hpos hload)).length ≤
      ExtIncidence.NativeOutputBound.allowance
        (ExtIncidence.NativeMeasured.capacity (pool a live occ s harity) (live.card + 1) w)
        (live.card + 1) (ps a live occ s harity P).length :=
  ExtIncidence.NativeRowInput.stream_fits s (live.card + 1) w (pool a live occ s harity)
    (ps a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
    (ps_rows_lt a live occ s harity P w hmon) (Nat.succ_le_succ (Nat.zero_le _))

/-- The same bound with the `2^K` row count made explicit (`paper.tex:2870`). -/
theorem headerStream_le_pow :
    (CloseoutRowsEstimator.Header.stream
        (rowInput a live occ s harity P w hs hmon hpos hload)).length ≤
      ExtIncidence.NativeOutputBound.allowance
        (ExtIncidence.NativeMeasured.capacity (pool a live occ s harity) (live.card + 1) w)
        (live.card + 1) (2 ^ live.card) := by
  have h := headerStream_le a live occ s harity P w hs hmon hpos hload
  rwa [ps_length] at h

end Writer

end

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowWriter
