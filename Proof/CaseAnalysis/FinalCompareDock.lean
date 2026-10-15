import Proof.CaseAnalysis.RowsEstimatorCoefficientsPrepare
import Proof.Hierarchy.CompetitorMonomialFields
import Proof.MachineModel.ClockNormalize
import Proof.MachineModel.ClockScalarFields
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Supplier.RowFieldPadding

/-! **Decision tail, stage 1 — the two facts the docking rests on.**

Paper C.10 (~4103): the machine passes validity only if the first estimated
average is at most `2*zeta` and every second moment at most `1+zeta`, and
accepts only if `mu~ >= theta_acc` (C.10.1). The physical comparators already
exist (`validity_mean_run`, `validity_moment_run`, `midpoint_run`); they read
their operands as SEPARATE framed binary words. The worker delivers each phase's
estimate as ONE record word. Two facts bridge them:

1. `recordWord_split` -- a record word is its six framed fields in order, so
   field `k` sits at a computable cursor and `Field.copy_run` can lift it out.
2. `frame_resize_binary` -- `ClockNormalize` widens a `binary` word exactly, so
   the record's `width W` operands become the comparator's `width (width W)`
   operands with no new stage.

Nothing here touches a tape; it is what makes the tape work in stage 2 routine. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10CompareDock

open NearCubicWires.RepairOrdinary
open CompetitorMonomialStream ClockNormalize ClockScalarFields SignedSortKey

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `fieldStream` over a concatenation is the concatenation of streams. -/
theorem fieldStream_append (fields : Fin 6 → List Bool) (js ks : List (Fin 6)) :
    fieldStream fields (js ++ ks) = fieldStream fields js ++ fieldStream fields ks := by
  simp [fieldStream, List.flatMap_append]

/-- **A record word splits at any field.** Field `k` is preceded by exactly the
stream of fields `0..k-1` and followed by that of `k+1..5`. -/
theorem recordWord_split (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ)
    (k : Fin 6) :
    CloseoutRowsEstimatorCoefficients.Stream.recordWord b q count denominator =
      fieldStream (CloseoutRowsEstimatorCoefficients.Stream.recordFields b q count denominator) (allFields.take k.val) ++
      frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b q count denominator k) ++
      fieldStream (CloseoutRowsEstimatorCoefficients.Stream.recordFields b q count denominator) (allFields.drop (k.val+1)) := by
  unfold CloseoutRowsEstimatorCoefficients.Stream.recordWord
  fin_cases k <;> simp [allFields, fieldStream]

/-- The cursor at which field `k` begins. -/
def fieldCursor (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ)
    (k : Fin 6) : ℕ :=
  (fieldStream (CloseoutRowsEstimatorCoefficients.Stream.recordFields b q count denominator) (allFields.take k.val)).length

/-- **Widening is exact.** For `p < 2^W` and `W ≤ w`, resizing the `W`-bit word
of `p` to `w` bits gives the `w`-bit word of `p`. This is what lets one
`normalize_run` feed the comparator from the record. -/
theorem resize_binary_widen (W w p : ℕ) (hp : p < 2^W) (hw : W ≤ w) :
    resize w (binary W p) = binary w p := by
  have hlen : (binary W p).length ≤ w := by
    rw [binary_length]; exact hw
  rw [resize_binary w _ hlen, binary_value W p hp]

/-- The framed form, as `normalize_run` leaves it on tape 2. -/
theorem frame_resize_binary (W w p : ℕ) (hp : p < 2^W) (hw : W ≤ w) :
    frame (resize w (binary W p)) = frame (binary w p) := by
  rw [resize_binary_widen W w p hp hw]

end NearCubicWires.RepairSource.CloseoutFinal.C10CompareDock
