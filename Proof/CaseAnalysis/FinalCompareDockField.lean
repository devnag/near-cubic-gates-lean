import Proof.CaseAnalysis.FinalCompareDockLit
import Proof.PCP.ProjectionNormalizationField

/-! **Decision tail, stage 2a-ii — lift one field out of a record word.**

`Realizes.hencoded` pins the worker's output as ONE record word,
`recordWord W est 1 1 = frame(pos) ++ frame(neg) ++ frame(den) ++ …`. The
comparator reads `pos`, `neg`, `den` as SEPARATE tapes. `Field.copy_run` copies
one framed field from a cursor on a source tape onto an output tape; with
`recordWord_split` the cursor for field `k` is computable. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockField

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorMonomialStream
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDock

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Field `k` of a record. -/
def field (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (k : Fin 6) :
    List Bool :=
  CloseoutRowsEstimatorCoefficients.Stream.recordFields b q count denominator k

/-- Field `k` in `copy_run`'s own shape: the source tape is `pre ++ frame bits ++ suffix`. -/
theorem field_step_split (pre bits suffix out : List Bool) :
    Step Field.machine (2*bits.length+1)
      ![pre.length, out.length] ![pre ++ frame bits ++ suffix, out]
      ![pre.length + 2*bits.length+1, (out ++ frame bits).length]
      ![pre ++ frame bits ++ suffix, out ++ frame bits] := by
  obtain ⟨r, hr, hfin, _hsteps⟩ := Field.copy_run pre bits suffix out
  refine Step.of_run (r := r) hr ?_ ?_
  · rw [hfin]; rfl
  · rw [hfin]; rfl

/-- **Copy field `k`** of the record on tape 0 (cursor at that field) onto tape 1. -/
theorem field_step (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ)
    (k : Fin 6) (out : List Bool) :
    Step Field.machine (2*(field b q count denominator k).length+1)
      ![fieldCursor b q count denominator k, out.length]
      ![CloseoutRowsEstimatorCoefficients.Stream.recordWord b q count denominator, out]
      ![fieldCursor b q count denominator k + 2*(field b q count denominator k).length+1,
        (out ++ frame (field b q count denominator k)).length]
      ![CloseoutRowsEstimatorCoefficients.Stream.recordWord b q count denominator,
        out ++ frame (field b q count denominator k)] := by
  have h := field_step_split
    (fieldStream (CloseoutRowsEstimatorCoefficients.Stream.recordFields b q count denominator)
      (allFields.take k.val))
    (CloseoutRowsEstimatorCoefficients.Stream.recordFields b q count denominator k)
    (fieldStream (CloseoutRowsEstimatorCoefficients.Stream.recordFields b q count denominator)
      (allFields.drop (k.val+1)))
    out
  rw [← recordWord_split b q count denominator k] at h
  exact h

end NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockField
