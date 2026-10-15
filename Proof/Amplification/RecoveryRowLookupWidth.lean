import Proof.Amplification.RecoveryRowLookupRewind

/-! Width retained by successful count lookups. Starting the saved-count tape
at the fixed width means it can feed the actual three-count carry checker
after every lookup without an uncharged padding operation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
open RecoveryRowLookupStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem advance_saved_length (x : Cursor) (hs : x.data.saved.length=x.data.row.width)
    (ha : (next x).1=true) : (advance x).data.saved.length=(advance x).data.row.width := by
  have hw : 4*x.data.row.width≤x.rest.length := by
    simpa only [next,RecoveryCertificateRow.row_isSome,decide_eq_true_eq] using ha
  rw [advance_width]
  change ((x.data.afterRead x.rest).cell (x.data.codeWord x.rest) (x.data.countWord x.rest)).done.saved.length=_
  rw [RecoveryRowLookupCell.done_saved]
  split
  · exact hs
  · split
    · exact RecoveryRowStream.words_length x.data.row.width x.rest 2 hw
    · exact hs

theorem iterate_saved_length (total : Nat) (x : Cursor) (hs : x.data.saved.length=x.data.row.width)
    (ha : (RepeatMachine.iterate next total x).1=true) :
    (RepeatMachine.iterate next total x).2.data.saved.length=(RepeatMachine.iterate next total x).2.data.row.width := by
  induction total generalizing x with
  | zero => exact hs
  | succ total ih =>
    cases hh : (next x).1 with
    | false => simp [RepeatMachine.iterate,hh] at ha
    | true =>
      simp only [RepeatMachine.iterate,hh,↓reduceIte] at ha ⊢
      exact ih (next x).2 (advance_saved_length x hs hh) ha

theorem output_saved_length (total : Nat) (d : Data) (bits : List Bool)
    (hs : d.saved.length=d.row.width) (ha : (readMany (readRow d.row.width) total bits).isSome=true) :
    (output total d bits).saved.length=d.row.width := by
  have hiter : (RepeatMachine.iterate next total ⟨clean d,bits⟩).1=true := by rw [iterate_accepts]; exact ha
  have h := iterate_saved_length total ⟨clean d,bits⟩ hs hiter
  exact h.trans (iterate_retained total ⟨clean d,bits⟩).1

end NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
