import Proof.Hierarchy.CompetitorSameBucketGroupLayout
import Proof.Amplification.RecoveryFocusDock

/-! Pointwise projection of the existing grouping bank. This is the same
24-tape layout, with its long vector reduced once before ambient operations. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Store.tapeAt (s : Store) (cap w p m : ℕ) (source out : List Bool) (i : ℕ) : List Bool :=
  match i with
  | 0 => source
  | 1 => List.replicate w true
  | 2 => List.replicate p true
  | 3 => List.replicate m true
  | 4 => out
  | 5 => RepairSource.VerifierDecoding.CompareMachine.word p
  | 6 => RepairSource.VerifierDecoding.CompareMachine.word (2*m)
  | 7 => CompetitorSameBucketGroupArithmetic.field cap s.magnitude
  | 8 => CompetitorSameBucketGroupArithmetic.field cap s.ids
  | 9 => CompetitorSameBucketGroupArithmetic.field cap s.current
  | 10 => [s.sign]
  | 11 => [s.present]
  | 12 => [s.same]
  | 13 => CompetitorSameBucketGroupArithmetic.scalar cap w s.positive
  | 14 => CompetitorSameBucketGroupArithmetic.scalar cap w s.negative
  | 15 => CompetitorSameBucketGroupArithmetic.scalar cap w 0
  | 22 => List.replicate cap true
  | 23 => CompetitorSameBucketGroupArithmetic.zeros (cap+1)
  | _ => CompetitorSameBucketGroupArithmetic.zeros cap

theorem Store.tapes_at (s : Store) (cap w p m : ℕ) (source out : List Bool) (i : Fin 24) :
    s.tapes cap w p m source out i=s.tapeAt cap w p m source out i.val := by
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
