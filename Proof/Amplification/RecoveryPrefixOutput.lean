import Proof.Amplification.RecoveryBoundedWordPrefix
import Proof.Amplification.RecoveryPrefixLoop
import Proof.PCP.ProjectionDimensionPower

/-! The existing bounded word copier removes the two high-sentinel bits by
an actual length-driven copy. Padding is retained on the source and is never
scanned beyond the requested prefix. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixOutput
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryBoundedTapeCopy ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copied_pad (word : List Bool) (cap n : Nat) :
    copied (ZeroPadding.pad cap word) n=copied word n := by
  unfold copied
  apply List.map_congr_left
  intro i _
  exact ZeroPadding.read_pad cap word i

theorem prefix_exact (xs : List Bool) (cap : Nat) :
    copied (ZeroPadding.pad cap (frame (xs++[false,true]))) (2*xs.length)++[false]=frame xs := by
  rw [copied_pad,RecoveryBoundedWordCopy.closed_frame]
  simp [ZeroPadding.pad]

theorem copy_ready (xs : List Bool) (cap log : Nat) :
    ClockJoin.ReadyRun RecoveryBoundedWordCopy.machine (4*xs.length+8)
      ![ZeroPadding.pad cap (frame (xs++[false,true])),[],List.replicate (2*xs.length) true,
        List.replicate log false]
      ![ZeroPadding.pad cap (frame (xs++[false,true])),frame xs,List.replicate (2*xs.length) true,
        List.replicate (max log (2*xs.length+3)) false] := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryBoundedWordCopy.copy_ready
    (ZeroPadding.pad cap (frame (xs++[false,true]))) (2*xs.length) log
  rw [prefix_exact] at ht
  rw [show 2*(2*xs.length)+8=4*xs.length+8 by omega] at hr hs
  exact ⟨r,hr,ht,hh,hs.le⟩

end NearCubicWires.RepairSource.RecoveryPrefixOutput
