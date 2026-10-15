import Proof.Amplification.RecoveryCompactState

/-! The existing produced witness length also bounds table broadcasts.
Logical zero padding after the copied suffix requires no suffix-length
producer. The checker reads only its actual capped row count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def buffer (table word : List Bool) := RecoveryColdPaddedCopy.data table word.length

theorem buffer_eq (table word : List Bool) (h : table.length≤word.length) :
    buffer table word=table++List.replicate (word.length-table.length) false :=
  RecoveryColdPaddedCopy.data_eq_pad table word.length h

theorem padded_at {t : Nat} (slot : Fin 4→Fin t) (hi : Function.Injective slot)
    (heads : Fin t→Nat) (ambient : Fin t→List Bool) (bits : List Bool) (width reset : Nat)
    (hin : ∀ j,ambient (slot j)=
      ![frame bits,[],CompareMachine.word width,List.replicate reset false] j)
    (hh : ∀ j,heads (slot j)=0) :
    AtRun (RecoveryFocus.machine slot RecoveryColdPaddedCopy.machine) (4*width+8) heads ambient
      (Function.update (Function.update ambient (slot 1)
        (frame (RecoveryColdPaddedCopy.data bits width))) (slot 3)
        (List.replicate (max reset (2*width+3)) false)) := by
  have h := AtRun.focus (padded_ready bits width reset) slot hi heads ambient hin hh
  rw [RecoveryColdHeader.install_pair slot hi ambient
    ![frame bits,frame (RecoveryColdPaddedCopy.data bits width),CompareMachine.word width,
      List.replicate (max reset (2*width+3)) false]
    (hin 0).symm (hin 2).symm] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
