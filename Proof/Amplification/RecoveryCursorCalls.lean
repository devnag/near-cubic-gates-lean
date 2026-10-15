import Proof.Amplification.RecoveryValuationRow
import Proof.Foundations.OrdinaryRewindCarrier

/-! Receipt composition with literal streaming head positions. Certificate
field readers leave the witness cursor advanced and their width driver at
head one; subsequent focused arithmetic preserves those physical heads. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem call_receipt {t k : Nat} (sizes : Fin k→Nat)
    (programs : (j : Fin k)→Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k)→Fin (sizes j)→(Fin t→Bool)→Option (Fin k))
    (j l : Fin k) (fuel : Nat) (source : Configuration t (sizes j))
    (receipt : ExecutionReceipt t (sizes j))
    (hr : runFrom (programs j) fuel source=some receipt)
    (hn : next j receipt.final.control receipt.final.scanned=some l) :
    ∃ n≤fuel+1,Timed (RecoveryCalls.machine sizes programs entry next) n
      (controlConfig (RecoveryCalls.code sizes j) source)
      (controlConfig (RecoveryCalls.code sizes l)
        (RecoveryCalls.restarted (programs l) receipt.final.heads receipt.final.tapes)) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel source receipt hr
  have hb := RecoveryCalls.body_timed sizes programs entry next j ⟨receipt.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs entry next j l receipt.final hh hn
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  have hs := runFrom_steps_le (programs j) fuel source receipt hr
  exact ⟨receipt.steps+1,by omega,h⟩

theorem stop_receipt {t k : Nat} (sizes : Fin k→Nat)
    (programs : (j : Fin k)→Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k)→Fin (sizes j)→(Fin t→Bool)→Option (Fin k))
    (j : Fin k) (fuel : Nat) (source : Configuration t (sizes j))
    (receipt : ExecutionReceipt t (sizes j))
    (hr : runFrom (programs j) fuel source=some receipt)
    (hn : next j receipt.final.control receipt.final.scanned=none) :
    ∃ n≤fuel+1,Timed (RecoveryCalls.machine sizes programs entry next) n
      (controlConfig (RecoveryCalls.code sizes j) source)
      (RecoveryCalls.stopped sizes receipt.final.heads receipt.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel source receipt hr
  have hb := RecoveryCalls.body_timed sizes programs entry next j ⟨receipt.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs entry next j receipt.final hh hn
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  have hs := runFrom_steps_le (programs j) fuel source receipt hr
  exact ⟨receipt.steps+1,by omega,h⟩

end NearCubicWires.RepairOrdinary.RecoveryRootRound
