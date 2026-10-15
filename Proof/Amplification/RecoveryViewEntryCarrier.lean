import Proof.Amplification.RecoveryViewSources

/-! Abstract-state transport of the cold prefix into the fixed bank avoids
unfolding its large finite controller during the initial-layout equality. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem embed_run {s : Nat} (p : Machine 32 s) (fuel : Nat) (a : Fin 32→List Bool)
    (base : ExecutionReceipt 32 s) (hb : run p fuel a=some base) :
    run (TapeEmbedding.machine 68 p) fuel (lift a)=
      some (TapeEmbedding.receipt (fun _ : Fin 68=>0) (fun _=>[]) base) := by
  have h := TapeEmbedding.run_embed p (fun _ : Fin 68=>0) (fun _=>[]) fuel _ base hb
  have hi : TapeEmbedding.config (fun _ : Fin 68=>0) (fun _=>[]) (initialConfiguration p a)=
      initialConfiguration (TapeEmbedding.machine 68 p) (lift a) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryColdView
