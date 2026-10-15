import Proof.Amplification.RecoveryTseitinNativeCircuitLoop

/-! The original node loop retains the output index and a blank physical
descriptor writer bank for its enclosing formula consumer. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Formula
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraData (output : Nat) : Fin 3→List Bool := ![List.replicate output true,[],[]]
noncomputable def state (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) :=
  TapeEmbedding.config (fun _ : Fin 3=>0) (extraData output)
    (Reuse.configuration phase n index pos word out cap total 1)
theorem old_heads (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) (i : Fin 1338) :
    (state phase n index pos word out cap total output).heads (i.castAdd 4)=Reuse.heads pos out.length i := by
  have he : i.castAdd 4=(i.castAdd 1).castAdd 3 := rfl
  rw [he]
  simp only [state,TapeEmbedding.config,Fin.addCases_left,Reuse.configuration,
    RepeatMachine.cfg,controlConfig,Reuse.entry]
theorem old_tapes (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) (i : Fin 1338) :
    (state phase n index pos word out cap total output).tapes (i.castAdd 4)=Reuse.data n index word out cap i := by
  have he : i.castAdd 4=(i.castAdd 1).castAdd 3 := rfl
  rw [he]
  simp only [state,TapeEmbedding.config,Fin.addCases_left,Reuse.configuration,
    RepeatMachine.cfg,controlConfig,Reuse.entry]
theorem extra_heads (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) (i : Fin 3) :
    (state phase n index pos word out cap total output).heads (i.natAdd 1339)=0 := by
  simp only [state,TapeEmbedding.config,Fin.addCases_right]
theorem extra_tapes (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) (i : Fin 3) :
    (state phase n index pos word out cap total output).tapes (i.natAdd 1339)=extraData output i := by
  simp only [state,TapeEmbedding.config,Fin.addCases_right]
theorem driver_head (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) :
    (state phase n index pos word out cap total output).heads 1338=1 := rfl
theorem driver_tape (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) :
    (state phase n index pos word out cap total output).tapes 1338=CompareMachine.word total := rfl

end NearCubicWires.RepairSource.RecoveryTseitinNative.Formula
