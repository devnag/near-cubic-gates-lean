import Proof.Amplification.RecoveryRawViewAccepted

/-! The raw-view entry reads the outer clause count into the very tape
used by its loop. Only the count cap and width workspaces remain prepared
inputs at this local boundary. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView RecoveryRowStructure
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advanced (x : State) (n : Nat) : State :=
  {x with inner:={x.inner with stream:={x.inner.stream with pos:=x.inner.stream.pos+2*n+2}}}
def countSlots : Fin 3→Fin 66 := ![29,65,64]
theorem countSlots_injective : Function.Injective countSlots := by decide
noncomputable def countMachine := RecoveryFocus.machine countSlots RecoveryCertificateCount.machine

theorem advanced_valid (x : State) (n : Nat) (hx : x.Valid) : (advanced x n).Valid := hx

theorem advanced_heads {s : Nat} (x : State) (n : Nat) (q : Fin s) :
    ((advanced x n).cfg q).heads=Function.update (x.cfg q).heads 29 (x.inner.stream.pos+2*n+2) := by
  have h := counted_heads x n q
  simp only [State.cfg,State.innerCfg,RecoveryBankPair.cfg,TapeEmbedding.config,
    RecoveryRawLiteralBound.State.cfg,RecoveryRawLiteralStream.State.cfg,
    RecoveryRawLiteralStream.State.extraHeads,counted,advanced] at h ⊢
  exact h

theorem advanced_tapes {s : Nat} (x : State) (n : Nat) (q : Fin s) :
    ((advanced x n).cfg q).tapes=(x.cfg q).tapes := by
  have h : ((advanced x n).inner.cfg q).tapes=(x.inner.cfg q).tapes := counted_inner_tapes x n q
  change Fin.addCases (m:=36) (n:=29) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool) ((advanced x n).inner.cfg q).tapes
      (fun _=>ZeroPadding.pad x.capacity (CompareMachine.word x.count))) x.extra=_
  rw [h]
  rfl

theorem counted_heads {s : Nat} (x : State) (n : Nat) (q : Fin s) :
    (RecoveryRawViewEnd.cfg (advanced x n) n q).heads=
      Function.update (RecoveryRawViewEnd.cfg x 0 q).heads 29 (x.inner.stream.pos+2*n+2) := by
  change Fin.addCases (m:=65) (n:=1) (motive:=fun _=>Nat) ((advanced x n).cfg q).heads (fun _=>1)=_
  rw [advanced_heads]
  funext i
  fin_cases i <;> rfl

theorem counted_tapes {s : Nat} (x : State) (n : Nat) (q : Fin s) :
    (RecoveryRawViewEnd.cfg (advanced x n) n q).tapes=
      Function.update (RecoveryRawViewEnd.cfg x 0 q).tapes 65 (CompareMachine.word n) := by
  have hd : (fun _ : Fin 1=>CompareMachine.word n)=
      Function.update (fun _ : Fin 1=>CompareMachine.word 0) 0 (CompareMachine.word n) := by
    funext i; fin_cases i; rfl
  change Fin.addCases (m:=65) (n:=1) (motive:=fun _=>List Bool) ((advanced x n).cfg q).tapes
    (fun _=>CompareMachine.word n)=_
  rw [advanced_tapes,hd,bank_update_right]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
