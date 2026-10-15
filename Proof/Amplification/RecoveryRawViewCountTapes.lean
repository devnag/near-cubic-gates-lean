import Proof.Amplification.RecoveryRawViewCopy

/-! The enclosing raw-view body reads its literal count at the actual
retained witness cursor and produces the very padded driver used by the
verified clause controller. Counter erasure is a separate paid predecessor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def counted (x : State) (n : Nat) : State :=
  {x with count:=n,inner:={x.inner with stream:={x.inner.stream with pos:=x.inner.stream.pos+2*n+2}}}

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem count_input (x : State) (word : List Bool) (k : Nat)
    (hz : x.count=0) (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    RecoveryFocus.config countSlots (x.cfg (0 : Fin 5)).heads (x.cfg (0 : Fin 5)).tapes
      (RecoveryCertificateCount.paddedCfg x.capacity 0 (frame word) (2*k) 0 x.limit 1)=x.cfg 0 := by
  apply focus_configuration countSlots countSlots_injective
  · rfl
  · intro j; fin_cases j
    · exact hp.symm
    · rfl
    · rfl
  · intro j; fin_cases j
    · change ZeroPadding.pad 0 (frame word)=x.inner.stream.source
      rw [ZeroPadding.pad_zero]
      exact hs.symm
    · change ZeroPadding.pad x.capacity (CompareMachine.word 0)=ZeroPadding.pad x.capacity (CompareMachine.word x.count)
      rw [hz]
    · exact ZeroPadding.pad_zero _
  · intro i _; rfl
  · intro i _; rfl

open RecoveryRowStructure

theorem counted_heads {s : Nat} (x : State) (n : Nat) (q : Fin s) :
    ((counted x n).cfg q).heads=Function.update (x.cfg q).heads 29 (x.inner.stream.pos+2*n+2) := by
  simp only [State.cfg,State.innerCfg,RecoveryBankPair.cfg,TapeEmbedding.config,
    RecoveryRawLiteralBound.State.cfg,RecoveryRawLiteralStream.State.cfg,
    RecoveryRawLiteralStream.State.extraHeads,counted]
  funext i
  fin_cases i <;> rfl

theorem counted_inner_tapes {s : Nat} (x : State) (n : Nat) (q : Fin s) :
    ((counted x n).inner.cfg q).tapes=(x.inner.cfg q).tapes := by
  simp only [RecoveryRawLiteralBound.State.cfg,TapeEmbedding.config,RecoveryRawLiteralStream.State.cfg,
    RecoveryBankPair.cfg,RecoveryRawLiteralStream.State.extra,counted]
  rfl

theorem counted_tapes {s : Nat} (x : State) (n : Nat) (q : Fin s) :
    ((counted x n).cfg q).tapes=Function.update (x.cfg q).tapes 35
      (ZeroPadding.pad x.capacity (CompareMachine.word n)) := by
  have hd : (fun _ : Fin 1=>ZeroPadding.pad x.capacity (CompareMachine.word n))=
      Function.update (fun _ : Fin 1=>ZeroPadding.pad x.capacity (CompareMachine.word x.count)) 0
        (ZeroPadding.pad x.capacity (CompareMachine.word n)) := by funext i; fin_cases i; rfl
  change Fin.addCases (m:=36) (n:=29) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool) ((counted x n).inner.cfg q).tapes
      (fun _=>ZeroPadding.pad x.capacity (CompareMachine.word n))) x.extra=_
  rw [counted_inner_tapes,hd,bank_update_right,bank_update_left]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawView
