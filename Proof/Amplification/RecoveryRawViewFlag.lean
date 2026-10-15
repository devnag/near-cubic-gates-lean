import Proof.Amplification.RecoveryRawViewCountRetained

/-! The raw-view body physically clears its acceptance bit before any
rejecting operation. Only the final clause checker can set it to true. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagged (x : State) (bit : Bool) : State :=
  {x with inner:={x.inner with stream:={x.inner.stream with
    data:={x.inner.stream.data with present:=bit}}}}

def flagMachine (bit : Bool) : Machine 65 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=28 then some bit else none,fun _=>.stay⟩ else none

theorem flagged_valid (x : State) (bit : Bool) (hx : x.Valid) : (flagged x bit).Valid := hx

theorem flagged_heads {s : Nat} (x : State) (bit : Bool) (q : Fin s) :
    ((flagged x bit).cfg q).heads=(x.cfg q).heads := by
  simp only [State.cfg,State.innerCfg,RecoveryBankPair.cfg,TapeEmbedding.config,
    RecoveryRawLiteralBound.State.cfg,RecoveryRawLiteralStream.State.cfg,
    RecoveryRawLiteralStream.State.extraHeads,flagged]

theorem flagged_tapes {s : Nat} (x : State) (bit : Bool) (q : Fin s) :
    ((flagged x bit).cfg q).tapes=Function.update (x.cfg q).tapes 28 [bit] := by
  have h29 : (flagged x bit).inner.stream.data.tapes=
      Function.update x.inner.stream.data.tapes 28 [bit] := by
    have he : (fun _ : Fin 1=>[bit])=Function.update (fun _ : Fin 1=>[x.inner.stream.data.present]) 0 [bit] := by
      funext i; fin_cases i; rfl
    change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool) x.inner.stream.data.data.tapes (fun _=>[bit])=_
    rw [he,bank_update_right]
    rfl
  have h31 : ((flagged x bit).inner.stream.cfg q).tapes=
      Function.update (x.inner.stream.cfg q).tapes 28 [bit] := by
    change Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool)
      (flagged x bit).inner.stream.data.tapes x.inner.stream.extra=_
    rw [h29,bank_update_left]
    rfl
  have h35 : ((flagged x bit).inner.cfg q).tapes=
      Function.update (x.inner.cfg q).tapes 28 [bit] := by
    change Fin.addCases (m:=31) (n:=4) (motive:=fun _=>List Bool)
      ((flagged x bit).inner.stream.cfg q).tapes x.inner.extra=_
    rw [h31,bank_update_left]
    rfl
  change Fin.addCases (m:=36) (n:=29) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      ((flagged x bit).inner.cfg q).tapes
      (fun _=>ZeroPadding.pad x.capacity (RepairSource.VerifierDecoding.CompareMachine.word x.count))) x.extra=_
  rw [h35,bank_update_left,bank_update_left]
  rfl

theorem flag_run (x : State) (bit : Bool) :
    ∃ r,runFrom (flagMachine bit) 1 (x.cfg 0)=some r ∧
      r.final=(flagged x bit).cfg 1 ∧ r.steps=1 := by
  have h : step (flagMachine bit) (x.cfg 0)=some ((flagged x bit).cfg 1) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · exact (flagged_heads x bit 1).symm
    · rw [flagged_tapes]
      funext i
      by_cases hi : i=28
      · subst i
        change writeTapeBit [x.inner.stream.data.present] 0 bit=[bit]
        rfl
      · simp only [applyAction,if_neg hi,Function.update_of_ne hi]
        rfl
  exact (Timed.single (by rfl) h).run (by rfl)

end NearCubicWires.RepairOrdinary.RecoveryRawView
