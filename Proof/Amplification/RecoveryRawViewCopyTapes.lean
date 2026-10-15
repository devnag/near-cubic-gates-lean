import Proof.Amplification.RecoveryRawViewOuter

/-! A paid framed copy hands the actual extracted clause code to the
retained inner checker. Both reset workspaces remain physically allocated. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copied_width (x : State) (bits : List Bool) (hw : bits.length=x.width) :
    (copied x bits).width=x.width := hw

theorem copied_capacity (x : State) (bits : List Bool) (hw : bits.length=x.width) :
    (copied x bits).capacity=x.capacity := by
  change 8192*(bits.length+1)^2=8192*(x.width+1)^2
  rw [hw]

theorem copied_valid (x : State) (bits : List Bool) (hx : x.Valid) (hw : bits.length=x.width) :
    (copied x bits).Valid := by
  have hc : RecoveryReusableUnpair.capacity bits=RecoveryReusableUnpair.capacity x.inner.stream.data.data.bits :=
    copied_capacity x bits hw
  refine ⟨⟨⟨?_,?_⟩,?_⟩,hx.2.1,?_,hx.2.2.2.1,?_⟩
  · intro i
    change (x.inner.stream.data.data.backing i).length ≤ RecoveryReusableUnpair.capacity bits
    rw [hc]
    exact hx.1.1.1 i
  · intro i
    change (x.inner.stream.data.data.fields i).length ≤ 2*bits.length+1
    rw [hw]
    exact hx.1.1.2 i
  · exact hx.1.2.trans hw.symm
  · exact hx.2.2.1.trans hw.symm
  · rw [copied_width x bits hw]
    exact hx.2.2.2.2

open RecoveryRowStructure

theorem replace_core_tapes (x : RecoveryClauseState.State) (bits : List Bool) (reset : Nat)
    (hc : RecoveryReusableUnpair.capacity bits=RecoveryReusableUnpair.capacity x.bits) :
    ({x with bits:=bits,capacity:=reset} : RecoveryClauseState.State).tapes=
      Function.update (Function.update x.tapes 0 (frame bits)) 22 (List.replicate reset false) := by
  funext i
  fin_cases i
  case «21»=>
    change List.replicate (RecoveryReusableUnpair.capacity bits) true=
      List.replicate (RecoveryReusableUnpair.capacity x.bits) true
    rw [hc]
  all_goals rfl

theorem reset_core_tapes (x : RecoveryClauseState.State) (reset : Nat) :
    ({x with capacity:=reset} : RecoveryClauseState.State).tapes=
      Function.update x.tapes 22 (List.replicate reset false) := by
  funext i
  fin_cases i <;> rfl

theorem copied_inner_tapes {s : Nat} (x : State) (bits : List Bool) (q : Fin s) (hw : bits.length=x.width) :
    ((copied x bits).innerCfg q).tapes=
      Function.update (Function.update (x.innerCfg q).tapes 0 (frame bits))
        22 (List.replicate (max x.inner.stream.data.data.capacity (4*bits.length+3)) false) := by
  let reset := max x.inner.stream.data.data.capacity (4*bits.length+3)
  have h28 := replace_core_tapes x.inner.stream.data.data bits reset (copied_capacity x bits hw)
  have h29 : (copied x bits).inner.stream.data.tapes=
      Function.update (Function.update x.inner.stream.data.tapes 0 (frame bits)) 22 (List.replicate reset false) := by
    change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
      ({x.inner.stream.data.data with bits:=bits,capacity:=reset} : RecoveryClauseState.State).tapes
      (fun _=>[x.inner.stream.data.present])=_
    rw [h28,bank_update_left,bank_update_left]
    rfl
  have he : (copied x bits).inner.stream.extra=x.inner.stream.extra := by
    change ![x.inner.stream.source,CompareMachine.word (2*bits.length)]=
      ![x.inner.stream.source,CompareMachine.word (2*x.width)]
    rw [hw]
  have h31 : ((copied x bits).inner.stream.cfg q).tapes=
      Function.update (Function.update (x.inner.stream.cfg q).tapes 0 (frame bits)) 22 (List.replicate reset false) := by
    change Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool)
      (copied x bits).inner.stream.data.tapes (copied x bits).inner.stream.extra=_
    rw [he,h29,bank_update_left,bank_update_left]
    rfl
  have h35 : ((copied x bits).inner.cfg q).tapes=
      Function.update (Function.update (x.inner.cfg q).tapes 0 (frame bits)) 22 (List.replicate reset false) := by
    change Fin.addCases (m:=31) (n:=4) (motive:=fun _=>List Bool)
      ((copied x bits).inner.stream.cfg q).tapes x.inner.extra=_
    rw [h31,bank_update_left,bank_update_left]
    rfl
  change Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
    ((copied x bits).inner.cfg q).tapes
    (fun _=>ZeroPadding.pad (copied x bits).capacity (CompareMachine.word x.count))=_
  rw [copied_capacity x bits hw,h35,bank_update_left,bank_update_left]
  rfl

theorem copied_extra (x : State) (bits : List Bool) :
    (copied x bits).extra=Function.update x.extra 22
      (List.replicate (max x.outer.capacity (2*bits.length+1)) false) := by
  change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
    ({x.outer with capacity:=max x.outer.capacity (2*bits.length+1)} : RecoveryClauseState.State).tapes
    (fun _=>CompareMachine.word x.limit)=_
  rw [reset_core_tapes,bank_update_left]
  rfl

theorem copied_tapes {s : Nat} (x : State) (bits : List Bool) (q : Fin s) (hw : bits.length=x.width) :
    ((copied x bits).cfg q).tapes=
      Function.update (Function.update (Function.update (x.cfg q).tapes
        58 (List.replicate (max x.outer.capacity (2*bits.length+1)) false)) 0 (frame bits))
        22 (List.replicate (max x.inner.stream.data.data.capacity (4*bits.length+3)) false) := by
  change Fin.addCases (m:=36) (n:=29) (motive:=fun _=>List Bool)
    ((copied x bits).innerCfg q).tapes (copied x bits).extra=_
  rw [copied_inner_tapes x bits q hw,copied_extra,bank_update_left,bank_update_left,bank_update_right]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawView
