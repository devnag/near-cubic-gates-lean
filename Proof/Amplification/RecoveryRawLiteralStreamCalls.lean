import Proof.Amplification.RecoveryRawLiteralStreamState

/-! Both stream callees execute on their fixed disjoint banks. The witness
cursor and physical width driver are retained through literal decoding. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_run (x : State) (hx : x.data.data.Valid) :
    ∃ r,runFrom literalMachine (RecoveryRawLiteral.cost x.data) (x.cfg literalMachine.start)=some r ∧
      r.final=(decoded x).cfg r.final.control ∧ r.steps ≤ RecoveryRawLiteral.cost x.data := by
  obtain ⟨base,hr,hf,hb,_⟩ := RecoveryRawLiteral.literal_run x.data hx
  obtain ⟨r,h,hs,hfinal⟩ := RecoveryBankPair.left_run RecoveryRawLiteral.machine (RecoveryRawLiteral.cost x.data)
    (x.data.cfg RecoveryRawLiteral.machine.start) base hr x.extraHeads x.extra
  refine ⟨r,h,?_,hs.le.trans hb⟩
  apply configuration_ext
  · rfl
  · rw [hfinal,hf]
    rfl
  · rw [hfinal,hf]
    change Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool)
      (RecoveryRawLiteral.output x.data).tapes x.extra=
      Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool) (decoded x).data.tapes (decoded x).extra
    rw [decoded_extra]
    rfl

theorem skip_run (x : State) :
    ∃ r,runFrom skipMachine (3*(2*x.width)+2) ((decoded x).cfg skipMachine.start)=some r ∧
      r.final=(skipped x).cfg r.final.control ∧ r.steps=3*(2*x.width)+2 := by
  obtain ⟨base,hr,hf,hb⟩ := LookupWalk.walk_run .right x.source x.pos (2*x.width)
  have hpos : LookupWalk.shift .right x.pos (2*(2*x.width))=x.pos+4*x.width := by
    change x.pos+2*(2*x.width)=x.pos+4*x.width
    omega
  rw [hpos] at hf
  obtain ⟨r,h,hs,hfinal⟩ := RecoveryBankPair.right_run (LookupWalk.machine .right) (3*(2*x.width)+2)
    (LookupWalk.cfg 0 x.source x.pos (2*x.width) 1) base hr (fun _ : Fin 29=>0) (decoded x).data.tapes
  have hi : RecoveryBankPair.cfg (fun _ : Fin 29=>0) (decoded x).data.tapes
      (LookupWalk.cfg 0 x.source x.pos (2*x.width) 1).heads
      (LookupWalk.cfg 0 x.source x.pos (2*x.width) 1).tapes
      (LookupWalk.cfg 0 x.source x.pos (2*x.width) 1).control=(decoded x).cfg skipMachine.start := by
    unfold State.cfg State.extra State.extraHeads
    rw [decoded_width]
    rfl
  rw [hi] at h
  refine ⟨r,h,?_,hs.trans hb⟩
  apply configuration_ext
  · rfl
  · rw [hfinal,hf]
    rfl
  · rw [hfinal,hf]
    change Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool) (decoded x).data.tapes
      ![x.source,CompareMachine.word (2*x.width)]=
      Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool) (skipped x).data.tapes (skipped x).extra
    unfold State.extra
    change Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool) (decoded x).data.tapes
      ![x.source,CompareMachine.word (2*x.width)]=
      Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool) (decoded x).data.tapes
      ![x.source,CompareMachine.word (2*(decoded x).width)]
    rw [decoded_width]

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralStream
