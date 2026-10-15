import Proof.Amplification.RecoveryRowStructureChildrenLeft

/-! The complete paired-row execution begins with the actual retained pair
word and its reusable second unpair, then follows both paid lookup tails. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def decodedChildren (x : Children) (pair : List Bool) : Children := {x with base:=decoded x.base pair}
def childrenOutput (x : Children) (pair bits : List Bool) :=
  leftOutput (decodedChildren x pair) (RecoveryFixedUnpair.leftWord pair) (RecoveryChildSelection.word false pair) bits
def childrenTime (x : Children) (pair : List Bool) :=
  RecoveryDecodeStep.time pair+1+
    leftTime (decodedChildren x pair) (RecoveryFixedUnpair.leftWord pair) (RecoveryChildSelection.word false pair)

theorem decodedChildren_valid (x : Children) (pair word bits : List Bool) (hx : x.Valid word bits)
    (hw : pair.length=x.base.state.bits.length) : (decodedChildren x pair).Valid word bits :=
  ⟨decoded_valid x.base pair word hx.1 hw,hx.2⟩

theorem children_trace (x : Children) (pair word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hw : pair.length=x.base.state.bits.length)
    (hsource : x.base.state.fields 0=frame pair)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest))
    (hcount : x.base.count.length=x.base.state.bits.length) :
    ∃ n≤childrenTime x pair,Timed childrenMachine n (x.cfg childrenMachine.start) (childrenStop (childrenOutput x pair bits)) ∧
      (childrenOutput x pair bits).Valid word bits := by
  change ∃ n≤childrenTime x pair,Timed childrenMachine n (childrenCfg x 0) (childrenStop (childrenOutput x pair bits)) ∧ _
  obtain ⟨base,hr0,hf0,_,_⟩ := decode_run x.base x.copyCapacity pair word hx.1 hw hsource
  obtain ⟨r,hr,hf,_⟩ := base_run decodeMachine x (decoded x.base pair) (RecoveryDecodeStep.time pair) base hr0 hf0
  obtain ⟨n0,hb0,h0⟩ := children_call 0 1 x (decodedChildren x pair) (RecoveryDecodeStep.time pair) r hr hf (by rfl)
  have hl : (RecoveryFixedUnpair.leftWord pair).length=(decodedChildren x pair).base.state.bits.length :=
    (RecoveryFixedUnpair.word_lengths pair).1.trans hw
  have hright : (RecoveryChildSelection.word false pair).length=(decodedChildren x pair).base.state.bits.length :=
    (RecoveryChildSelection.word_length false pair).trans hw
  have htape : (decodedChildren x pair).tapes 17=
      ZeroPadding.pad (RecoveryReusableUnpair.capacity pair) (frame (RecoveryFixedUnpair.leftWord pair)) := by
    have h := RecoveryLiteralDecode.output_tag x.base.state 0 pair
    rw [RecoveryLiteralDecode.decoded_output x.base.state 0 pair hw] at h
    exact h
  have hfield : (decodedChildren x pair).base.state.fields 0=frame (RecoveryChildSelection.word false pair) := by
    change (RecoveryLiteralDecode.decodedState x.base.state 0 pair).fields 0=_
    simp [RecoveryLiteralDecode.decodedState]
  obtain ⟨n1,hb1,h1,hv1⟩ := left_trace (decodedChildren x pair) (RecoveryFixedUnpair.leftWord pair)
    (RecoveryChildSelection.word false pair) word bits (RecoveryReusableUnpair.capacity pair) rows rest
    (decodedChildren_valid x pair word bits hx hw) hl hright htape hfield hp hcount
  exact ⟨n0+n1,by unfold childrenTime; omega,h0.trans h1,hv1⟩

theorem children_run (x : Children) (pair word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hw : pair.length=x.base.state.bits.length)
    (hsource : x.base.state.fields 0=frame pair)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest))
    (hcount : x.base.count.length=x.base.state.bits.length) :
    ∃ r,runFrom childrenMachine (childrenTime x pair) (x.cfg childrenMachine.start)=some r ∧
      r.final=(childrenOutput x pair bits).cfg r.final.control ∧ r.steps≤childrenTime x pair ∧
      (childrenOutput x pair bits).Valid word bits := by
  obtain ⟨n,hn,h,hv⟩ := children_trace x pair word bits rows rest hx hw hsource hp hcount
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [childrenMachine,childrenStop,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel childrenMachine n (childrenTime x pair-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,?_,hs.le.trans hn,hv⟩
  rw [hf]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
