import Proof.Amplification.RecoveryRowStructureChildrenRight

/-! Whole left-lookup tail, continuing through the right lookup and count
check only after the physical left-found flag succeeds. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftFound (x : Children) (left bits : List Bool) := bankOutput (bankKey x left) bits
def leftOutput (x : Children) (left right bits : List Bool) :=
  if (leftFound x left bits).bank.found then rightOutput (leftSaved (leftFound x left bits)) right bits
  else childrenRejected (leftFound x left bits)
def leftTime (x : Children) (left right : List Bool) :=
  (8*left.length+8)+1+bankTime x+1+(8*x.base.state.bits.length+8)+1+
    ((8*right.length+8)+1+bankTime x+1+(4*x.base.count.length+5))

theorem left_trace (x : Children) (left right word bits : List Bool) (padding : Nat) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hl : left.length=x.base.state.bits.length) (hr : right.length=x.base.state.bits.length)
    (hleft : x.tapes 17=ZeroPadding.pad padding (frame left)) (hright : x.base.state.fields 0=frame right)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest))
    (hcount : x.base.count.length=x.base.state.bits.length) :
    ∃ n≤leftTime x left right,Timed childrenMachine n (childrenCfg x 1) (childrenStop (leftOutput x left right bits)) ∧
      (leftOutput x left right bits).Valid word bits := by
  obtain ⟨copied,hr0,hf0,_,hv0⟩ := key_copy_run true x left word bits padding hx hl hleft
  obtain ⟨n0,hb0,h0⟩ := children_call 1 2 x (bankKey x left) (8*left.length+8) copied hr0 hf0 (by rfl)
  obtain ⟨looked,hr1,hf1,_,hv1,_,_⟩ := bank_run (bankKey x left) word bits rows rest hv0 hp
  cases ha : (leftFound x left bits).bank.found
  · obtain ⟨n1,hb1,h1⟩ := children_call 2 7 (bankKey x left) (leftFound x left bits) (bankTime x) looked hr1 hf1 (by
      rw [hf1]
      change (if (leftFound x left bits).bank.found then some (3 : Fin 8) else some 7)=some 7
      rw [ha]; rfl)
    obtain ⟨n2,hb2,h2⟩ := children_reject_tail (leftFound x left bits)
    refine ⟨n0+n1+n2,by unfold leftTime; omega,?_,?_⟩
    · simpa only [leftOutput,ha,Bool.false_eq_true,if_false] using (h0.trans h1).trans h2
    · simp only [leftOutput,ha,Bool.false_eq_true,if_false]
      exact hv1
  · obtain ⟨n1,hb1,h1⟩ := children_call 2 3 (bankKey x left) (leftFound x left bits) (bankTime x) looked hr1 hf1 (by
      rw [hf1]
      change (if (leftFound x left bits).bank.found then some (3 : Fin 8) else some 7)=some 3
      rw [ha]; rfl)
    obtain ⟨saved,hr2,hf2,_,hv2⟩ := save_count_run (leftFound x left bits) word bits hv1
    have hsaved : (leftFound x left bits).bank.saved.length=x.base.state.bits.length :=
      hv1.2.2.2.1.trans hv1.2.1.2.1
    have hsave : runFrom saveCountMachine (8*x.base.state.bits.length+8)
        ((leftFound x left bits).cfg saveCountMachine.start)=some saved := by simpa only [hsaved] using hr2
    obtain ⟨n2,hb2,h2⟩ := children_call 3 4 (leftFound x left bits) (leftSaved (leftFound x left bits))
      (8*x.base.state.bits.length+8) saved hsave hf2 (by rfl)
    have hwidth : (leftFound x left bits).bank.row.width=x.bank.row.width :=
      hv1.2.1.2.1.trans hx.2.1.2.1.symm
    have hparse : readMany (readRow (leftSaved (leftFound x left bits)).bank.row.width)
        (leftSaved (leftFound x left bits)).total bits=some (rows,rest) := by
      change readMany (readRow (leftFound x left bits).bank.row.width) x.total bits=some (rows,rest)
      rw [hwidth]
      exact hp
    obtain ⟨n3,hb3,h3,hv3⟩ := right_trace (leftSaved (leftFound x left bits)) right word bits rows rest hv2 hr hright hparse hcount hsaved
    have htime : rightTime (leftSaved (leftFound x left bits)) right=
        (8*right.length+8)+1+bankTime x+1+(4*x.base.count.length+5) := by
      change (8*right.length+8)+1+(2*x.total*(RecoveryRowLookupStream.budget (leftFound x left bits).bank.row.width+3)+12)+1+
        (4*x.base.count.length+5)=_
      rw [hwidth]
      rfl
    rw [htime] at hb3
    refine ⟨n0+n1+n2+n3,by unfold leftTime; omega,?_,?_⟩
    · simpa only [leftOutput,ha,if_true] using ((h0.trans h1).trans h2).trans h3
    · simpa only [leftOutput,ha,if_true] using hv3

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
