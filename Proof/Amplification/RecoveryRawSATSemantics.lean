import Proof.Amplification.RecoveryRawSATWhole

/-! The clause replay has one retained valuation parser and fixed prefix
parameters. Its outer list code is consumed by the actual cell machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def State.code (x : State) := value x.outer.bits
def clauseCheck (width cap committed count : Nat) (word : List Bool) (code : Nat) : Bool :=
  (readList cap (readEntry width) word).any (fun pair=>
    CompactCertificate.clausePredicate committed count pair.1 code)

def prefixCheck (P : Nat→Bool) : Nat→Nat→Bool
  | 0,_=>true
  | n+1,code=>decide (code≠0) && P (Nat.unpair (code-1)).1 &&
      prefixCheck P n (Nat.unpair (code-1)).2
def tailCode : Nat→Nat→Nat
  | 0,code=>code
  | n+1,code=>tailCode n (Nat.unpair (code-1)).2

structure Inv (width cap committed count : Nat) (word : List Bool) (x : State) : Prop where
  valid : x.Valid word
  width_eq : x.width=width
  cap_eq : x.valuation.cap=cap
  committed_eq : value x.valuation.committed=committed
  count_eq : value x.valuation.binaryCount=count

theorem leaf_answer (x : State) (word : List Bool) (hx : x.Valid word) (hz : x.code≠0) :
    leafAnswer x word=clauseCheck x.width x.valuation.cap (value x.valuation.committed)
      (value x.valuation.binaryCount) word (Nat.unpair (x.code-1)).1 := by
  have hw := head_width x word hx
  have hv := RecoveryCellStore.head_value x.outer.bits hz
  change value (headWord x)=(Nat.unpair (x.code-1)).1 at hv
  change (readList x.valuation.cap (readEntry (headWord x).length) word).any
    (fun pair=>CompactCertificate.clausePredicate (value x.valuation.committed)
      (value x.valuation.binaryCount) pair.1 (value (headWord x)))=_
  rw [hw,hv]
  rfl

theorem answer_inv (width cap committed count : Nat) (word : List Bool) (x : State)
    (hx : Inv width cap committed count word x) :
    answer x word=(decide (x.code≠0) &&
      clauseCheck width cap committed count word (Nat.unpair (x.code-1)).1) := by
  by_cases hz : x.code=0
  · change (decide (x.code≠0) && leafAnswer x word)=_
    simp only [hz,ne_eq,not_true_eq_false,decide_false,Bool.false_and]
  · rw [answer,leaf_answer x word hx.valid hz,hx.width_eq,hx.cap_eq,hx.committed_eq,hx.count_eq]
    rfl

theorem accepted_inv (width cap committed count : Nat) (word : List Bool) (x : State)
    (hx : Inv width cap committed count word x) (out : AcceptedResult x word) :
    Inv width cap committed count word out.data := by
  refine ⟨out.valid,out.width.trans hx.width_eq,out.cap.trans hx.cap_eq,?_,?_⟩
  · rw [out.committed]; exact hx.committed_eq
  · rw [out.count]; exact hx.count_eq

theorem accepted_code (x : State) (word : List Bool) (out : AcceptedResult x word)
    (ha : answer x word=true) : out.data.code=(Nat.unpair (x.code-1)).2 := by
  have hz : x.code≠0 := by
    have h := ha
    simp only [answer,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  change value out.data.outer.bits=_
  rw [out.outerBits,RecoveryThreeCellReader.after_value x.outer 0 hz]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawSAT
