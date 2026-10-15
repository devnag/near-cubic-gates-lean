import Proof.Amplification.RecoveryRowStructureSemantics
import Proof.MachineModel.OrdinaryAdd

/-! A fixed carry automaton checks the three binary row-count relations in
one pass. Both addition carries are retained in finite control; overflow is
rejected rather than hidden behind an input-fit premise. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowCounts
open RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev State := Fin 6→Bool
def initial : State := ![false,true,true,true,true,false]
def advance (s : State) (parent left right : Bool) : State :=
  ![Add.carry left right (s 0),s 1 && (parent==Add.bit left right (s 0)),
    s 2 && (left==right),Add.carry right false (s 3),
    s 4 && (left==Add.bit right false (s 3)),s 5 || right]
def finish (s : State) : Bool := s 1 && !(s 0) && (s 2 || (s 4 && !(s 3))) && s 5

def iterate : List Bool→List Bool→List Bool→State→State
  | p::ps,l::ls,r::rs,s => iterate ps ls rs (advance s p l r)
  | _,_,_,s=>s

def summary (parent left right : List Bool) (s : State) : State :=
  ![Add.overflow left right (s 0),s 1 && (parent==Add.sum left right (s 0)),
    s 2 && (left==right),Add.overflow right (List.replicate right.length false) (s 3),
    s 4 && (left==Add.sum right (List.replicate right.length false) (s 3)),s 5 || right.any id]

theorem iterate_eq (parent left right : List Bool) (s : State)
    (hl : parent.length=left.length) (hr : left.length=right.length) :
    iterate parent left right s=summary parent left right s := by
  induction parent generalizing left right s with
  | nil =>
    have hleft : left=[] := List.length_eq_zero_iff.mp hl.symm
    have hright : right=[] := List.length_eq_zero_iff.mp (hr.symm.trans hl.symm)
    subst left; subst right
    funext i
    fin_cases i <;> simp [iterate,summary,Add.overflow,Add.sum]
  | cons p ps ih =>
    cases left with
    | nil => simp at hl
    | cons l ls =>
      cases right with
      | nil => simp at hr
      | cons r rs =>
        rw [iterate,ih ls rs (advance s p l r) (by simpa using hl) (by simpa using hr)]
        funext i
        fin_cases i <;> simp [summary,advance,Add.overflow,Add.sum,List.replicate_succ,Bool.and_assoc,Bool.or_assoc]

theorem word_unique (left right : List Bool) (hl : left.length=right.length) (hv : value left=value right) :
    left=right := by
  have hleft := BoundedCounter.binary_of_value left
  have hright := BoundedCounter.binary_of_value right
  rw [hl,hv] at hleft
  exact hleft.symm.trans hright

theorem sum_eq_iff (out left right : List Bool) (carry : Bool)
    (hl : out.length=left.length) (hr : left.length=right.length) :
    (out=Add.sum left right carry ∧ Add.overflow left right carry=false) ↔
      value out=value left+value right+carry.toNat := by
  have hv := Add.sum_value left right carry hr
  have hlen := Add.sum_length left right carry hr
  constructor
  · rintro ⟨ho,hc⟩
    simpa only [ho,hc,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using hv
  · intro hn
    have hout := value_lt out
    have hsum := value_lt (Add.sum left right carry)
    rw [hlen] at hsum
    rw [hl] at hout
    have hc : Add.overflow left right carry=false := by
      cases he : Add.overflow left right carry with
      | false => rfl
      | true =>
        simp only [he,Bool.toNat_true,Nat.mul_one] at hv
        omega
    have he : value out=value (Add.sum left right carry) := by
      simp only [hc,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hv
      omega
    exact ⟨word_unique out (Add.sum left right carry) (hl.trans hlen.symm) he,hc⟩

theorem value_zero_iff (bits : List Bool) : bits.any id=false ↔ value bits=0 := by
  induction bits with
  | nil => simp [value]
  | cons bit bits ih => cases bit <;> simp [List.any_cons,value,ih]

theorem finish_iterate (parent left right : List Bool)
    (hl : parent.length=left.length) (hr : left.length=right.length) :
    finish (iterate parent left right initial)=
      (value parent==value left+value right &&
        (value left==value right || value left==value right+1) && decide (0<value right)) := by
  rw [iterate_eq parent left right initial hl hr]
  apply Bool.eq_iff_iff.mpr
  have hsum := sum_eq_iff parent left right false hl hr
  have hsucc := sum_eq_iff left right (List.replicate right.length false) true hr (by simp)
  have hzero : value (List.replicate right.length false)=0 := RecoveryRootIteration.zeros_value right.length
  have heq : left=right ↔ value left=value right := by
    constructor
    · exact congrArg value
    · exact word_unique left right hr
  have hnonzero : right.any id=true ↔ 0<value right := by
    rw [←Bool.not_eq_false, value_zero_iff]
    omega
  change ((((parent==Add.sum left right false) && !(Add.overflow left right false)) &&
    ((left==right) || ((left==Add.sum right (List.replicate right.length false) true) &&
      !(Add.overflow right (List.replicate right.length false) true)))) && right.any id)=true ↔ _
  simp only [Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,decide_eq_true_eq]
  simp only [Bool.toNat_false,Nat.add_zero] at hsum
  simp only [hzero,Bool.toNat_true,Nat.add_zero] at hsucc
  rw [hsum,hsucc,heq,hnonzero]

end NearCubicWires.RepairOrdinary.RecoveryRowCounts
