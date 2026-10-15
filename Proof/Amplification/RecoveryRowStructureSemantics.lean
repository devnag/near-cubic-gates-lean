import Proof.Amplification.RecoveryRowLookupResult

/-! Literal structural-row ABI using first-match prior-row lookups and
bounded subtraction. These equations specify the executed branch checker;
checked prior rows make the first matching count sufficient. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open RepairSource.RecoveryOracle.BalancedCertificate RecoveryRowLookupTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countsCheck (parent left right : Nat) : Bool :=
  decide (left≤parent) && decide (right≤left) && parent-left==right &&
    (left-right==0 || left-right==1) && decide (0<right)

theorem countsCheck_eq (parent left right : Nat) :
    countsCheck parent left right=
      (parent==left+right && (left==right || left==right+1) && decide (0<right)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [countsCheck,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq]
  omega

def childrenCheck (prior : List Row) (row : Row) : Bool :=
  match lookupCount prior (Nat.unpair (Nat.unpair row.code).2).1,
      lookupCount prior (Nat.unpair (Nat.unpair row.code).2).2 with
  | some left,some right => (Nat.unpair row.code).1==2 && countsCheck row.count left right
  | _,_=>false

def check (prior : List Row) (row : Row) : Bool :=
  if row.kind=0 then row.code==0 && row.count==0
  else if row.kind=1 then Nat.unpair row.code==(1,row.payload) && row.count==1
  else if row.kind=2 then childrenCheck prior row else false

theorem childrenCheck_iff (prior : List Row) (row : Row) (hp : checkFrom [] prior=true) :
    childrenCheck prior row=true ↔ ∃ left∈prior,∃ right∈prior,
      (Nat.unpair row.code).1=2 ∧
      Nat.unpair (Nat.unpair row.code).2=(left.code,right.code) ∧
      row.count=left.count+right.count ∧
      (left.count=right.count ∨ left.count=right.count+1) ∧ 0<right.count := by
  constructor
  · intro h
    unfold childrenCheck at h
    split at h
    next lc rc hl hr =>
      obtain ⟨left,hlm,hlc,hln⟩ := lookupCount_sound _ _ _ hl
      obtain ⟨right,hrm,hrc,hrn⟩ := lookupCount_sound _ _ _ hr
      rw [countsCheck_eq] at h
      simp only [Bool.and_eq_true,beq_iff_eq,Bool.or_eq_true,decide_eq_true_eq] at h
      refine ⟨left,hlm,right,hrm,h.1,?_,?_,?_,?_⟩
      · exact Prod.ext hlc.symm hrc.symm
      · simpa only [hln,hrn] using h.2.1.1
      · simpa only [hln,hrn] using h.2.1.2
      · simpa only [hrn] using h.2.2
    next => contradiction
  · rintro ⟨left,hl,right,hr,htag,hpair,hcount,hbalance,hpositive⟩
    have hlc : left.code=(Nat.unpair (Nat.unpair row.code).2).1 := (congrArg Prod.fst hpair).symm
    have hrc : right.code=(Nat.unpair (Nat.unpair row.code).2).2 := (congrArg Prod.snd hpair).symm
    have hlook := (checked_lookup_iff prior hp _ left.count).mpr ⟨left,hl,hlc,rfl⟩
    have hrlook := (checked_lookup_iff prior hp _ right.count).mpr ⟨right,hr,hrc,rfl⟩
    simp only [childrenCheck,hlook,hrlook,countsCheck_eq]
    simp only [Bool.and_eq_true,beq_iff_eq,Bool.or_eq_true,decide_eq_true_eq]
    exact ⟨htag,⟨hcount,hbalance⟩,hpositive⟩

theorem check_eq (prior : List Row) (row : Row) (hp : checkFrom [] prior=true) :
    check prior row=unpairCheck prior row := by
  unfold check unpairCheck
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  apply Bool.eq_iff_iff.mpr
  rw [childrenCheck_iff prior row hp]
  simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,Bool.or_eq_true,decide_eq_true_eq,and_assoc]

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
