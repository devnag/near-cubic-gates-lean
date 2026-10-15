import Proof.Amplification.RecoveryCompactSize

/-! Canonical balanced decoding has polynomial certificates whose local
rules inspect only unpair results and earlier rows. No re-encoding is part
of the checker. Encoding appears solely in this correctness proof. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.BalancedCertificate
open CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Row where
  kind : Nat
  code : Nat
  count : Nat
  payload : Nat
  deriving DecidableEq

def localCheck (prior : List Row) (row : Row) : Bool :=
  if row.kind=0 then row.code==0 && row.count==0
  else if row.kind=1 then Nat.unpair row.code==(1,row.payload) && row.count==1
  else if row.kind=2 then prior.any fun left => prior.any fun right =>
    Nat.unpair row.code==(2,Nat.pair left.code right.code) &&
      row.count==left.count+right.count &&
      (left.count==right.count || left.count==right.count+1) && 0<right.count
  else false

/-- A version of the branch check using only unpair and comparisons, rather
than pairing the two child codes. This is the literal arithmetic ABI. -/
def unpairCheck (prior : List Row) (row : Row) : Bool :=
  if row.kind=0 then row.code==0 && row.count==0
  else if row.kind=1 then Nat.unpair row.code==(1,row.payload) && row.count==1
  else if row.kind=2 then prior.any fun left => prior.any fun right =>
    (Nat.unpair row.code).1==2 &&
      Nat.unpair (Nat.unpair row.code).2==(left.code,right.code) &&
      row.count==left.count+right.count &&
      (left.count==right.count || left.count==right.count+1) && 0<right.count
  else false

theorem unpairCheck_eq (prior : List Row) (row : Row) : unpairCheck prior row=localCheck prior row := by
  unfold unpairCheck localCheck
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  congr 1
  funext left
  congr 1
  funext right
  have hp : Nat.unpair row.code=(2,Nat.pair left.code right.code) ↔
      (Nat.unpair row.code).1=2 ∧ Nat.unpair (Nat.unpair row.code).2=(left.code,right.code) := by
    constructor
    · intro h; simp [h]
    · rintro ⟨ht,hc⟩
      apply Prod.ext ht
      have h := congrArg (fun p : Nat×Nat => Nat.pair p.1 p.2) hc
      simpa using h
  apply Bool.eq_iff_iff.mpr
  simp [hp,and_assoc]

def checkFrom (prior : List Row) : List Row → Bool
  | [] => true
  | row::rest => unpairCheck prior row && checkFrom (prior++[row]) rest

def Meaning (row : Row) : Prop :=
  ∃ values : List Nat, encodeBalancedList values=row.code ∧ values.length=row.count

theorem encode_append (left right : List Nat)
    (hr : 0<right.length)
    (hb : left.length=right.length ∨ left.length=right.length+1) :
    encodeBalancedList (left++right)=Nat.pair 2 (Nat.pair (encodeBalancedList left) (encodeBalancedList right)) := by
  have hl : 0<left.length := by omega
  have hn : 2≤(left++right).length := by simp; omega
  have hm : ((left++right).length+1)/2=left.length := by simp; omega
  have ht : (left++right).take (((left++right).length+1)/2)=left := by rw [hm]; simp
  have hd : (left++right).drop (((left++right).length+1)/2)=right := by rw [hm]; simp
  cases he : left++right with
  | nil => simp [he] at hn
  | cons a rest =>
    cases rest with
    | nil => simp [he] at hn
    | cons b rest =>
      rw [he] at ht hd
      change encodeBalancedList (a::b::rest)=_
      rw [encodeBalancedList,ht,hd]

theorem local_sound (prior : List Row) (row : Row)
    (hp : ∀ entry∈prior,Meaning entry) (hc : unpairCheck prior row=true) : Meaning row := by
  rw [unpairCheck_eq] at hc
  unfold localCheck at hc
  split at hc
  · simp only [Bool.and_eq_true,beq_iff_eq] at hc
    exact ⟨[],by simpa [encodeBalancedList] using hc.1.symm,by simpa using hc.2.symm⟩
  · split at hc
    · simp only [Bool.and_eq_true,beq_iff_eq] at hc
      refine ⟨[row.payload],?_,by simpa using hc.2.symm⟩
      have h := congrArg (fun p : Nat×Nat => Nat.pair p.1 p.2) hc.1
      simpa [encodeBalancedList] using h.symm
    · split at hc
      · simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,Bool.or_eq_true,decide_eq_true_eq,and_assoc] at hc
        obtain ⟨left,hl,right,hr,hpair,hcount,hbalance,hpositive⟩ := hc
        obtain ⟨lv,hlc,hln⟩ := hp left hl
        obtain ⟨rv,hrc,hrn⟩ := hp right hr
        refine ⟨lv++rv,?_,by simp [hln,hrn,hcount]⟩
        rw [encode_append lv rv (by omega) (by omega),hlc,hrc]
        have h := congrArg (fun p : Nat×Nat => Nat.pair p.1 p.2) hpair
        simpa using h.symm
      · contradiction

theorem check_sound (prior rows : List Row) (hp : ∀ entry∈prior,Meaning entry)
    (hc : checkFrom prior rows=true) : ∀ entry∈prior++rows,Meaning entry := by
  induction rows generalizing prior with
  | nil => simpa using hp
  | cons row rest ih =>
    simp only [checkFrom,Bool.and_eq_true] at hc
    have hn : ∀ entry∈prior++[row],Meaning entry := by
      intro entry he
      rcases List.mem_append.mp he with hm|hm
      · exact hp entry hm
      · simpa using List.mem_singleton.mp hm ▸ local_sound prior row hp hc.1
    simpa [List.append_assoc] using ih (prior++[row]) hn hc.2

theorem local_mono (small large : List Row) (row : Row)
    (hi : ∀ entry∈small,entry∈large) (hc : unpairCheck small row=true) :
    unpairCheck large row=true := by
  rw [unpairCheck_eq] at hc ⊢
  unfold localCheck at *
  split at hc <;> simp_all only [↓reduceIte]
  split at hc <;> simp_all only [↓reduceIte]
  split at hc <;> simp_all only [↓reduceIte]
  simp only [List.any_eq_true] at hc ⊢
  obtain ⟨left,hl,right,hr,h⟩ := hc
  exact ⟨left,hi left hl,right,hi right hr,h⟩

theorem check_mono (small large rows : List Row)
    (hi : ∀ entry∈small,entry∈large) (hc : checkFrom small rows=true) : checkFrom large rows=true := by
  induction rows generalizing small large with
  | nil => rfl
  | cons row rest ih =>
    simp only [checkFrom,Bool.and_eq_true] at hc ⊢
    refine ⟨local_mono small large row hi hc.1,ih (small++[row]) (large++[row]) ?_ hc.2⟩
    intro entry he
    rcases List.mem_append.mp he with h|h
    · exact List.mem_append_left _ (hi entry h)
    · exact List.mem_append_right _ h

theorem check_append (prior left right : List Row) :
    checkFrom prior (left++right)= (checkFrom prior left && checkFrom (prior++left) right) := by
  induction left generalizing prior with
  | nil => simp [checkFrom]
  | cons row rest ih => simp [checkFrom,ih,List.append_assoc,Bool.and_assoc]

def rootRow (values : List Nat) : Row :=
  match values with
  | [] => ⟨0,0,0,0⟩
  | [value] => ⟨1,Nat.pair 1 value,1,value⟩
  | _::_::_ => ⟨2,encodeBalancedList values,values.length,0⟩

theorem rootRow_code (values : List Nat) : (rootRow values).code=encodeBalancedList values := by
  cases values with
  | nil => simp [rootRow,encodeBalancedList]
  | cons a rest => cases rest <;> simp [rootRow,encodeBalancedList]

theorem rootRow_count (values : List Nat) : (rootRow values).count=values.length := by
  cases values with
  | nil => rfl
  | cons a rest => cases rest <;> rfl

end NearCubicWires.RepairSource.RecoveryOracle.BalancedCertificate
