import Proof.Amplification.RecoveryBalancedCertificateSize

/-! A total raw syntax certificate retains natural Boolean tags before
validation. Consequently it can certify the legacy decoder's failure and
its default empty-CNF behavior, rather than accidentally rejecting it. The
checks below consume predecessor/unpair results, not a constructed encoding. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.RawSyntaxCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def listCheck {α : Type} (itemCheck : Nat → α → Bool) (code : Nat) : List α → Bool
  | [] => code==0
  | item::rest => code != 0 && itemCheck (Nat.unpair (code-1)).1 item &&
      listCheck itemCheck (Nat.unpair (code-1)).2 rest

theorem listCheck_iff {α : Type} [Encodable α] (itemCheck : Nat → α → Bool)
    (hi : ∀ code item,itemCheck code item=true ↔ Encodable.encode item=code)
    (values : List α) (code : Nat) :
    listCheck itemCheck code values=true ↔ Encodable.encode values=code := by
  induction values generalizing code with
  | nil =>
    change (code==0)=true ↔ 0=code
    rw [beq_iff_eq]
    exact eq_comm
  | cons item rest ih =>
    cases code with
    | zero => simp [listCheck,Encodable.encode_list_cons]
    | succ code =>
      simp only [listCheck,Nat.add_sub_cancel,Bool.and_eq_true,hi,ih]
      constructor
      · rintro ⟨⟨_,hh⟩,ht⟩
        rw [Encodable.encode_list_cons,hh,ht,Nat.pair_unpair]
      · intro h
        rw [Encodable.encode_list_cons] at h
        have hp : Nat.pair (Encodable.encode item) (Encodable.encode rest)=code := by omega
        have hu := congrArg Nat.unpair hp
        simp only [Nat.unpair_pair] at hu
        exact ⟨⟨by simp,(congrArg Prod.fst hu)⟩,congrArg Prod.snd hu⟩

def literalCheck (code : Nat) (literal : Nat×Nat) : Bool := Nat.unpair code==literal

theorem literalCheck_iff (code : Nat) (literal : Nat×Nat) :
    literalCheck code literal=true ↔ Encodable.encode literal=code := by
  rcases literal with ⟨tag,index⟩
  change (Nat.unpair code==(tag,index))=true ↔ Nat.pair tag index=code
  simp only [beq_iff_eq]
  constructor
  · intro h
    have he := congrArg (fun p : Nat×Nat => Nat.pair p.1 p.2) h
    simpa using he.symm
  · intro h
    have he := congrArg Nat.unpair h
    simpa using he.symm

abbrev View := List (List (Nat×Nat))
def clauseCheck := listCheck literalCheck
def check := listCheck clauseCheck

theorem check_iff (code : Nat) (view : View) : check code view=true ↔ Encodable.encode view=code :=
  listCheck_iff clauseCheck (fun c clause => listCheck_iff literalCheck literalCheck_iff clause c) view code

def OntoEncoding (α : Type) [Encodable α] : Prop := ∀ code,∃ value : α,Encodable.encode value=code

theorem onto_nat : OntoEncoding Nat := fun code => ⟨code,rfl⟩

theorem onto_prod {α β : Type} [Encodable α] [Encodable β]
    (ha : OntoEncoding α) (hb : OntoEncoding β) : OntoEncoding (α×β) := by
  intro code
  obtain ⟨left,hl⟩ := ha (Nat.unpair code).1
  obtain ⟨right,hr⟩ := hb (Nat.unpair code).2
  exact ⟨(left,right),by rw [Encodable.encode_prod_val,hl,hr,Nat.pair_unpair]⟩

theorem onto_list {α : Type} [Encodable α] (ha : OntoEncoding α) : OntoEncoding (List α) := by
  intro code
  induction code using Nat.strong_induction_on with
  | h code ih =>
    cases code with
    | zero => exact ⟨[],rfl⟩
    | succ code =>
      obtain ⟨head,hh⟩ := ha (Nat.unpair code).1
      obtain ⟨tail,ht⟩ := ih (Nat.unpair code).2 (Nat.lt_succ_of_le (Nat.unpair_right_le code))
      exact ⟨head::tail,by rw [Encodable.encode_list_cons,hh,ht,Nat.pair_unpair]⟩

theorem exists_view (code : Nat) : ∃ view : View,check code view=true := by
  obtain ⟨view,h⟩ := onto_list (onto_list (onto_prod onto_nat onto_nat)) code
  exact ⟨view,(check_iff code view).mpr h⟩

def projectLiteral (literal : Nat×Nat) : Bool×Nat := (literal.1==1,literal.2)
def projectClause (clause : List (Nat×Nat)) := clause.map projectLiteral
def project (view : View) := view.map projectClause
def tagsValid (view : View) : Bool := view.all fun clause => clause.all fun literal => literal.1≤1

theorem decode_bool_tag (tag : Nat) :
    Encodable.decode (α := Bool) tag=if tag≤1 then some (tag==1) else none := by
  cases tag with
  | zero => rfl
  | succ tag =>
    cases tag with
    | zero => rfl
    | succ tag =>
      rw [Encodable.decode_ge_two _ (by omega),if_neg (by omega)]

theorem decode_literal (literal : Nat×Nat) :
    Encodable.decode (α := Bool×Nat) (Encodable.encode literal)=
      if literal.1≤1 then some (projectLiteral literal) else none := by
  rw [Encodable.encode_prod_val,Encodable.decode_prod_val]
  change (do
    let b ← Encodable.decode (α := Bool) (Nat.unpair (Nat.pair literal.1 literal.2)).1
    let n ← Encodable.decode (α := Nat) (Nat.unpair (Nat.pair literal.1 literal.2)).2
    pure (b,n))=_
  rw [Nat.unpair_pair,decode_bool_tag]
  split <;> rfl

theorem decode_clause (clause : List (Nat×Nat)) :
    Encodable.decode (α := List (Bool×Nat)) (Encodable.encode clause)=
      if clause.all (fun literal => literal.1≤1) then some (projectClause clause) else none := by
  induction clause with
  | nil => simp [projectClause]
  | cons literal rest ih =>
    rw [Encodable.encode_list_cons,Encodable.decode_list_succ,Nat.unpair_pair,decode_literal,ih]
    simp only [List.all_cons,projectClause,List.map_cons]
    by_cases htag : literal.1≤1
    · cases ht : rest.all (fun literal => decide (literal.1≤1)) <;>
        simp only [htag,decide_true,ite_true,Bool.true_and,Bool.false_eq_true,ite_false] <;> rfl
    · cases ht : rest.all (fun literal => decide (literal.1≤1)) <;>
        simp only [htag,decide_false,ite_false,Bool.false_and] <;> rfl

theorem decode_view (view : View) :
    Encodable.decode (α := EncodedCNF) (Encodable.encode view)=
      if tagsValid view then some (project view) else none := by
  induction view with
  | nil => simp [tagsValid,project]
  | cons clause rest ih =>
    rw [Encodable.encode_list_cons,Encodable.decode_list_succ,Nat.unpair_pair,decode_clause,ih]
    simp only [tagsValid,List.all_cons,project,List.map_cons]
    cases hc : clause.all (fun literal => decide (literal.1≤1)) <;>
      cases hr : rest.all (fun clause => clause.all (fun literal => decide (literal.1≤1))) <;>
      simp only [Bool.true_and,Bool.false_and,Bool.false_eq_true,ite_false,ite_true] <;> rfl

theorem certified_decode (code : Nat) (view : View) (hc : check code view=true) :
    Encodable.decode (α := EncodedCNF) code=if tagsValid view then some (project view) else none := by
  rw [← (check_iff code view).mp hc]
  exact decode_view view

theorem certified_default (code : Nat) (view : View) (hc : check code view=true) :
    decodeCNF code=if tagsValid view then project view else [] := by
  unfold decodeCNF
  rw [certified_decode code view hc]
  cases tagsValid view <;> rfl

theorem invalid_raw_accepted (code : Nat) (view : View)
    (hc : check code view=true) (hi : tagsValid view=false) : correctedSat code=true := by
  have hd : decodeCNF code=[] := by rw [certified_default code view hc,hi]; rfl
  have hw : wellSizedCNFEncoding code (decodeCNF code)=true := by
    simp [hd,wellSizedCNFEncoding]
  rw [correctedSat,if_pos hw]
  rw [legacySat_wellSized_iff code hw]
  exact ⟨fun _ => false,by simp [hd,TseitinCNF.formulaEval]⟩

end NearCubicWires.RepairSource.RecoveryOracle.RawSyntaxCertificate
