import Proof.Amplification.RecoveryRawSyntaxCertificate
import Proof.MachineModel.OrdinarySignedSortKey

/-! The full raw syntax certificate is polynomial in the original binary
code length, including invalid Boolean tags. Its serialization is a literal
flat bit string with unary list counts and fixed-width scalar fields. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.RawSyntaxCertificate
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pair_double_right (left right : Nat) : 2*right≤Nat.pair left right+1 := by
  cases right with
  | zero => omega
  | succ right => unfold Nat.pair; split <;> nlinarith

theorem list_length_power {α : Type} [Encodable α] (values : List α) (hn : values≠[]) :
    2^values.length≤2*Encodable.encode values := by
  induction values with
  | nil => contradiction
  | cons head rest ih =>
    cases rest with
    | nil =>
      rw [Encodable.encode_list_cons]
      change 2≤2*(Nat.pair (Encodable.encode head) 0+1)
      omega
    | cons item tail =>
      have hi := ih (by simp)
      have hd := pair_double_right (Encodable.encode head) (Encodable.encode (item::tail))
      rw [Encodable.encode_list_cons]
      simp only [List.length_cons,pow_succ] at *
      nlinarith

theorem list_length_bits {α : Type} [Encodable α] (values : List α) :
    values.length≤natBitLength (Encodable.encode values) := by
  by_cases hn : values=[]
  · simp [hn]
  have hp := list_length_power values hn
  have hc : Encodable.encode values<2^natBitLength (Encodable.encode values) :=
    Nat.lt_pow_succ_log_self (by omega) _
  by_contra h
  have hh : 2^(natBitLength (Encodable.encode values)+1)≤2^values.length :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_succ] at hh
  omega

theorem member_code_le {α : Type} [Encodable α] (item : α) (values : List α) (hm : item∈values) :
    Encodable.encode item≤Encodable.encode values := by
  induction values with
  | nil => simp at hm
  | cons head rest ih =>
    rcases List.mem_cons.mp hm with rfl|hr
    · exact (Nat.left_le_pair _ _).trans (Nat.le_succ _)
    · exact (ih hr).trans ((Nat.right_le_pair _ _).trans (Nat.le_succ _))

theorem width_mono {left right : Nat} (h : left≤right) : natBitLength left≤natBitLength right :=
  Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem view_bounds (code : Nat) (view : View) (hc : check code view=true) :
    view.length≤natBitLength code ∧
      ∀ clause∈view,clause.length≤natBitLength code ∧
        ∀ literal∈clause,literal.1≤code ∧ literal.2≤code := by
  have he := (check_iff code view).mp hc
  refine ⟨by simpa [he] using list_length_bits view,?_⟩
  intro clause hm
  have hclause : Encodable.encode clause≤code := (member_code_le clause view hm).trans_eq he
  refine ⟨(list_length_bits clause).trans (width_mono hclause),?_⟩
  intro literal hl
  have hcode : Encodable.encode literal≤code := (member_code_le literal clause hl).trans hclause
  rcases literal with ⟨tag,index⟩
  change Nat.pair tag index≤code at hcode
  exact ⟨(Nat.left_le_pair _ _).trans hcode,(Nat.right_le_pair _ _).trans hcode⟩

def literals (view : View) := (view.map List.length).sum

theorem literals_bound (view : View) (bound : Nat) (h : ∀ clause∈view,clause.length≤bound) :
    literals view≤bound*view.length := by
  induction view with
  | nil => simp [literals]
  | cons clause rest ih =>
    have hh := h clause (by simp)
    have ht := ih (by intro c hc; exact h c (by simp [hc]))
    simp only [literals,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

def packLiteral (width : Nat) (literal : Nat×Nat) : List Bool :=
  SignedSortKey.binary width literal.1++SignedSortKey.binary width literal.2
def packClause (width : Nat) (clause : List (Nat×Nat)) : List Bool :=
  List.replicate clause.length true++[false]++clause.flatMap (packLiteral width)
def pack (width : Nat) (view : View) : List Bool :=
  List.replicate view.length true++[false]++view.flatMap (packClause width)

theorem pack_literal_length (width : Nat) (literal : Nat×Nat) :
    (packLiteral width literal).length=2*width := by simp [packLiteral]; omega

theorem pack_clause_length (width : Nat) (clause : List (Nat×Nat)) :
    (packClause width clause).length=(2*width+1)*clause.length+1 := by
  have hflat : (clause.flatMap (packLiteral width)).length=2*width*clause.length := by
    induction clause with
    | nil => simp
    | cons literal rest ih => simp only [List.flatMap_cons,List.length_append,pack_literal_length,ih,List.length_cons]; ring
  simp only [packClause,List.length_append,List.length_replicate,List.length_singleton,hflat]
  ring

theorem pack_length (width : Nat) (view : View) :
    (pack width view).length=2*view.length+1+(2*width+1)*literals view := by
  have hflat : (view.flatMap (packClause width)).length=(2*width+1)*literals view+view.length := by
    induction view with
    | nil => simp [literals]
    | cons clause rest ih =>
      simp only [List.flatMap_cons,List.length_append,pack_clause_length,ih,literals,List.map_cons,List.sum_cons,List.length_cons] at *
      ring
  simp only [pack,List.length_append,List.length_replicate,List.length_singleton,hflat]
  omega

theorem pack_bound (code : Nat) (view : View) (hc : check code view=true) :
    (pack (natBitLength code) view).length≤8*(natBitLength code+1)^3 := by
  obtain ⟨hview,hclauses⟩ := view_bounds code view hc
  have h := literals_bound view (natBitLength code) (by intro clause hm; exact (hclauses clause hm).1)
  have hm : literals view≤(natBitLength code)^2 := by nlinarith
  have hp := Nat.mul_le_mul_left (2*natBitLength code+1) hm
  rw [pack_length]
  nlinarith

theorem field_values (code : Nat) (view : View) (hc : check code view=true)
    (clause : List (Nat×Nat)) (hm : clause∈view) (literal : Nat×Nat) (hl : literal∈clause) :
    RadixSemantics.value (SignedSortKey.binary (natBitLength code) literal.1)=literal.1 ∧
      RadixSemantics.value (SignedSortKey.binary (natBitLength code) literal.2)=literal.2 := by
  have h := ((view_bounds code view hc).2 clause hm).2 literal hl
  have hb : code<2^natBitLength code := Nat.lt_pow_succ_log_self (by omega) _
  exact ⟨SignedSortKey.binary_value _ _ (h.1.trans_lt hb),SignedSortKey.binary_value _ _ (h.2.trans_lt hb)⟩

theorem bounded_raw_view (code : Nat) :
    ∃ view : View,check code view=true ∧ (pack (natBitLength code) view).length≤8*(natBitLength code+1)^3 := by
  obtain ⟨view,hv⟩ := exists_view code
  exact ⟨view,hv,pack_bound code view hv⟩

end NearCubicWires.RepairSource.RecoveryOracle.RawSyntaxCertificate
