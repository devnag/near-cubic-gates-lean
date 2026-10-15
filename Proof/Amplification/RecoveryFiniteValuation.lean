import Proof.Amplification.RecoveryCompactSize

/-! One finite indexed valuation is shared by all clause checks. Lookup
always takes the first matching index, so repeated variables are consistent
without a separate pairwise-consistency algorithm. Prefix counts remain
binary and are used only by comparison and bounded-word bit lookup. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.FiniteValuation
open TseitinCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Table := List (Nat×Bool)
def lookup : Table → Nat → Bool
  | [],_ => false
  | (key,bit)::rest,index => if index=key then bit else lookup rest index
def ofAssignment (indices : List Nat) (assignment : Nat → Bool) : Table :=
  indices.map fun index => (index,assignment index)
def assignment (committed count : Nat) (table : Table) (index : Nat) : Bool :=
  if index<count then committed.testBit index else lookup table index
def check (request : CompactRequest) (table : Table) : Bool :=
  request.base.all (fun clause => clause.length=3) &&
    formulaEval (assignment request.committed request.count table) request.base

theorem lookup_of_mem (indices : List Nat) (a : Nat → Bool) (index : Nat) (hi : index∈indices) :
    lookup (ofAssignment indices a) index=a index := by
  induction indices with
  | nil => simp at hi
  | cons head rest ih =>
    rcases List.mem_cons.mp hi with rfl|hm
    · simp [ofAssignment,lookup]
    · by_cases he : index=head
      · simp [ofAssignment,lookup,he]
      · simpa [ofAssignment,lookup,he] using ih hm

theorem assignment_on_base (request : CompactRequest) (a : Nat → Bool)
    (hp : ∀ index<request.count,a index=request.committed.testBit index)
    {clause : List (Bool×Nat)} (hc : clause∈request.base) {literal : Bool×Nat} (hl : literal∈clause) :
    assignment request.committed request.count (ofAssignment request.variables a) literal.2=a literal.2 := by
  have hv : literal.2∈request.variables := by
    simp only [CompactRequest.variables,List.mem_eraseDups,List.mem_map]
    exact ⟨literal,List.mem_flatten.mpr ⟨clause,hc,hl⟩,rfl⟩
  by_cases hi : literal.2<request.count
  · simp [assignment,hi,hp _ hi]
  · simp [assignment,hi,lookup_of_mem request.variables a literal.2 hv]

theorem check_of_assignment (request : CompactRequest) (a : Nat → Bool)
    (hthree : request.base.all (fun clause => clause.length=3)=true)
    (hp : ∀ index<request.count,a index=request.committed.testBit index)
    (heval : formulaEval a request.base=true) : check request (ofAssignment request.variables a)=true := by
  simp only [check,hthree,Bool.true_and]
  have heq : formulaEval (assignment request.committed request.count (ofAssignment request.variables a)) request.base=
      formulaEval a request.base := by
    unfold formulaEval clauseEval
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true,List.any_eq_true]
    apply forall_congr'
    intro clause
    apply imp_congr_right
    intro hc
    apply exists_congr
    intro literal
    apply and_congr_right
    intro hl
    simp [literalEval,assignment_on_base request a hp hc hl]
  exact heq.trans heval

theorem check_sound (request : CompactRequest) (table : Table) (hc : check request table=true) :
    compactMeaning request := by
  simp only [check,Bool.and_eq_true] at hc
  exact ⟨hc.1,assignment request.committed request.count table,
    (by intro index hi; simp [assignment,hi]),hc.2⟩

theorem check_iff (request : CompactRequest) :
    (∃ table,check request table=true) ↔ compactMeaning request := by
  constructor
  · rintro ⟨table,hc⟩; exact check_sound request table hc
  · rintro ⟨hthree,a,hp,heval⟩
    exact ⟨ofAssignment request.variables a,check_of_assignment request a hthree hp heval⟩

theorem bounded_table (request : CompactRequest) (hm : compactMeaning request) :
    ∃ table,check request table=true ∧ table.length≤3*request.base.length ∧
      ∀ entry∈table,entry.1∈request.variables := by
  obtain ⟨old,ho⟩ := (compactVerifier_iff request).mpr hm
  have hlen := compact_witness_length ho
  have hold : old.length=request.variables.length := by
    have hh := ho
    simp only [compactVerifier,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1.1
  rcases hm with ⟨hthree,a,hp,heval⟩
  refine ⟨ofAssignment request.variables a,check_of_assignment request a hthree hp heval,?_,?_⟩
  · simpa only [ofAssignment,List.length_map,hold] using hlen
  · intro entry he
    obtain ⟨index,hi,rfl⟩ := List.mem_map.mp he
    exact hi

end NearCubicWires.RepairSource.RecoveryOracle.FiniteValuation
