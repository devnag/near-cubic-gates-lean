import Proof.Amplification.RecoveryValuationTableLoop

/-! Exact parser and first-match semantics of the physical valuation loop. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationTable
open LocalBitMultitape RecoveryValuationStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem readEntry_some (width : Nat) (bits : List Bool) (entry : Nat×Bool) (rest : List Bool)
    (h : readEntry width bits=some (entry,rest)) :
    entry=(value (bits.take width),bits[width]?.getD false) ∧ rest=bits.drop (width+1) := by
  have hh : width<bits.length := by
    have hi := congrArg Option.isSome h
    rw [readEntry_isSome] at hi
    simp only [Option.isSome_some,decide_eq_true_eq] at hi
    omega
  rw [readEntry_full width bits hh] at h
  exact ⟨(congrArg Prod.fst (Option.some.inj h)).symm,(congrArg Prod.snd (Option.some.inj h)).symm⟩

theorem readMany_head_none {α : Type} (read : Parser α) (count : Nat) (bits : List Bool)
    (h : read bits=none) : readMany read (count+1) bits=none := by
  rw [readMany,h]
  rfl

theorem readMany_head_some {α : Type} (read : Parser α) (count : Nat) (bits : List Bool)
    (item : α) (rest : List Bool) (h : read bits=some (item,rest)) :
    readMany read (count+1) bits=(readMany read count rest).map (fun pair=>(item::pair.1,pair.2)) := by
  rw [readMany,h]
  change (readMany read count rest).bind (fun pair=>some (item::pair.1,pair.2))=_
  cases readMany read count rest with
  | none => rfl
  | some pair => cases pair; rfl

theorem iterate_accepts (count : Nat) (x : Cursor) :
    (RepeatMachine.iterate next count x).1=(readMany (readEntry x.data.width) count x.rest).isSome := by
  induction count generalizing x with
  | zero => rfl
  | succ count ih =>
    cases hp : readEntry x.data.width x.rest with
    | none =>
      rw [readMany_head_none _ count x.rest hp]
      simp only [RepeatMachine.iterate,next,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    | some pair =>
      rcases pair with ⟨entry,rest⟩
      obtain ⟨_,hr⟩ := readEntry_some x.data.width x.rest entry rest hp
      simp only [RepeatMachine.iterate,next,hp,Option.isSome_some,↓reduceIte]
      rw [ih (advance x),readMany_head_some _ count x.rest entry rest hp]
      change (readMany (readEntry x.data.width) count (x.rest.drop (x.data.width+1))).isSome=_
      rw [←hr]
      cases readMany (readEntry x.data.width) count rest <;> rfl

def applyEntry (index : Nat) (state : Bool×Bool) (entry : Nat×Bool) : Bool×Bool :=
  (RecoveryValuationRow.matched state.1 (decide (index=entry.1)),
    RecoveryValuationRow.selected state.1 (decide (index=entry.1)) entry.2 state.2)
def accumulator (x : Cursor) : Bool×Bool := (x.data.found,x.data.value)
def lookupOr : FiniteValuation.Table→Nat→Bool→Bool
  | [],_,old=>old
  | (key,bit)::rest,index,old=>if index=key then bit else lookupOr rest index old

theorem fold_selected (table : FiniteValuation.Table) (index : Nat) (found old : Bool) :
    (table.foldl (applyEntry index) (found,old)).2=
      if found then old else lookupOr table index old := by
  induction table generalizing found old with
  | nil => cases found <;> rfl
  | cons entry rest ih =>
    rcases entry with ⟨key,bit⟩
    rw [List.foldl_cons,ih]
    cases found <;> by_cases he : index=key <;>
      simp [applyEntry,RecoveryValuationRow.matched,RecoveryValuationRow.selected,lookupOr,he]

theorem lookupOr_false (table : FiniteValuation.Table) (index : Nat) :
    lookupOr table index false=FiniteValuation.lookup table index := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key,bit⟩
    simp only [lookupOr,FiniteValuation.lookup,ih]

theorem iterate_accumulator (count : Nat) (x : Cursor) (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readMany (readEntry x.data.width) count x.rest=some (table,rest)) :
    accumulator (RepeatMachine.iterate next count x).2=
      table.foldl (applyEntry (value x.data.index)) (accumulator x) := by
  induction count generalizing x table rest with
  | zero =>
    have he : ([],x.rest)=(table,rest) := Option.some.inj hp
    have ht : table=[] := (congrArg Prod.fst he).symm
    subst table
    rfl
  | succ count ih =>
    cases hentry : readEntry x.data.width x.rest with
    | none => rw [readMany_head_none _ count x.rest hentry] at hp; contradiction
    | some pair =>
      rcases pair with ⟨entry,tail⟩
      obtain ⟨he,ht⟩ := readEntry_some x.data.width x.rest entry tail hentry
      cases htail : readMany (readEntry x.data.width) count tail with
      | none =>
        rw [readMany_head_some _ count x.rest entry tail hentry,htail] at hp
        contradiction
      | some pair =>
        rcases pair with ⟨entries,finish⟩
        have hresult : (entry::entries,finish)=(table,rest) := by
          rw [readMany_head_some _ count x.rest entry tail hentry,htail] at hp
          exact Option.some.inj hp
        have htable : table=entry::entries := (congrArg Prod.fst hresult).symm
        subst table
        have htail' : readMany (readEntry (advance x).data.width) count (advance x).rest=some (entries,finish) := by
          simpa only [advance,Data.done,Data.afterRow,Data.afterMatch,Data.afterField,ht] using htail
        have hi := ih (advance x) entries finish htail'
        simp only [RepeatMachine.iterate,next,hentry,Option.isSome_some,↓reduceIte,List.foldl_cons]
        rw [hi]
        rw [he]
        rfl

end NearCubicWires.RepairOrdinary.RecoveryValuationTable
