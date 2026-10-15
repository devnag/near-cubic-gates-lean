import Proof.Amplification.RecoveryRowLookupLoop

/-! Exact parsing and first-match numeric semantics for the executed
prior-row loop. Repeated checked codes have unique counts, so this is the
lookup required by the balanced-certificate branch checker. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
open LocalBitMultitape RecoveryRowLookupStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate RepairSource.VerifierDecoding
open RecoveryValuationTable (readMany_head_none readMany_head_some)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem readRow_some (width : Nat) (bits : List Bool) (row : Row) (rest : List Bool)
    (h : readRow width bits=some (row,rest)) :
    row=RecoveryRowFields.parsed width bits ∧ rest=bits.drop (4*width) := by
  have hh : 4*width≤bits.length := by
    have hi := congrArg Option.isSome h
    rw [RecoveryCertificateRow.row_isSome] at hi
    simpa only [Option.isSome_some,decide_eq_true_eq] using hi
  rw [RecoveryRowFields.readRow_full width bits hh] at h
  exact ⟨(congrArg Prod.fst (Option.some.inj h)).symm,(congrArg Prod.snd (Option.some.inj h)).symm⟩

theorem advance_width (x : Cursor) : (advance x).data.row.width=x.data.row.width :=
  afterRead_width x.data x.rest
theorem advance_key (x : Cursor) : (advance x).data.key=x.data.key := rfl
theorem advance_rest (x : Cursor) : (advance x).rest=x.rest.drop (4*x.data.row.width) := rfl

theorem iterate_accepts (count : Nat) (x : Cursor) :
    (RepeatMachine.iterate next count x).1=(readMany (readRow x.data.row.width) count x.rest).isSome := by
  induction count generalizing x with
  | zero => rfl
  | succ count ih =>
    cases hp : readRow x.data.row.width x.rest with
    | none =>
      rw [readMany_head_none _ count x.rest hp]
      simp only [RepeatMachine.iterate,next,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    | some pair =>
      rcases pair with ⟨entry,rest⟩
      obtain ⟨_,hr⟩ := readRow_some x.data.row.width x.rest entry rest hp
      simp only [RepeatMachine.iterate,next,hp,Option.isSome_some,↓reduceIte]
      rw [ih (advance x),readMany_head_some _ count x.rest entry rest hp,advance_width,advance_rest,←hr]
      cases readMany (readRow x.data.row.width) count rest <;> rfl

def applyRow (key : Nat) (state : Bool×Nat) (row : Row) : Bool×Nat :=
  (state.1 || decide (key=row.code),if state.1 then state.2 else if key=row.code then row.count else state.2)
def accumulator (x : Cursor) : Bool×Nat := (x.data.found,value x.data.saved)
def lookupOr : List Row→Nat→Nat→Nat
  | [],_,old => old
  | row::rest,key,old => if key=row.code then row.count else lookupOr rest key old
def lookupCount : List Row→Nat→Option Nat
  | [],_ => none
  | row::rest,key => if key=row.code then some row.count else lookupCount rest key

theorem next_accumulator (x : Cursor) (row : Row) (rest : List Bool)
    (hp : readRow x.data.row.width x.rest=some (row,rest)) :
    accumulator (advance x)=applyRow (value x.data.key) (accumulator x) row := by
  obtain ⟨he,_⟩ := readRow_some x.data.row.width x.rest row rest hp
  rw [he]
  let d := (x.data.afterRead x.rest).cell (x.data.codeWord x.rest) (x.data.countWord x.rest)
  apply Prod.ext
  · exact RecoveryRowLookupCell.done_found d
  · change value d.done.saved=(if d.found then value d.saved else
      if value d.key=value d.code then value d.count else value d.saved)
    rw [RecoveryRowLookupCell.done_saved]
    cases d.found <;> by_cases hc : value d.key=value d.code <;> simp [hc]

theorem fold_selected (rows : List Row) (key : Nat) (found : Bool) (old : Nat) :
    (rows.foldl (applyRow key) (found,old)).2=if found then old else lookupOr rows key old := by
  induction rows generalizing found old with
  | nil => cases found <;> rfl
  | cons row rest ih =>
    rw [List.foldl_cons,ih]
    cases found <;> by_cases he : key=row.code <;> simp [applyRow,lookupOr,he]

theorem fold_found (rows : List Row) (key : Nat) (found : Bool) (old : Nat) :
    (rows.foldl (applyRow key) (found,old)).1=(found || rows.any (fun row=>decide (key=row.code))) := by
  induction rows generalizing found old with
  | nil => simp
  | cons row rest ih =>
    rw [List.foldl_cons,ih]
    simp only [applyRow,List.any_cons,Bool.or_assoc]

theorem iterate_accumulator (count : Nat) (x : Cursor) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.data.row.width) count x.rest=some (rows,rest)) :
    accumulator (RepeatMachine.iterate next count x).2=
      rows.foldl (applyRow (value x.data.key)) (accumulator x) := by
  induction count generalizing x rows rest with
  | zero =>
    have he : ([],x.rest)=(rows,rest) := Option.some.inj hp
    have hr : rows=[] := (congrArg Prod.fst he).symm
    subst rows
    rfl
  | succ count ih =>
    cases hrow : readRow x.data.row.width x.rest with
    | none => rw [readMany_head_none _ count x.rest hrow] at hp; contradiction
    | some pair =>
      rcases pair with ⟨row,tail⟩
      obtain ⟨_,ht⟩ := readRow_some x.data.row.width x.rest row tail hrow
      cases htail : readMany (readRow x.data.row.width) count tail with
      | none =>
        rw [readMany_head_some _ count x.rest row tail hrow,htail] at hp
        contradiction
      | some pair =>
        rcases pair with ⟨entries,finish⟩
        have he : (row::entries,finish)=(rows,rest) := by
          rw [readMany_head_some _ count x.rest row tail hrow,htail] at hp
          exact Option.some.inj hp
        have hr : rows=row::entries := (congrArg Prod.fst he).symm
        subst rows
        have htail' : readMany (readRow (advance x).data.row.width) count (advance x).rest=
            some (entries,finish) := by
          rw [advance_width,advance_rest,←ht]
          exact htail
        have hi := ih (advance x) entries finish htail'
        simp only [RepeatMachine.iterate,next,hrow,Option.isSome_some,↓reduceIte,List.foldl_cons]
        rw [hi,advance_key,next_accumulator x row tail hrow]

theorem lookupCount_getD (rows : List Row) (key old : Nat) :
    (lookupCount rows key).getD old=lookupOr rows key old := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    by_cases he : key=row.code <;> simp [lookupCount,lookupOr,he,ih]

end NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
