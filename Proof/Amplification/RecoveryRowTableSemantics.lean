import Proof.Amplification.RecoveryRowTableInvariant

namespace NearCubicWires.RepairOrdinary.RecoveryRowTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def localAnswer (width : Nat) (P : Nat→Bool) (prior : List Row) (input : List Bool) : Bool :=
  (readRow width input).any (fun pair=>unpairCheck prior pair.1 && leafCheck P pair.1)
def tableCheck (width : Nat) (P : Nat→Bool) : Nat→List Row→List Bool→Bool
  | 0,_,_=>true
  | n+1,prior,input=>match readRow width input with
    | none=>false
    | some (row,rest)=>unpairCheck prior row && leafCheck P row && tableCheck width P n (prior++[row]) rest

theorem body_answer (width limit : Nat) (word bits : List Bool) (P : Nat→Bool) (x : Cursor)
    (hx : Inv width limit word bits P x) :
    readWholeAnswer x.data word bits x.input=localAnswer width P x.prior x.input := by
  cases hp : readRow width x.input with
  | none => simp only [readWholeAnswer,hx.sameWidth,hp,Option.isSome_none,Bool.false_and,localAnswer,Option.any_none]
  | some pair =>
    rcases pair with ⟨row,rest⟩
    have hi : 4*x.data.base.state.bits.length ≤ x.input.length := by
      have h := congrArg Option.isSome hp
      simpa only [RecoveryCertificateRow.row_isSome,Option.isSome_some,decide_eq_true_eq,hx.sameWidth] using h
    have hb : x.data.bank.row.width=width := hx.ready.2.1.2.1.trans hx.sameWidth
    have hprefix : readMany (readRow x.data.bank.row.width) x.data.total bits=some (x.prior,x.input) := by
      rw [hb]; exact hx.parsed
    have h := read_whole_answer x.data word bits x.input x.prior x.input hprefix hx.checked hi
    rw [hx.predicate,hx.sameWidth] at h
    rw [h]
    have he := RecoveryRowLookupTable.readRow_some width x.input row rest hp
    simp only [localAnswer,hp,Option.any_some,he.1]

theorem table_check_reject (width : Nat) (P : Nat→Bool) (n : Nat) (prior : List Row) (input : List Bool)
    (h : localAnswer width P prior input=false) : tableCheck width P (n+1) prior input=false := by
  unfold localAnswer at h
  unfold tableCheck
  cases hp : readRow width input with
  | none=>rfl
  | some pair=>
    rcases pair with ⟨row,rest⟩
    simp only [hp,Option.any_some] at h
    change ((unpairCheck prior row && leafCheck P row) && tableCheck width P n (prior++[row]) rest)=false
    rw [h]
    rfl

theorem table_check_advance (width : Nat) (P : Nat→Bool) (n : Nat) (x : Cursor) (word bits : List Bool)
    (out : ReadLeafResult x.data word bits x.input) (hw : x.data.base.state.bits.length=width)
    (h : localAnswer width P x.prior x.input=true) :
    tableCheck width P (n+1) x.prior x.input=
      tableCheck width P n (advance x word bits out).prior (advance x word bits out).input := by
  have hi : 4*width ≤ x.input.length := by
    have hs : (readRow width x.input).isSome=true := Option.isSome_iff_exists.mpr (by
      cases hp : readRow width x.input with
      | none=>simp [localAnswer,hp] at h
      | some pair=>exact ⟨pair,rfl⟩)
    simpa only [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] using hs
  have hp := RecoveryRowFields.readRow_full width x.input hi
  simp only [localAnswer,hp,Option.any_some] at h
  simp only [tableCheck,hp,h,Bool.true_and,advance,hw]

theorem table_check_parser (width : Nat) (P : Nat→Bool) (n : Nat) (prior : List Row) (input : List Bool) :
    tableCheck width P n prior input=
      (readMany (readRow width) n input).any (fun pair=>checkFrom prior pair.1 && pair.1.all (leafCheck P)) := by
  induction n generalizing prior input with
  | zero=>rfl
  | succ n ih=>
    cases hp : readRow width input with
    | none=>rw [RecoveryValuationTable.readMany_head_none _ n input hp]; simp [tableCheck,hp]
    | some pair=>
      rcases pair with ⟨row,rest⟩
      rw [RecoveryValuationTable.readMany_head_some _ n input row rest hp]
      simp only [tableCheck,hp,ih]
      cases ht : readMany (readRow width) n rest with
      | none=>simp
      | some pair=>
        rcases pair with ⟨rows,tail⟩
        simp only [Option.map_some,Option.any_some,checkFrom,List.all_cons]
        cases unpairCheck prior row <;> cases leafCheck P row <;>
          cases checkFrom (prior++[row]) rows <;> cases rows.all (leafCheck P) <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryRowTable
