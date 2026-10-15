import Proof.Amplification.RecoveryRowStructureChildrenEntry

/-! Exact semantic acceptance of the complete paired-row ordinary caller.
Both actual first-match lookups select the arithmetic operands; the checked
prefix later connects these counts to the balanced-certificate row rule. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate RecoveryRowLookupTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bankOutput_width (x : Children) (bits : List Bool) :
    (bankOutput x bits).bank.row.width=x.bank.row.width :=
  (iterate_retained x.total ⟨clean x.bank,bits⟩).1

theorem right_output_answer (x : Children) (key bits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    (rightOutput x key bits).base.valid=
      match lookupCount rows (value key) with
      | none=>false
      | some count=>countsCheck (value x.base.count) (value x.base.code) count := by
  obtain ⟨hfound,hsaved⟩ := output_lookup x.total (bankKey x key).bank bits rows rest hp
  change (rightFound x key bits).bank.found=rows.any (fun row=>decide (value key=row.code)) at hfound
  change value (rightFound x key bits).bank.saved=lookupOr rows (value key) (value x.bank.saved) at hsaved
  rw [lookupFound_option] at hfound
  rw [lookupOr_option] at hsaved
  cases hcode : lookupCount rows (value key) with
  | none =>
    have hf : (rightFound x key bits).bank.found=false := by simpa only [hcode,Option.isSome_none] using hfound
    simp only [rightOutput,hf,Bool.false_eq_true,if_false]
    rfl
  | some count =>
    have hf : (rightFound x key bits).bank.found=true := by simpa only [hcode,Option.isSome_some] using hfound
    have hc : value (rightFound x key bits).bank.saved=count := by simpa only [hcode,Option.getD_some] using hsaved
    simp only [rightOutput,hf,if_true]
    change RecoveryRowCounts.relation x.base.count x.base.code (rightFound x key bits).bank.saved=_
    rw [countsCheck_eq]
    unfold RecoveryRowCounts.relation
    rw [hc]

theorem left_output_answer (x : Children) (left right bits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    (leftOutput x left right bits).base.valid=
      match lookupCount rows (value left),lookupCount rows (value right) with
      | some lc,some rc=>countsCheck (value x.base.count) lc rc
      | _,_=>false := by
  obtain ⟨hfound,hsaved⟩ := output_lookup x.total (bankKey x left).bank bits rows rest hp
  change (leftFound x left bits).bank.found=rows.any (fun row=>decide (value left=row.code)) at hfound
  change value (leftFound x left bits).bank.saved=lookupOr rows (value left) (value x.bank.saved) at hsaved
  rw [lookupFound_option] at hfound
  rw [lookupOr_option] at hsaved
  cases hcode : lookupCount rows (value left) with
  | none =>
    have hf : (leftFound x left bits).bank.found=false := by simpa only [hcode,Option.isSome_none] using hfound
    simp only [leftOutput,hf,Bool.false_eq_true,if_false]
    rfl
  | some count =>
    have hf : (leftFound x left bits).bank.found=true := by simpa only [hcode,Option.isSome_some] using hfound
    have hc : value (leftFound x left bits).bank.saved=count := by simpa only [hcode,Option.getD_some] using hsaved
    simp only [leftOutput,hf,if_true]
    have hwidth : (leftSaved (leftFound x left bits)).bank.row.width=x.bank.row.width := bankOutput_width (bankKey x left) bits
    have hparse : readMany (readRow (leftSaved (leftFound x left bits)).bank.row.width)
        (leftSaved (leftFound x left bits)).total bits=some (rows,rest) := by
      rw [hwidth]
      exact hp
    rw [right_output_answer (leftSaved (leftFound x left bits)) right bits rows rest hparse]
    change (match lookupCount rows (value right) with
      | none=>false
      | some rc=>countsCheck (value x.base.count) (value (leftFound x left bits).bank.saved) rc)=_
    rw [hc]
    cases lookupCount rows (value right) <;> rfl

def pairAnswer (rows : List Row) (parent : Nat) (pair : List Bool) : Bool :=
  match lookupCount rows (Nat.unpair (value pair)).1,lookupCount rows (Nat.unpair (value pair)).2 with
  | some lc,some rc=>countsCheck parent lc rc
  | _,_=>false

theorem children_output_answer (x : Children) (pair bits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    (childrenOutput x pair bits).base.valid=pairAnswer rows (value x.base.count) pair := by
  have h := left_output_answer (decodedChildren x pair) (RecoveryFixedUnpair.leftWord pair)
    (RecoveryChildSelection.word false pair) bits rows rest hp
  rw [(RecoveryLiteralDecode.literal_values pair).1,(RecoveryLiteralDecode.literal_values pair).2] at h
  exact h

theorem pairAnswer_eq_childrenCheck (rows : List Row) (row : Row) (pair : List Bool)
    (hp : value pair=(Nat.unpair row.code).2) (htag : (Nat.unpair row.code).1=2) :
    pairAnswer rows row.count pair=childrenCheck rows row := by
  unfold pairAnswer childrenCheck
  rw [hp,htag]
  cases lookupCount rows (Nat.unpair (Nat.unpair row.code).2).1 <;>
    cases lookupCount rows (Nat.unpair (Nat.unpair row.code).2).2 <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
