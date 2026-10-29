import SourceAdapters.Proximity.FiniteTables

/-!
Q02/Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the fixed-query decision table is
converted by an actual ordinary machine into the common padded literal
block. A second finite ordinary table prints the selected local honest
assignment from the decision table and query-answer tuple. Supplying these
finite input tables by repeated source calls remains a separate adapter.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.TseitinCNF
open NearCubicGates.Published.CW19Proximity

def predicateTable {q : ℕ} (predicate : BitInput q → Bool) : BitInput (2 ^ q) :=
  fun code => predicate (fun i => code.val.testBit i.val)

def predicateOfTable {q : ℕ} (table : BitInput (2 ^ q)) : BitInput q → Bool :=
  fun input => table ⟨bitAssignmentCode input, bitAssignmentCode_lt_two_pow input⟩

theorem predicateOfTable_table {q : ℕ} (predicate : BitInput q → Bool) :
    predicateOfTable (predicateTable predicate) = predicate := by
  funext input
  unfold predicateOfTable predicateTable
  congr 1
  funext i
  exact bitAssignmentCode_testBit input i

/-- Flat local literals: sign followed by the self-delimited binary local index. -/
def blockWord {q : ℕ} (predicate : BitInput q → Bool) : List Bool :=
  (predicateBlock predicate).flatMap fun clause =>
    clause.flatMap fun literal => [literal.1] ++ frame literal.2.bits

def blockTableWord {q : ℕ} (table : BitInput (2 ^ q)) : List Bool :=
  blockWord (predicateOfTable table)

theorem blockTableWord_predicate {q : ℕ} (predicate : BitInput q → Bool) :
    blockTableWord (predicateTable predicate) = blockWord predicate := by
  simp only [blockTableWord, predicateOfTable_table]

/-- Actual finite-control ordinary compiler; q is fixed before circuit input length. -/
theorem blockTable_polynomial (q : ℕ) :
    SourcePolyTime (fun table : BitInput (2 ^ q) => List.ofFn table) blockTableWord :=
  table_polynomial blockTableWord

/-- Concatenate the complete decision table and the actual q query answers. -/
def honestTableInput {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q) :
    BitInput (2 ^ q + q) := Fin.addCases (predicateTable predicate) input

def honestTableWord {q : ℕ} (table : BitInput (2 ^ q + q)) : List Bool :=
  let truth : BitInput (2 ^ q) := fun i => table (Fin.castAdd q i)
  let input : BitInput q := fun i => table (Fin.natAdd (2 ^ q) i)
  List.ofFn (fun i : Fin (blockVariableBound q) =>
    canonicalBlockAssignment (predicateOfTable truth) input i.val)

theorem honestTableWord_input {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q) :
    honestTableWord (honestTableInput predicate input) =
      List.ofFn (fun i : Fin (blockVariableBound q) => canonicalBlockAssignment predicate input i.val) := by
  simp only [honestTableWord, honestTableInput, Fin.addCases_left, Fin.addCases_right,
    predicateOfTable_table]

/-- Actual finite ordinary honest-assignment table, with its own charged writer. -/
theorem honestTable_polynomial (q : ℕ) :
    SourcePolyTime (fun table : BitInput (2 ^ q + q) => List.ofFn table) honestTableWord :=
  table_polynomial honestTableWord

end NearCubicGates.Adapters.Proximity
