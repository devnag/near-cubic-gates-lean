import SourceAdapters.Compile.OracleQueryPrefix
import SourceAdapters.Compile.BoundedSizes

/-!
proof of `thm:short-pcp-ours`, Step 4: explicit gates select finite query cells and allocated length.
The length uses one-hot wires, preserving literal-list termination. Together
with prefixExpression these gates recognize every possible query length with
an explicit linear operation bound per candidate; no truth table is expanded.
The shared disjunction expression supplies the operation bound.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def queryWordBits (width : ℕ) := width+(width+1)

def queryWordEncoding (width : ℕ) (word : List Bool) : BitInput (queryWordBits width) :=
  Fin.addCases (fun i : Fin width => word.getD i.val false)
    (fun length : Fin (width+1) => decide (word.length=length.val))

def queryCellExpression (width position : ℕ) : BoolExpr (queryWordBits width) :=
  if h : position<width then .input ((⟨position,h⟩ : Fin width).castAdd (width+1)) else .const false

def queryAllocatedExpression (width position : ℕ) : BoolExpr (queryWordBits width) :=
  anyExpression (List.ofFn fun length : Fin (width+1) =>
    if position<length.val then .input (length.natAdd width) else .const false)

theorem queryCellExpression_eval (width position : ℕ) (word : List Bool) (hw : word.length ≤ width) :
    (queryCellExpression width position).eval (queryWordEncoding width word)=word.getD position false := by
  unfold queryCellExpression
  split
  · simp only [BoolExpr.eval,queryWordEncoding,Fin.addCases_left]
  · rename_i h
    have hp : word.length ≤ position := by omega
    simp [BoolExpr.eval,List.getD_eq_getElem?_getD,List.getElem?_eq_none hp]

theorem queryAllocatedExpression_eval (width position : ℕ) (word : List Bool)
    (hw : word.length ≤ width) :
    (queryAllocatedExpression width position).eval (queryWordEncoding width word)=
      decide (position<word.length) := by
  apply Bool.eq_iff_iff.mpr
  simp only [queryAllocatedExpression,anyExpression_true,List.mem_ofFn,exists_exists_eq_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨length,hl⟩
    split at hl
    · rename_i hp
      have he : word.length=length.val := by simpa [BoolExpr.eval,queryWordEncoding] using hl
      omega
    · simp [BoolExpr.eval] at hl
  · intro hp
    refine ⟨⟨word.length,Nat.lt_succ_of_le hw⟩,?_⟩
    simp only [hp,↓reduceIte,BoolExpr.eval,queryWordEncoding,Fin.addCases_right,decide_true]

theorem queryCellExpression_operations (width position : ℕ) :
    expressionOperations (queryCellExpression width position) ≤ 1 := by
  unfold queryCellExpression
  split <;> simp [expressionOperations]

theorem queryAllocatedExpression_operations (width position : ℕ) :
    expressionOperations (queryAllocatedExpression width position) ≤ 2*width+3 := by
  have h := anyExpression_operations (n := queryWordBits width)
    (List.ofFn fun length : Fin (width+1) =>
      if position<length.val then BoolExpr.input (length.natAdd width) else .const false) 1 (by
      intro e he
      obtain ⟨length,rfl⟩ := List.mem_ofFn.mp he
      split <;> simp [expressionOperations])
  change expressionOperations (queryAllocatedExpression width position) ≤ _ at h
  simp only [List.length_ofFn] at h
  convert h using 1
  omega

def queryPrefixExpression (width count : ℕ) : BoolExpr (queryWordBits width) :=
  prefixExpression (queryCellExpression width) (queryAllocatedExpression width) count 0

theorem queryPrefixExpression_eval (width count : ℕ) (word : List Bool)
    (hw : word.length ≤ width) :
    (queryPrefixExpression width count).eval (queryWordEncoding width word)=framePrefix count word := by
  simpa [queryPrefixExpression] using prefixExpression_eval
    (queryCellExpression width) (queryAllocatedExpression width) (queryWordEncoding width word) word
    (fun j => queryCellExpression_eval width j word hw)
    (fun j => queryAllocatedExpression_eval width j word hw) count 0

theorem queryPrefixExpression_operations (width count : ℕ) :
    expressionOperations (queryPrefixExpression width count) ≤ 2*count+2*width+6 := by
  have h := prefixExpression_operations (queryCellExpression width) (queryAllocatedExpression width)
    1 (2*width+3) (queryCellExpression_operations width) (queryAllocatedExpression_operations width) count 0
  simpa [queryPrefixExpression,Nat.mul_comm,Nat.add_assoc] using h

end NearCubicGates.Adapters.Compile.OracleExecution
