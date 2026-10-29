import SourceAdapters.Compile.OracleChargedStep
import SourceAdapters.Compile.BoundedExpression

/-!
proof of `thm:short-pcp-ours`, Step 4: recognize the actual framed query using polynomial local gate
formulas. Termination is checked inside the allocated list, so an unwritten
blank cell cannot terminate a malformed query. Each payload cell is ignored
by validity and later supplies the corresponding oracle-address bit.
The recursion inspects only the even marker positions.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def framePrefix : ℕ → List Bool → Bool
  | 0, word => decide (0<word.length) && !(word.getD 0 false)
  | count+1, word => word.getD 0 false && framePrefix count (word.drop 2)

@[simp] theorem framePrefix_nil (count : ℕ) : framePrefix count []=false := by
  cases count <;> simp [framePrefix]

theorem framePrefix_append (bits padding : List Bool) :
    framePrefix bits.length (RepairOrdinary.frame bits++padding)=true := by
  induction bits with
  | nil => simp [framePrefix,RepairOrdinary.frame]
  | cons bit bits ih => simpa [framePrefix,RepairOrdinary.frame] using ih

theorem framePrefix_sound (count : ℕ) (word : List Bool) (h : framePrefix count word=true) :
    ∃ bits padding, bits.length=count ∧ word=RepairOrdinary.frame bits++padding := by
  induction count generalizing word with
  | zero =>
    cases word with
    | nil => simp at h
    | cons bit tail =>
      cases bit
      · exact ⟨[],tail,rfl,rfl⟩
      · simp [framePrefix] at h
  | succ count ih =>
    cases word with
    | nil => simp at h
    | cons marker tail =>
      cases tail with
      | nil => simp [framePrefix] at h
      | cons bit tail =>
        cases marker
        · simp [framePrefix] at h
        · have ht : framePrefix count tail=true := by simpa [framePrefix] using h
          obtain ⟨bits,padding,hlen,hword⟩ := ih tail ht
          exact ⟨bit::bits,padding,by simp [hlen],by simp [RepairOrdinary.frame,hword]⟩

theorem framePrefix_iff (count : ℕ) (word : List Bool) :
    framePrefix count word=true ↔
      ∃ bits padding, bits.length=count ∧ word=RepairOrdinary.frame bits++padding := by
  constructor
  · exact framePrefix_sound count word
  · rintro ⟨bits,padding,rfl,rfl⟩
    exact framePrefix_append bits padding

theorem framePrefix_parse (count : ℕ) (word : List Bool) :
    framePrefix count word=true ↔
      ∃ bits padding, bits.length=count ∧ parseFrame word=some (bits,padding) := by
  simp only [framePrefix_iff,parseFrame_iff]

/-- `read` selects a cell; `allocated` checks the literal stored length. -/
def prefixExpression {n : ℕ} (read allocated : ℕ → BoolExpr n) : ℕ → ℕ → BoolExpr n
  | 0, position => .and (allocated position) (.not (read position))
  | count+1, position => .and (read position) (prefixExpression read allocated count (position+2))

theorem prefixExpression_eval {n : ℕ} (read allocated : ℕ → BoolExpr n)
    (input : BitInput n) (word : List Bool)
    (hread : ∀ j, (read j).eval input=word.getD j false)
    (hlen : ∀ j, (allocated j).eval input=decide (j<word.length)) (count position : ℕ) :
    (prefixExpression read allocated count position).eval input=
      framePrefix count (word.drop position) := by
  induction count generalizing position with
  | zero =>
    simp [prefixExpression,framePrefix,BoolExpr.eval,hread,hlen,List.getD_eq_getElem?_getD]
  | succ count ih =>
    simp [prefixExpression,framePrefix,BoolExpr.eval,hread,ih,List.getD_eq_getElem?_getD,List.drop_drop]

theorem prefixExpression_operations {n : ℕ} (read allocated : ℕ → BoolExpr n)
    (readBound lengthBound : ℕ)
    (hr : ∀ j, expressionOperations (read j) ≤ readBound)
    (hl : ∀ j, expressionOperations (allocated j) ≤ lengthBound) (count position : ℕ) :
    expressionOperations (prefixExpression read allocated count position) ≤
      count*(readBound+1)+lengthBound+readBound+2 := by
  induction count generalizing position with
  | zero =>
    simp only [prefixExpression,expressionOperations]
    have := hr position
    have := hl position
    omega
  | succ count ih =>
    simp only [prefixExpression,expressionOperations]
    have := hr position
    have := ih (position+2)
    nlinarith

end NearCubicGates.Adapters.Compile.OracleExecution
