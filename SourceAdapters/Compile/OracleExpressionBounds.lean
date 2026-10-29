import SourceAdapters.Compile.OracleTransition

/-!
proof of `thm:short-pcp-ours`, Step 4: explicit polynomial operation bounds for the full charged
transition formulas. Program table dimensions are fixed before the request.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def localActionBound (width : ℕ) := 3*width+6+(width+1)*(3*width+3)
def queryActionBound (width : ℕ) := 6+(4*width+6)*(6*width+3)
def localGuardBound (t width cap : ℕ) := 2*(cap+1)+t*(3*width+2)+3
def queryGuardBound (width cap : ℕ) := 2+(4*width+6)*(2*((cap+1)*(3*width+2)+1)+1)
def transitionBodyBound (t width cap : ℕ) :=
  localActionBound width+queryActionBound width+localGuardBound t width cap+queryGuardBound width cap+1
def clockTransitionBound (t s width cap : ℕ) :=
  s*(2^t*(t*(2*width+3)+2+transitionBodyBound t width cap+2)+2)+1

theorem localActionExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ)
    (action : Action p.base.tapeCount p.base.stateCount) (index : Fin (clockBits p width cap)) :
    expressionOperations (localActionExpression p width cap action index) ≤ localActionBound width := by
  refine Fin.addCases ?_ ?_ index
  · intro i
    simp only [localActionExpression,Fin.addCases_left,renameExpression_operations]
    have h := actionExpression_operations action i
    unfold localActionBound
    omega
  · intro extra
    refine Fin.addCases ?_ ?_ extra
    · intro pair
      simp only [localActionExpression,Fin.addCases_left,Fin.addCases_right]
      have h := actionLengthExpression_operations (cap := cap) action
        (finProdFinEquiv.symm pair).1 (finProdFinEquiv.symm pair).2
      unfold localActionBound
      omega
    · intro budget
      simp only [localActionExpression,Fin.addCases_right,localRemainingExpression]
      split
      · simp [expressionOperations]
      · change 1 ≤ localActionBound width
        unfold localActionBound
        omega

theorem liftClockExpression_operations {p : OrdinaryOracleProgram} {width cap : ℕ}
    (e : BoolExpr (clockBits p width cap)) :
    expressionOperations (liftClockExpression e)=expressionOperations e :=
  renameExpression_operations _ _

theorem queryActionExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ)
    (rule : OracleReturn p.base.stateCount) (index : Fin (clockBits p width cap)) :
    expressionOperations (queryActionExpression p width cap rule index) ≤ queryActionBound width := by
  refine Fin.addCases ?_ ?_ index
  · intro view
    refine Fin.addCases ?_ ?_ view
    · intro q
      simp [queryActionExpression,expressionOperations,answerExpression,queryActionBound]
    · intro rest
      simp [queryActionExpression,expressionOperations,queryActionBound]
  · intro extra
    refine Fin.addCases ?_ ?_ extra
    · intro pair
      simp [queryActionExpression,expressionOperations,queryActionBound]
    · intro budget
      simp only [queryActionExpression,Fin.addCases_right,liftClockExpression_operations]
      have h := clockRemainingExpression_operations p width cap budget
      unfold queryActionBound
      omega

theorem positiveClockExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ) :
    expressionOperations (positiveClockExpression p width cap) ≤ 2*(cap+1)+1 := by
  unfold positiveClockExpression
  apply (anyExpression_operations _ 1 ?_).trans (by simp [Nat.mul_comm])
  intro e he
  obtain ⟨budget,rfl⟩ := List.mem_ofFn.mp he
  split <;> simp [expressionOperations]

theorem localGuardExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ)
    (action : Action p.base.tapeCount p.base.stateCount) :
    expressionOperations (localGuardExpression p width cap action) ≤
      localGuardBound p.base.tapeCount width cap := by
  simp only [localGuardExpression,expressionOperations,renameExpression_operations]
  have ha := actionFitsExpression_operations (width := width) action
  have hp := positiveClockExpression_operations p width cap
  unfold localGuardBound
  omega

theorem clockAffordableExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ) :
    expressionOperations (clockAffordableExpression p width cap) ≤
      (4*width+6)*(2*((cap+1)*(3*width+2)+1)+1) := by
  have h := substituteExpression_operations (chargeSubstitution p width cap)
    (queryAffordableExpression width cap) (4*width+6) (by omega)
    (chargeSubstitution_operations p width cap)
  have hq : expressionOperations (queryAffordableExpression width cap) ≤ (cap+1)*(3*width+2)+1 := by
    unfold queryAffordableExpression
    apply (anyExpression_operations _ (3*width+1) ?_).trans (by simp)
    intro e he
    obtain ⟨target,rfl⟩ := List.mem_ofFn.mp he
    exact queryRemainingExpression_operations width cap target
  have hn := expression_nodes_le_operations (queryAffordableExpression width cap)
  change expressionOperations (clockAffordableExpression p width cap) ≤ _ at h
  nlinarith

theorem queryGuardExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ) :
    expressionOperations (queryGuardExpression p width cap) ≤ queryGuardBound width cap := by
  have h := clockAffordableExpression_operations p width cap
  have hr : expressionOperations (rewoundExpression p width cap) ≤ 1 := by
    unfold rewoundExpression
    split <;> simp [expressionOperations]
  simp only [queryGuardExpression,expressionOperations]
  unfold queryGuardBound
  omega

theorem answerTableSelection_operations (p : OrdinaryOracleProgram) (width cap : ℕ)
    (values : Fin p.base.stateCount → (Fin p.base.tapeCount → Bool) → BoolExpr (clockBits p width cap+1))
    (bound : ℕ) (h : ∀ q scans, expressionOperations (values q scans) ≤ bound) :
    expressionOperations (answerTableSelection p width cap values) ≤
      p.base.stateCount*(2^p.base.tapeCount*(p.base.tapeCount*(2*width+3)+2+bound+2)+2)+1 := by
  unfold answerTableSelection
  apply (anyExpression_operations _
    (2^p.base.tapeCount*(p.base.tapeCount*(2*width+3)+2+bound+2)+1) ?_).trans (by simp)
  intro e he
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp he
  apply (anyExpression_operations _ (p.base.tapeCount*(2*width+3)+2+bound+1) ?_).trans (by simp)
  intro e he
  obtain ⟨mask,rfl⟩ := List.mem_ofFn.mp he
  simp only [expressionOperations,liftClockExpression_operations,renameExpression_operations]
  have hr := rowExpression_operations (s := p.base.stateCount) (width := width) q (scanMask mask)
  have hb := h q (scanMask mask)
  omega

theorem clockTransitionExpression_operations (p : OrdinaryOracleProgram) (width cap : ℕ)
    (index : Fin (clockBits p width cap)) :
    expressionOperations (clockTransitionExpression p width cap index) ≤
      clockTransitionBound p.base.tapeCount p.base.stateCount width cap := by
  unfold clockTransitionExpression clockTransitionBound
  apply answerTableSelection_operations
  intro q scans
  split
  · simp [expressionOperations]
  · split
    · split
      · simp [expressionOperations,transitionBodyBound]
      · rename_i action _
        simp only [expressionOperations,liftClockExpression_operations]
        have ha := localActionExpression_operations p width cap action index
        have hg := localGuardExpression_operations p width cap action
        unfold transitionBodyBound
        omega
    · rename_i rule _
      simp only [expressionOperations,liftClockExpression_operations]
      have ha := queryActionExpression_operations p width cap rule index
      have hg := queryGuardExpression_operations p width cap
      unfold transitionBodyBound
      omega

end NearCubicGates.Adapters.Compile.OracleExecution
