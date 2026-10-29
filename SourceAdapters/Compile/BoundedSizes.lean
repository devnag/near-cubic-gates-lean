import SourceAdapters.Compile.BoundedSchedule

/-!
proof of `lem:multitape-refuter`, Step 3: actual operation counts for finite transition
expressions, and the clock-linear shared-DAG bound. The full read-symbol
transition table is charged explicitly by s*2^t, as in verifier code.
The added-node equality and vector bound charge every emitted node.
-/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

theorem anyExpression_operations {n : ℕ} (expressions : List (BoolExpr n)) (bound : ℕ)
    (h : ∀ e ∈ expressions, expressionOperations e ≤ bound) :
    expressionOperations (anyExpression expressions) ≤ expressions.length * (bound + 1) + 1 := by
  induction expressions with
  | nil => simp [anyExpression, expressionOperations]
  | cons e rest ih =>
      have he := h e (by simp)
      have hr := ih (fun x hx => h x (by simp [hx]))
      simp only [anyExpression, expressionOperations, List.length_cons]
      nlinarith

theorem allExpression_operations {n : ℕ} (expressions : List (BoolExpr n)) (bound : ℕ)
    (h : ∀ e ∈ expressions, expressionOperations e ≤ bound) :
    expressionOperations (allExpression expressions) ≤ expressions.length * (bound + 1) + 1 := by
  induction expressions with
  | nil => simp [allExpression, expressionOperations]
  | cons e rest ih =>
      have he := h e (by simp)
      have hr := ih (fun x hx => h x (by simp [hx]))
      simp only [allExpression, expressionOperations, List.length_cons]
      nlinarith

theorem headSelection_operations {t s width : ℕ} (tape : Fin t)
    (values : Fin width → BoolExpr (windowBits t s width)) (bound : ℕ)
    (h : ∀ position, expressionOperations (values position) ≤ bound) :
    expressionOperations (headSelection tape values) ≤ width * (bound + 2) + 1 := by
  unfold headSelection
  have hlist : ∀ e ∈ List.ofFn (fun position =>
      BoolExpr.and (.input (headIndex tape position)) (values position)),
      expressionOperations e ≤ bound + 1 := by
    intro e he
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp he
    simp only [expressionOperations]
    have := h position
    omega
  simpa [Nat.add_assoc] using anyExpression_operations _ (bound + 1) hlist

theorem scannedExpression_operations {t s width : ℕ} (tape : Fin t) :
    expressionOperations (@scannedExpression t s width tape) ≤ 2 * width + 1 := by
  have h := headSelection_operations (s := s) (width := width) tape
    (fun position => BoolExpr.input (cellIndex tape position)) 0 (by intro p; rfl)
  simpa [headSelection, scannedExpression, Nat.mul_comm] using h

theorem scanPatternExpression_operations {t s width : ℕ} (scans : Fin t → Bool) :
    expressionOperations (@scanPatternExpression t s width scans) ≤ t * (2 * width + 3) + 1 := by
  unfold scanPatternExpression
  have h := allExpression_operations
    (List.ofFn (fun tape : Fin t => if scans tape then
      @scannedExpression t s width tape else .not (scannedExpression tape)))
    (2 * width + 2) ?_
  · simpa using h
  · intro e he
    obtain ⟨tape, rfl⟩ := List.mem_ofFn.mp he
    have hread := scannedExpression_operations (s := s) (width := width) tape
    split
    · omega
    · simp only [expressionOperations]; omega

theorem rowExpression_operations {t s width : ℕ} (state : Fin s) (scans : Fin t → Bool) :
    expressionOperations (@rowExpression t s width state scans) ≤ t * (2 * width + 3) + 2 := by
  have h := scanPatternExpression_operations (s := s) (width := width) scans
  simp only [rowExpression, expressionOperations]
  omega

theorem actionFitsExpression_operations {t s width : ℕ} (action : Action t s) :
    expressionOperations (@actionFitsExpression t s width action) ≤ t * (3 * width + 2) + 1 := by
  unfold actionFitsExpression
  have h := allExpression_operations
    (List.ofFn (fun tape : Fin t => @headSelection t s width tape
      (fun position => .const (decide ((action.move tape).apply position.val < width)))))
    (3 * width + 1) ?_
  · simpa using h
  · intro e he
    obtain ⟨tape, rfl⟩ := List.mem_ofFn.mp he
    simpa [Nat.mul_comm] using headSelection_operations (s := s) tape
      (fun position : Fin width => BoolExpr.const (decide ((action.move tape).apply position.val < width)))
      1 (by intro p; rfl)

theorem actionExpression_operations {t s width : ℕ} (action : Action t s)
    (index : Fin (windowBits t s width)) :
    expressionOperations (actionExpression action index) ≤ 3 * width + 5 := by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) index
  · intro q
    simp [actionExpression, expressionOperations]
  · intro pair
    simp only [actionExpression, Fin.addCases_left, Fin.addCases_right]
    have h := headSelection_operations (s := s) (finProdFinEquiv.symm pair).1
      (fun old : Fin width => BoolExpr.const
        (decide ((action.move (finProdFinEquiv.symm pair).1).apply old.val =
          (finProdFinEquiv.symm pair).2.val))) 1 (by intro p; rfl)
    omega
  · intro pair
    simp only [actionExpression, Fin.addCases_right]
    unfold writtenCellExpression
    split <;> simp [expressionOperations]

def transitionBitBound (t s width : ℕ) : ℕ :=
  s * (2^t * (t * (2 * width + 3) + 2 + 4 * (t+1) * (width+2) + 2) + 2) + 1

/-- Explicit polynomial local bound in the literal transition table size. -/
theorem transitionExpression_operations {t s width : ℕ} (machine : Machine t s)
    (index : Fin (windowBits t s width)) :
    expressionOperations (transitionExpression machine index) ≤ transitionBitBound t s width := by
  unfold transitionExpression tableSelection transitionBitBound
  apply (anyExpression_operations _ (2^t *
    (t * (2*width+3)+2+4*(t+1)*(width+2)+2)+1) ?_).trans_eq
  · simp
  · intro e he
    obtain ⟨state, rfl⟩ := List.mem_ofFn.mp he
    apply (anyExpression_operations _
      (t*(2*width+3)+2+4*(t+1)*(width+2)+1) ?_).trans_eq
    · simp
    · intro e he
      obtain ⟨mask, rfl⟩ := List.mem_ofFn.mp he
      have hrow := rowExpression_operations (width := width) state (scanMask mask)
      have hvalue : expressionOperations
          (if machine.halted state then BoolExpr.input index else
            match machine.rule state (scanMask mask) with
            | none => .const false
            | some action => .and (actionFitsExpression action) (actionExpression action index)) ≤
          4*(t+1)*(width+2) := by
        split
        · simp [expressionOperations]
        · split
          · simp only [expressionOperations]; nlinarith
          · next action _ =>
            have hf := actionFitsExpression_operations (width := width) action
            have ha := actionExpression_operations action index
            simp only [expressionOperations]
            nlinarith
      change expressionOperations (rowExpression state (scanMask mask)) + _ + 1 ≤ _
      exact (Nat.add_le_add_right (Nat.add_le_add hrow hvalue) 1)

/-- proof of `lem:multitape-refuter`, Step 3: fully charged clocked schedule, with no local-bound premise. -/
theorem compileTransitionRounds_polynomial {n t s width : ℕ} (machine : Machine t s)
    (fuel : ℕ) (builder : BooleanDAGBuilder n)
    (wires : Fin (windowBits t s width) → LiveWire builder) :
    (compileTransitionRounds machine builder wires fuel).extension.suffix.length ≤
      fuel * (windowBits t s width * transitionBitBound t s width) :=
  compileTransitionRounds_added_le machine fuel builder wires _
    (transitionExpression_operations machine)

end NearCubicGates.Adapters.Compile
