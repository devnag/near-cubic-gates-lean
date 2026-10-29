import SourceAdapters.Compile.BoundedTransition
import SourceAdapters.Compile.BoundedRounds

/-!
proof of `lem:multitape-refuter`, Step 3: the literal bounded transition circuit schedule.
A missing transition or out-of-window head maps to all-zero control, which
is absorbing. A real halt remains unchanged. These are semantic constructions,
not assumptions that the desired source compiler or uniform generator exists.
-/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

/-- All-zero is the explicit failed-run value. -/
def encodeWindowOption {t s width : ℕ} :
    Option (MachineWindow t s width) → BitInput (windowBits t s width)
  | none => fun _ => false
  | some a => a.encode

/-- The next bit is selected from the actual finite rule table. -/
def transitionExpression {t s width : ℕ} (machine : Machine t s)
    (index : Fin (windowBits t s width)) : BoolExpr (windowBits t s width) :=
  tableSelection (fun state scans =>
    if machine.halted state then .input index else
      match machine.rule state scans with
      | none => .const false
      | some action => .and (actionFitsExpression action) (actionExpression action index))

@[simp] theorem transitionExpression_eval {t s width : ℕ} (machine : Machine t s)
    (a : MachineWindow t s width) (index : Fin (windowBits t s width)) :
    (transitionExpression machine index).eval a.encode =
      encodeWindowOption (a.advance machine) index := by
  rw [transitionExpression, tableSelection_eval]
  unfold MachineWindow.advance
  split
  · simp_all [BoolExpr.eval, encodeWindowOption]
  · cases hr : machine.rule a.control a.scanned with
    | none => simp [ BoolExpr.eval, encodeWindowOption]
    | some action =>
        by_cases hfit : ∀ tape, (action.move tape).apply (a.heads tape).val < width
        · have hfits : (actionFitsExpression action).eval a.encode = true :=
            (actionFitsExpression_eval a action).mpr hfit
          simp [ hfit, BoolExpr.eval, hfits, actionExpression_eval, encodeWindowOption]
        · have hfits : (actionFitsExpression action).eval a.encode = false := by
            exact Bool.eq_false_iff.mpr (by simpa using hfit)
          simp [ hfit, BoolExpr.eval, hfits, encodeWindowOption]

@[simp] theorem transitionExpression_dead {t s width : ℕ} (machine : Machine t s)
    (index : Fin (windowBits t s width)) :
    (transitionExpression machine index).eval (fun _ => false) = false := by
  apply Bool.eq_false_iff.mpr
  simp [transitionExpression, tableSelection, BoolExpr.eval, rowExpression]

/-- Evaluate the fixed local vector for exactly the clocked number of rounds. -/
def transitionRounds {t s width : ℕ} (machine : Machine t s) :
    ℕ → BitInput (windowBits t s width) → BitInput (windowBits t s width)
  | 0, input => input
  | fuel + 1, input => transitionRounds machine fuel
      (fun index => (transitionExpression machine index).eval input)

@[simp] theorem transitionRounds_dead {t s width : ℕ} (machine : Machine t s)
    (fuel : ℕ) : @transitionRounds t s width machine fuel (fun _ => false) = fun _ => false := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [transitionRounds] using ih

/-- Exact state-vector semantics of the fixed transition schedule. -/
theorem transitionRounds_correct {t s width : ℕ} (machine : Machine t s)
    (fuel : ℕ) (a : MachineWindow t s width) :
    transitionRounds machine fuel a.encode = encodeWindowOption (a.rounds machine fuel) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
      simp only [transitionRounds, transitionExpression_eval, MachineWindow.rounds]
      cases ha : a.advance machine with
      | none => simp [encodeWindowOption]
      | some b => simpa [encodeWindowOption] using ih b

/-- The checked shared-DAG schedule, retaining prior round outputs as wires. -/
def compileTransitionRounds {n t s width : ℕ} (machine : Machine t s)
    (builder : BooleanDAGBuilder n) (wires : Fin (windowBits t s width) → LiveWire builder) :
    (fuel : ℕ) → CompiledValues builder (windowBits t s width)
      (fun index input => transitionRounds machine fuel
        (fun i => (wires i).function input) index)
  | 0 =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        output := fun i => (wires i).output
        correct := fun i input => (wires i).correct input }
  | fuel + 1 =>
      let first := compileVectorOnWires builder wires (windowBits t s width)
        (transitionExpression machine)
      let rest := compileTransitionRounds machine first.final first.live fuel
      { final := rest.final
        extension := first.extension.trans rest.extension
        output := rest.output
        correct := rest.correct }

/-- Given the concrete per-bit local-operation bound, fuel scales DAG size
linearly. The local bound is arithmetic about the explicit expression above. -/
theorem compileTransitionRounds_added_le {n t s width : ℕ} (machine : Machine t s)
    (fuel : ℕ) (builder : BooleanDAGBuilder n)
    (wires : Fin (windowBits t s width) → LiveWire builder) (bound : ℕ)
    (hbound : ∀ index : Fin (windowBits t s width), expressionOperations (transitionExpression machine index) ≤ bound) :
    (compileTransitionRounds machine builder wires fuel).extension.suffix.length ≤
      fuel * (windowBits t s width * bound) := by
  induction fuel generalizing builder with
  | zero => simp [compileTransitionRounds, BooleanDAGExtension.refl]
  | succ fuel ih =>
      let first := compileVectorOnWires builder wires (windowBits t s width)
        (transitionExpression machine)
      have hfirst := compileVectorOnWires_added_le (windowBits t s width)
        builder wires (transitionExpression machine) bound hbound
      have hrest := ih first.final first.live
      simp only [compileTransitionRounds, BooleanDAGExtension.trans, List.length_append]
      change first.extension.suffix.length +
        (compileTransitionRounds machine first.final first.live fuel).extension.suffix.length ≤ _
      change first.extension.suffix.length ≤ _ at hfirst
      nlinarith

end NearCubicGates.Adapters.Compile
