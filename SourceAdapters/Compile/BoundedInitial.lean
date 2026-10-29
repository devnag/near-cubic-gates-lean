import SourceAdapters.Compile.BoundedSizes
import Proof.Gates.Cells.CompK

/-!
proof of `lem:multitape-refuter`, Step 3: the bounded verifier circuit starts with the actual framed
input/witness tapes. Only clock+1 tape cells are needed because every head
starts at zero. A witness payload cell is an input gate, never a guessed
truth-table value. -/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

/-- Compile an initial vector of expressions over actual external inputs. -/
def compileExternalVector {n : ℕ} (builder : BooleanDAGBuilder n) :
    (count : ℕ) → (expressions : Fin count → BoolExpr n) →
      CompiledValues builder count (fun index input => (expressions index).eval input)
  | 0, _ =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        output := Fin.elim0
        correct := fun index => Fin.elim0 index }
  | count + 1, expressions =>
      let first := compileExpr builder (expressions 0)
      let rest := compileExternalVector first.final count (fun i => expressions i.succ)
      { final := rest.final
        extension := first.extension.trans rest.extension
        output := Fin.cases (rest.extension.lift first.output) rest.output
        correct := by
          intro index
          refine Fin.cases ?_ ?_ index
          · intro input
            exact (rest.extension.wireValue_lift input first.output).trans (first.correct input)
          · intro i input
            exact rest.correct i input }

theorem compileExternalVector_added_le {n : ℕ} (count : ℕ)
    (builder : BooleanDAGBuilder n) (expressions : Fin count → BoolExpr n)
    (bound : ℕ) (hbound : ∀ i, (expressions i).nodeCount ≤ bound) :
    (compileExternalVector builder count expressions).extension.suffix.length ≤ count * bound := by
  induction count generalizing builder with
  | zero => simp [compileExternalVector, BooleanDAGExtension.refl]
  | succ count ih =>
      let first := compileExpr builder (expressions 0)
      have hrest := ih first.final (fun i => expressions i.succ) (fun i => hbound i.succ)
      have hfirst := hbound 0
      simp only [compileExternalVector, BooleanDAGExtension.trans, List.length_append]
      change first.extension.suffix.length +
        (compileExternalVector first.final count (fun i => expressions i.succ)).extension.suffix.length ≤ _
      rw [show first.extension.suffix.length = (expressions 0).nodeCount from compileExpr_addedNodes _ _]
      nlinarith

def witnessFrameExpression {n : ℕ} (position : ℕ) : BoolExpr n :=
  if position % 2 = 0 then .const (decide (position / 2 < n))
  else if h : position / 2 < n then .input ⟨position / 2, h⟩ else .const false

@[simp] theorem witnessFrameExpression_eval {n : ℕ} (witness : BitInput n) (position : ℕ) :
    (witnessFrameExpression position).eval witness =
      readTapeBit (frame (List.ofFn witness)) position := by
  rw [NearCubicGates.Close.Cells.frame_read]
  unfold witnessFrameExpression
  split
  · simp [BoolExpr.eval]
  · split
    · next h => simp [BoolExpr.eval, List.getD_eq_getElem?_getD, h]
    · next h => simp [BoolExpr.eval, List.getD_eq_getElem?_getD, h]

@[simp] theorem witnessFrameExpression_nodes {n : ℕ} (position : ℕ) :
    (@witnessFrameExpression n position).nodeCount = 1 := by
  unfold witnessFrameExpression
  split
  · rfl
  · split <;> rfl

def verifierInitialWindow (v : Verifier) (input : List Bool) {n : ℕ}
    (witness : BitInput n) (fuel : ℕ) : MachineWindow v.tapeCount v.stateCount (fuel+1) :=
  MachineWindow.ofConfiguration
    (initialConfiguration v.machine (v.inputTapes input (List.ofFn witness))) (by
      intro tape
      simp [initialConfiguration])

def verifierInitialExpression (v : Verifier) (input : List Bool) (n fuel : ℕ) :
    Fin (windowBits v.tapeCount v.stateCount (fuel+1)) → BoolExpr n :=
  Fin.addCases (fun state => .const (decide (v.machine.start = state)))
    (Fin.addCases
      (fun index => .const (decide ((finProdFinEquiv.symm index).2.val = 0)))
      (fun index => let pair := finProdFinEquiv.symm index
        if pair.1.val = 0 then .const (readTapeBit (frame input) pair.2.val)
        else if pair.1.val = 1 then witnessFrameExpression pair.2.val else .const false))

@[simp] theorem verifierInitialExpression_eval (v : Verifier) (input : List Bool)
    {n : ℕ} (witness : BitInput n) (fuel : ℕ)
    (index : Fin (windowBits v.tapeCount v.stateCount (fuel+1))) :
    (verifierInitialExpression v input n fuel index).eval witness =
      (verifierInitialWindow v input witness fuel).encode index := by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) index
  · intro state
    simp [verifierInitialExpression, verifierInitialWindow, MachineWindow.encode,
      MachineWindow.ofConfiguration, initialConfiguration, BoolExpr.eval]
  · intro pair
    simp only [verifierInitialExpression, verifierInitialWindow, MachineWindow.encode,
      MachineWindow.ofConfiguration, initialConfiguration, Fin.addCases_left,
      Fin.addCases_right, BoolExpr.eval, Fin.ext_iff]
    simp [eq_comm]
  · intro pair
    simp only [verifierInitialExpression, verifierInitialWindow, MachineWindow.encode,
      MachineWindow.ofConfiguration, initialConfiguration, Fin.addCases_right,
      Verifier.inputTapes]
    split
    · rfl
    · split
      · exact witnessFrameExpression_eval _ _
      · simp [BoolExpr.eval, readTapeBit]

@[simp] theorem verifierInitialExpression_nodes (v : Verifier) (input : List Bool)
    (n fuel : ℕ) (index : Fin (windowBits v.tapeCount v.stateCount (fuel+1))) :
    (verifierInitialExpression v input n fuel index).nodeCount = 1 := by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) index
  · intro state; simp [verifierInitialExpression, BoolExpr.nodeCount]
  · intro pair; simp [verifierInitialExpression, BoolExpr.nodeCount]
  · intro pair
    simp only [verifierInitialExpression, Fin.addCases_right]
    split
    · rfl
    · split
      · exact witnessFrameExpression_nodes _
      · rfl

/-- The clock-sized window starts from exactly the ordinary framed source. -/
theorem verifierInitialWindow_accepted (v : Verifier) (input : List Bool)
    {n : ℕ} (witness : BitInput n) (fuel : ℕ) :
    (verifierInitialWindow v input witness fuel).accepted v.machine v.accepting fuel = true ↔
      v.acceptsAt fuel input (List.ofFn witness) := by
  exact MachineWindow.accepted_iff v.machine v.accepting fuel
    (MachineWindow.ofConfiguration_represents _ _) (by intro tape; simp [initialConfiguration])

end NearCubicGates.Adapters.Compile
