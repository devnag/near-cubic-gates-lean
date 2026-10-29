import SourceAdapters.Compile.OracleLengthExpressions

/-!
proof of `thm:short-pcp-ours`, Step 4: the complete local-action vector, including exact allocated
lengths and the paid unit clock decrement. Its head/cell/control formulas
reuse the already checked literal ordinary-machine action expressions.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

theorem window_representation_unique {t s width : ℕ} {a b : MachineWindow t s width}
    {c : Configuration t s} (ha : a.Represents c) (hb : b.Represents c) : a=b := by
  cases a with
  | mk qa headsA cellsA =>
    cases b with
    | mk qb headsB cellsB =>
      have hq : qa=qb := ha.control.trans hb.control.symm
      have hh : headsA=headsB := by
        funext tape
        exact Fin.ext ((ha.heads tape).trans (hb.heads tape).symm)
      have ht : cellsA=cellsB := by
        funext tape position
        exact (ha.cells tape position).trans (hb.cells tape position).symm
      cases hq; cases hh; cases ht
      rfl

theorem actionWindow_fits {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (action : Action p.base.tapeCount p.base.stateCount)
    (hfit : ∀ tape, (action.move tape).apply (a.window.observed.heads tape).val < width) :
    Fits width (applyAction a.window.unpack action) := by
  constructor
  · exact hfit
  · intro tape
    have ht := a.window.unpack_fits.2 tape
    have hh := a.window.unpack_fits.1 tape
    simp only [applyAction]
    cases hw : action.write tape
    · exact ht
    · simp only [RepairOrdinary.RecoveryTapeSupport.write_length]
      omega

def localState {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (action : Action p.base.tapeCount p.base.stateCount)
    (hfit : ∀ tape, (action.move tape).apply (a.window.observed.heads tape).val < width) :
    ClockState p width cap :=
  ⟨Window.pack (applyAction a.window.unpack action) (actionWindow_fits a action hfit),
    ⟨a.remaining.val-1,by have := a.remaining.isLt; omega⟩⟩

theorem localState_observed {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (action : Action p.base.tapeCount p.base.stateCount)
    (hfit : ∀ tape, (action.move tape).apply (a.window.observed.heads tape).val < width) :
    (localState a action hfit).window.observed=a.window.observed.apply action hfit := by
  apply window_representation_unique (c := applyAction a.window.unpack action)
  · have h := MachineWindow.ofConfiguration_represents
      (localState a action hfit).window.unpack (localState a action hfit).window.unpack_fits.1
    change (localState a action hfit).window.observed.Represents
      (Window.pack (applyAction a.window.unpack action) (actionWindow_fits a action hfit)).unpack at h
    rwa [Window.unpack_pack] at h
  · exact (MachineWindow.ofConfiguration_represents _ _).apply action hfit

def localRemainingExpression (p : OrdinaryOracleProgram) (width cap : ℕ)
    (target : Fin (cap+1)) : BoolExpr (clockBits p width cap) :=
  if h : target.val+1<cap+1 then .input (clockBudgetIndex ⟨target.val+1,h⟩) else .const false

theorem localRemainingExpression_eval {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (target : Fin (cap+1)) (hp : 0<a.remaining.val) :
    (localRemainingExpression p width cap target).eval a.encode=
      decide (a.remaining.val-1=target.val) := by
  unfold localRemainingExpression
  split
  · rename_i ht
    simp only [BoolExpr.eval,ClockState.encode_budget,Fin.ext_iff]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · rename_i ht
    have he : a.remaining.val-1 ≠ target.val := by
      have := a.remaining.isLt
      omega
    simp [BoolExpr.eval,he]

def localActionExpression (p : OrdinaryOracleProgram) (width cap : ℕ)
    (action : Action p.base.tapeCount p.base.stateCount) :
    Fin (clockBits p width cap) → BoolExpr (clockBits p width cap) :=
  Fin.addCases
    (fun index => renameExpression clockViewIndex (actionExpression action index))
    (Fin.addCases
      (fun index => let pair := finProdFinEquiv.symm index
        actionLengthExpression action pair.1 pair.2)
      (localRemainingExpression p width cap))

theorem localActionExpression_eval {p : OrdinaryOracleProgram} {width cap : ℕ}
    (a : ClockState p width cap) (action : Action p.base.tapeCount p.base.stateCount)
    (hfit : ∀ tape, (action.move tape).apply (a.window.observed.heads tape).val < width)
    (hp : 0<a.remaining.val) (index : Fin (clockBits p width cap)) :
    (localActionExpression p width cap action index).eval a.encode=
      (localState a action hfit).encode index := by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) index
  · intro i
    simp only [localActionExpression,Fin.addCases_left,renameExpression_eval]
    have hv : (fun j => a.encode (clockViewIndex j))=a.window.observed.encode := funext a.encode_view
    rw [hv,actionExpression_eval _ _ hfit]
    change _=(localState a action hfit).encode (clockViewIndex i)
    rw [ClockState.encode_view,localState_observed]
  · intro pair
    simp only [localActionExpression,Fin.addCases_left,Fin.addCases_right,actionLengthExpression_eval,
      ClockState.encode]
    simp only [localState,Window.pack,Fin.ext_iff]
  · intro target
    simp only [localActionExpression,Fin.addCases_right,localRemainingExpression_eval a target hp,
      ClockState.encode,localState,Fin.ext_iff]

end NearCubicGates.Adapters.Compile.OracleExecution
