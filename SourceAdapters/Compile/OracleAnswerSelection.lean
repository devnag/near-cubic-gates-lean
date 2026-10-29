import SourceAdapters.Compile.OracleQueryAction
import SourceAdapters.Compile.OracleTableExpressions

/-!
proof of `thm:short-pcp-ours`, Step 4: select the literal fixed program table after appending one actual
oracle-answer wire. The read/control selectors still use only old state wires.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def answerTableSelection (p : OrdinaryOracleProgram) (width cap : ℕ)
    (values : Fin p.base.stateCount → (Fin p.base.tapeCount → Bool) →
      BoolExpr (clockBits p width cap+1)) : BoolExpr (clockBits p width cap+1) :=
  anyExpression (List.ofFn fun state : Fin p.base.stateCount =>
    anyExpression (List.ofFn fun mask : Fin (2^p.base.tapeCount) =>
      .and (liftClockExpression (renameExpression clockViewIndex (rowExpression state (scanMask mask))))
        (values state (scanMask mask))))

theorem answerTableSelection_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) (answer : Bool)
    (values : Fin p.base.stateCount → (Fin p.base.tapeCount → Bool) →
      BoolExpr (clockBits p width cap+1)) :
    (answerTableSelection p width cap values).eval (answerEncoding a answer)=
      (values a.window.view.control a.window.unpack.scanned).eval (answerEncoding a answer) := by
  have hv : (fun i => a.encode (clockViewIndex i))=a.window.observed.encode := funext a.encode_view
  have hc : a.window.observed.control=a.window.view.control := rfl
  have hsc : a.window.observed.scanned=a.window.unpack.scanned :=
    (MachineWindow.ofConfiguration_represents _ _).scanned
  apply Bool.eq_iff_iff.mpr
  simp only [answerTableSelection,anyExpression_true,List.mem_ofFn,exists_exists_eq_and,
    BoolExpr.eval,Bool.and_eq_true,liftClockExpression_eval,renameExpression_eval,hv,rowExpression_eval]
  constructor
  · rintro ⟨state,mask,⟨hs,hm⟩,hx⟩
    simpa only [←hs,hm,hc,hsc] using hx
  · intro hx
    obtain ⟨mask,hm⟩ := scanMask_surjective p.base.tapeCount a.window.observed.scanned
    refine ⟨a.window.observed.control,mask,⟨rfl,hm⟩,?_⟩
    simpa only [hm,hsc,hc] using hx

theorem answerTableSelection_dead (p : OrdinaryOracleProgram) (width cap : ℕ) (answer : Bool)
    (values : Fin p.base.stateCount → (Fin p.base.tapeCount → Bool) →
      BoolExpr (clockBits p width cap+1)) :
    (answerTableSelection p width cap values).eval
      (Fin.addCases (fun _ : Fin (clockBits p width cap) => false) (fun _ : Fin 1 => answer))=false := by
  apply Bool.eq_false_iff.mpr
  simp [answerTableSelection,liftClockExpression,renameExpression_eval,rowExpression,BoolExpr.eval]

end NearCubicGates.Adapters.Compile.OracleExecution
