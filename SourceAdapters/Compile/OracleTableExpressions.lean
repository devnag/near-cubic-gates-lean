import SourceAdapters.Compile.OracleClockEncoding

/-!
proof of `thm:short-pcp-ours`, Step 4: choose explicit transition formulas using the program's fixed
control/read table. Only s*2^t rows are enumerated, with s,t fixed before the
compiler coefficient; tape configurations are never enumerated. Bodies may
read the extra allocation/clock wires of the finite state.
The table selectors use the extended input-wire domain.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def clockControlSelection (p : OrdinaryOracleProgram) (width cap : ℕ)
    (values : Fin p.base.stateCount → BoolExpr (clockBits p width cap)) :
    BoolExpr (clockBits p width cap) :=
  anyExpression (List.ofFn fun state =>
    .and (.input (clockViewIndex (controlIndex state))) (values state))

theorem clockControlSelection_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) (values : Fin p.base.stateCount → BoolExpr (clockBits p width cap)) :
    (clockControlSelection p width cap values).eval a.encode=
      (values a.window.view.control).eval a.encode := by
  apply Bool.eq_iff_iff.mpr
  simp [clockControlSelection,BoolExpr.eval,Window.observed,MachineWindow.ofConfiguration,Window.unpack]

def clockTableSelection (p : OrdinaryOracleProgram) (width cap : ℕ)
    (values : Fin p.base.stateCount → (Fin p.base.tapeCount → Bool) → BoolExpr (clockBits p width cap)) :
    BoolExpr (clockBits p width cap) :=
  anyExpression (List.ofFn fun state : Fin p.base.stateCount =>
    anyExpression (List.ofFn fun mask : Fin (2^p.base.tapeCount) =>
      .and (renameExpression clockViewIndex (rowExpression state (scanMask mask)))
        (values state (scanMask mask))))

theorem clockTableSelection_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap)
    (values : Fin p.base.stateCount → (Fin p.base.tapeCount → Bool) → BoolExpr (clockBits p width cap)) :
    (clockTableSelection p width cap values).eval a.encode=
      (values a.window.view.control a.window.unpack.scanned).eval a.encode := by
  have hv : (fun i => a.encode (clockViewIndex i))=a.window.observed.encode :=
    funext a.encode_view
  apply Bool.eq_iff_iff.mpr
  simp only [clockTableSelection,anyExpression_true,List.mem_ofFn,exists_exists_eq_and,
    BoolExpr.eval,Bool.and_eq_true,renameExpression_eval,hv,rowExpression_eval]
  constructor
  · rintro ⟨state,mask,⟨hs,hm⟩,hx⟩
    have hc : a.window.observed.control=a.window.view.control := rfl
    have hsc : a.window.observed.scanned=a.window.unpack.scanned :=
      (MachineWindow.ofConfiguration_represents _ _).scanned
    simpa [←hs,hm,hc,hsc] using hx
  · intro hx
    obtain ⟨mask,hm⟩ := scanMask_surjective p.base.tapeCount a.window.observed.scanned
    refine ⟨a.window.observed.control,mask,⟨rfl,hm⟩,?_⟩
    have hsc : a.window.observed.scanned=a.window.unpack.scanned :=
      (MachineWindow.ofConfiguration_represents _ _).scanned
    have hc : a.window.observed.control=a.window.view.control := rfl
    simpa only [hm,hsc,hc] using hx

theorem clockTableSelection_operations (p : OrdinaryOracleProgram) (width cap : ℕ)
    (values : Fin p.base.stateCount → (Fin p.base.tapeCount → Bool) → BoolExpr (clockBits p width cap))
    (bound : ℕ) (h : ∀ q scans, expressionOperations (values q scans) ≤ bound) :
    expressionOperations (clockTableSelection p width cap values) ≤
      p.base.stateCount*(2^p.base.tapeCount*(p.base.tapeCount*(2*width+3)+2+bound+2)+2)+1 := by
  unfold clockTableSelection
  apply (anyExpression_operations _
    (2^p.base.tapeCount*(p.base.tapeCount*(2*width+3)+2+bound+2)+1) ?_).trans (by simp)
  intro e he
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp he
  apply (anyExpression_operations _ (p.base.tapeCount*(2*width+3)+2+bound+1) ?_).trans (by simp)
  intro e he
  obtain ⟨mask,rfl⟩ := List.mem_ofFn.mp he
  simp only [expressionOperations,renameExpression_operations]
  have hr := rowExpression_operations (s := p.base.stateCount) (width := width) q (scanMask mask)
  have hb := h q (scanMask mask)
  omega

end NearCubicGates.Adapters.Compile.OracleExecution
