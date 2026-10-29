import SourceAdapters.Compile.OracleClockCharge

/-!
proof of `thm:short-pcp-ours`, Step 4: exact admission guards for local and oracle steps. Local work
needs one remaining tick and a fitting head update. An ask additionally needs
an allocated framed prefix, its full charge, and an already-rewound head.
Malformed queries and insufficient clocks give false, never an accepting halt.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

theorem clockAffordableExpression_true (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) :
    (clockAffordableExpression p width cap).eval a.encode=true ↔
      ∃ bits padding, a.window.unpack.tapes p.queryTape=RepairOrdinary.frame bits++padding ∧
        2*bits.length+2 ≤ a.remaining.val := by
  rw [clockAffordableExpression,substituteExpression_eval,chargeSubstitution_eval]
  simp only [queryAffordableExpression,anyExpression_true,List.mem_ofFn,exists_exists_eq_and,
    queryRemainingExpression_true]
  constructor
  · rintro ⟨target,count,hpre,hr⟩
    obtain ⟨bits,padding,hlen,hword⟩ := framePrefix_sound _ _ hpre
    exact ⟨bits,padding,hword,by omega⟩
  · rintro ⟨bits,padding,hq,hc⟩
    have hpre : framePrefix bits.length (a.window.unpack.tapes p.queryTape)=true := by
      rw [hq]; exact framePrefix_append bits padding
    refine ⟨⟨a.remaining.val-(2*bits.length+2),by have := a.remaining.isLt; omega⟩,
      ⟨bits.length,framePrefix_count_bound hpre (a.window.unpack_fits.2 _)⟩,hpre,?_⟩
    change a.remaining.val=(a.remaining.val-(2*bits.length+2))+2*bits.length+2
    omega

def rewoundExpression (p : OrdinaryOracleProgram) (width cap : ℕ) : BoolExpr (clockBits p width cap) :=
  if h : 0<width then .input (clockViewIndex (headIndex p.queryTape ⟨0,h⟩)) else .const false

theorem rewoundExpression_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) :
    (rewoundExpression p width cap).eval a.encode=decide (a.window.unpack.heads p.queryTape=0) := by
  unfold rewoundExpression
  split
  · simp only [BoolExpr.eval,ClockState.encode_view,MachineWindow.encode_head,Fin.ext_iff]
    rfl
  · have := a.window.unpack_fits.1 p.queryTape
    omega

def queryGuardExpression (p : OrdinaryOracleProgram) (width cap : ℕ) : BoolExpr (clockBits p width cap) :=
  .and (rewoundExpression p width cap) (clockAffordableExpression p width cap)

theorem queryGuardExpression_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) :
    (queryGuardExpression p width cap).eval a.encode=true ↔
      a.window.unpack.heads p.queryTape=0 ∧
      ∃ bits padding, a.window.unpack.tapes p.queryTape=RepairOrdinary.frame bits++padding ∧
        2*bits.length+2 ≤ a.remaining.val := by
  simp only [queryGuardExpression,BoolExpr.eval,Bool.and_eq_true,rewoundExpression_eval,
    decide_eq_true_eq,clockAffordableExpression_true]

def positiveClockExpression (p : OrdinaryOracleProgram) (width cap : ℕ) : BoolExpr (clockBits p width cap) :=
  anyExpression (List.ofFn fun budget : Fin (cap+1) =>
    if 0<budget.val then .input (clockBudgetIndex budget) else .const false)

theorem positiveClockExpression_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) :
    (positiveClockExpression p width cap).eval a.encode=true ↔ 0<a.remaining.val := by
  simp only [positiveClockExpression,anyExpression_true,List.mem_ofFn,exists_exists_eq_and]
  constructor
  · rintro ⟨budget,hb⟩
    split at hb
    · rename_i hp
      have he : a.remaining=budget := by simpa only [BoolExpr.eval,ClockState.encode_budget,
        decide_eq_true_eq] using hb
      rwa [he]
    · simp [BoolExpr.eval] at hb
  · intro hp
    exact ⟨a.remaining,by simp only [hp,↓reduceIte,BoolExpr.eval,ClockState.encode_budget,decide_true]⟩

def localGuardExpression (p : OrdinaryOracleProgram) (width cap : ℕ)
    (action : Action p.base.tapeCount p.base.stateCount) : BoolExpr (clockBits p width cap) :=
  .and (positiveClockExpression p width cap)
    (renameExpression clockViewIndex (actionFitsExpression action))

theorem localGuardExpression_eval (p : OrdinaryOracleProgram) (width cap : ℕ)
    (a : ClockState p width cap) (action : Action p.base.tapeCount p.base.stateCount) :
    (localGuardExpression p width cap action).eval a.encode=true ↔
      0<a.remaining.val ∧
        ∀ tape, (action.move tape).apply (a.window.observed.heads tape).val < width := by
  have hv : (fun j => a.encode (clockViewIndex j))=a.window.observed.encode := funext a.encode_view
  simp only [localGuardExpression,BoolExpr.eval,Bool.and_eq_true,positiveClockExpression_eval,
    renameExpression_eval,hv,actionFitsExpression_eval]

theorem queryGuardExpression_dead (p : OrdinaryOracleProgram) (width cap : ℕ) :
    (queryGuardExpression p width cap).eval (fun _ => false)=false := by
  unfold queryGuardExpression rewoundExpression
  split <;> simp [BoolExpr.eval]

theorem localGuardExpression_dead (p : OrdinaryOracleProgram) (width cap : ℕ)
    (action : Action p.base.tapeCount p.base.stateCount) :
    (localGuardExpression p width cap action).eval (fun _ => false)=false := by
  apply Bool.eq_false_iff.mpr
  simp [localGuardExpression,positiveClockExpression,BoolExpr.eval]

end NearCubicGates.Adapters.Compile.OracleExecution
