import SourceAdapters.Compile.OraclePrintTransCharge

/-!
proof of `thm:short-pcp-ours`, Step 4: pure query-guard and answer-controlled state templates.
The answer is the additional wire at clockBits; query tapes and allocation
wires are retained exactly, and the existing charged-clock formula is reused.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit OracleExecution
set_option autoImplicit false

def clockSizeT (p : OrdinaryOracleProgram) : Tm :=
  .add (initLengthEndT p) (.add (.v 1) (.k 1))

def queryActionU (p : OrdinaryOracleProgram) (rule : OracleReturn p.base.stateCount) : U :=
  .ite (.lt (.v 4) (.k p.base.stateCount))
    (.or (.and (.inp (clockSizeT p)) (.cst (.eq (.k rule.onTrue.val) (.v 4))))
      (.and (.not (.inp (clockSizeT p))) (.cst (.eq (.k rule.onFalse.val) (.v 4)))))
    (.ite (.lt (.v 4) (initLengthEndT p)) (.inp (.v 4))
      (remainingU p 5 (.sub (.v 4) (initLengthEndT p))))

theorem queryActionU_eq (p : OrdinaryOracleProgram) (width cap ell dl : ℕ) (D : List Bool)
    (rule : OracleReturn p.base.stateCount) (index : Fin (clockBits p width cap)) :
    postR (fun i => i.val) (queryActionExpression p width cap rule index)=
      (queryActionU p rule).toks D [width,cap,ell,dl,index.val] := by
  refine Fin.addCases ?_ ?_ index
  · intro view
    refine Fin.addCases ?_ ?_ view
    · intro q
      have hq := q.isLt
      simp [queryActionExpression,postR,answerExpression,queryActionU,U.toks,Tm.eval,clockSizeT,
        initLengthEndT,initWindowT,clockBits,windowBits,Fin.ext_iff,boolNat_nonzero,Nat.add_assoc]
    · intro rest
      have hr := rest.isLt
      have ht : p.base.stateCount+rest.val<
          (p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width))+p.base.tapeCount*(width+1) := by omega
      simp [queryActionExpression,postR,queryActionU,U.toks,Tm.eval,initLengthEndT,initWindowT,
        clockViewIndex,ht]
  · intro extra
    refine Fin.addCases ?_ ?_ extra
    · intro pair
      have hp := pair.isLt
      have hs : p.base.stateCount ≤ windowBits p.base.tapeCount p.base.stateCount width + pair.val := by
        simp only [windowBits]; omega
      simp [queryActionExpression,postR,queryActionU,U.toks,Tm.eval,initLengthEndT,initWindowT,
        clockLengthIndex,windowBits,Nat.mod_add_div]
      omega
    · intro budget
      simp only [queryActionExpression,Fin.addCases_right,postR_liftClock]
      have hrem := remainingU_eq p width cap D
        [width,cap,ell,dl,(windowBits p.base.tapeCount p.base.stateCount width)+
          (p.base.tapeCount*(width+1)+budget.val)] rfl rfl (by simp) budget
        (.sub (.v 4) (initLengthEndT p)) (by simp [Tm.eval,initLengthEndT,initWindowT,windowBits];omega)
        (by simp [Tm.lvOk,initLengthEndT,initWindowT])
      rw [hrem]
      simp [queryActionU,U.toks,Tm.eval,initLengthEndT,initWindowT,windowBits,Nat.add_assoc]

def queryGuardU (p : OrdinaryOracleProgram) (ℓ : ℕ) : U :=
  .and (.ite (.lt (.k 0) (.v 0)) (.inp (headT p.base.stateCount p.queryTape.val (.k 0))) (.ofBool false))
    (affordableU p ℓ)

theorem queryGuardU_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hC : env.getD 1 0=cap) (hlen : 2 ≤ env.length) :
    postR (fun i => i.val) (queryGuardExpression p width cap)=(queryGuardU p env.length).toks D env := by
  unfold queryGuardExpression queryGuardU
  simp only [postR,U.toks,affordableU_eq p width cap D env hW hC hlen]
  unfold rewoundExpression
  by_cases hw : 0<width
  · simp only [hw,↓reduceDIte,postR,clockViewIndex,Fin.val_castAdd,headIndex_val,Tm.eval,hW,
      ↓reduceIte,show ¬(1=0) by omega,headT]
  · simp only [hw,↓reduceDIte,postR,Tm.eval,hW,↓reduceIte,U.ofBool_toks]

end NearCubicGates.Adapters.Compile.OraclePrint
