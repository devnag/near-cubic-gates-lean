import SourceAdapters.Compile.OraclePrintTransCore

/-!
proof of `thm:short-pcp-ours`, Step 4: runtime templates for literal prefix checks and full oracle
clock debits. The templates generate the exact existing expression syntax,
including false branches, rather than a merely equivalent Boolean formula.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit OracleExecution
set_option autoImplicit false

theorem substitute_any {n m : ℕ} (σ : Fin n → BoolExpr m) (es : List (BoolExpr n)) :
    substituteExpression σ (anyExpression es)=anyExpression (es.map (substituteExpression σ)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [anyExpression,substituteExpression,ih]

theorem clockPrefix_tokens (p : OrdinaryOracleProgram) (width cap : ℕ) (D : List Bool)
    (env : List ℕ) (hW : env.getD 0 0=width) (hlen : 0<env.length) (count : ℕ) (ct : Tm)
    (hc : ct.eval env=count) (hlc : ct.lvOk env.length) :
    postR (fun i => i.val) (clockPrefixExpression p width cap count)=
      (prefixU p.base.tapeCount p.base.stateCount p.queryTape.val env.length ct (.k 0)).toks D env := by
  rw [clockPrefixExpression,postR_rename]
  exact prefix_eq p width cap D env hW hlen count 0 ct (.k 0) hc rfl hlc trivial

def remainingU (p : OrdinaryOracleProgram) (ℓ : ℕ) (target : Tm) : U :=
  let charge := Tm.add (.add target (.mul (.k 2) (.v ℓ))) (.k 2)
  .bigOr (.v 0)
    (.and (prefixU p.base.tapeCount p.base.stateCount p.queryTape.val (ℓ+1) (.v ℓ) (.k 0))
      (.ite (.lt charge (.add (.v 1) (.k 1))) (.inp (budgetT p charge)) (.ofBool false))) (.ofBool false)

theorem remainingU_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hC : env.getD 1 0=cap) (hlen : 2 ≤ env.length)
    (target : Fin (cap+1)) (tt : Tm) (ht : tt.eval env=target.val) (hlt : tt.lvOk env.length) :
    postR (fun i => i.val) (clockRemainingExpression p width cap target)=
      (remainingU p env.length tt).toks D env := by
  unfold clockRemainingExpression queryRemainingExpression remainingU
  rw [substitute_any,List.map_ofFn]
  refine postR_anyOfFn _ _ D env _ _ _ (by simp only [Tm.eval,hW]) (fun count => ?_) (by simp)
  have hWa : (env++[count.val]).getD 0 0=width := by rw [List.getD_append _ _ _ _ (by omega)];exact hW
  have hCa : (env++[count.val]).getD 1 0=cap := by rw [List.getD_append _ _ _ _ (by omega)];exact hC
  have hta : tt.eval (env++[count.val])=target.val := by rw [Tm.eval_append _ _ _ hlt,ht]
  have hcount : (env++[count.val]).getD env.length 0=count.val := by simp
  have hpref := clockPrefix_tokens p width cap D (env++[count.val]) hWa (by simp) count.val (.v env.length)
    (by simp only [Tm.eval,hcount]) (by simp [Tm.lvOk])
  rw [List.length_append,List.length_singleton] at hpref
  simp only [Function.comp_def,substituteExpression,chargeSubstitution,Fin.addCases_left,postR,U.toks]
  rw [hpref]
  by_cases hcost : target.val+2*count.val+2<cap+1
  · simp only [hcost,↓reduceDIte,substituteExpression,chargeSubstitution,Fin.addCases_right,postR,
      Tm.eval,hta,hcount,hCa,↓reduceIte,show ¬(1=0) by omega]
    rw [clockBudget_val]
    simp only [budgetT,initLengthEndT,initWindowT,Tm.eval,hWa,hta,hcount]
  · simp only [hcost,↓reduceDIte,substituteExpression,postR,Tm.eval,hta,hcount,hCa,↓reduceIte,U.ofBool_toks]

def affordableU (p : OrdinaryOracleProgram) (ℓ : ℕ) : U :=
  .bigOr (.add (.v 1) (.k 1)) (remainingU p (ℓ+1) (.v ℓ)) (.ofBool false)

theorem affordableU_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hC : env.getD 1 0=cap) (hlen : 2 ≤ env.length) :
    postR (fun i => i.val) (clockAffordableExpression p width cap)=(affordableU p env.length).toks D env := by
  unfold clockAffordableExpression queryAffordableExpression affordableU
  rw [substitute_any,List.map_ofFn]
  refine postR_anyOfFn _ _ D env _ _ _ (by simp only [Tm.eval,hC]) (fun target => ?_) (by simp)
  change postR _ (clockRemainingExpression p width cap target)=_
  have h := remainingU_eq p width cap D (env++[target.val])
    (by rw [List.getD_append _ _ _ _ (by omega)];exact hW)
    (by rw [List.getD_append _ _ _ _ (by omega)];exact hC)
    (by simp;omega) target (.v env.length) (by simp [Tm.eval]) (by simp [Tm.lvOk])
  simpa only [List.length_append,List.length_singleton] using h

end NearCubicGates.Adapters.Compile.OraclePrint
