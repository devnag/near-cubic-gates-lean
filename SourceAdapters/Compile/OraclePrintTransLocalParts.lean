import SourceAdapters.Compile.OraclePrintTransSelect

/-!
proof of `thm:short-pcp-ours`, Step 4: exact runtime templates for local head movement, cell writes,
allocation-length selection and the unit-budget guard. These preserve the
existing expression syntax, including each constant and selector gate.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
  NearCubicWires.LocalBitMultitape OracleExecution
set_option autoImplicit false

def positiveU (p : OrdinaryOracleProgram) (ℓ : ℕ) : U :=
  .bigOr (.add (.v 1) (.k 1))
    (.ite (.lt (.k 0) (.v ℓ)) (.inp (budgetT p (.v ℓ))) (.ofBool false)) (.ofBool false)

theorem positiveU_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hC : env.getD 1 0=cap) (hlen : 2 ≤ env.length) :
    postR (fun i => i.val) (positiveClockExpression p width cap)=(positiveU p env.length).toks D env := by
  unfold positiveClockExpression positiveU
  refine postR_anyOfFn _ _ D env _ _ _ (by simp only [Tm.eval,hC]) (fun b => ?_) (by simp)
  have hWa : (env++[b.val]).getD 0 0=width := by rw [List.getD_append _ _ _ _ (by omega)];exact hW
  have hb : (env++[b.val]).getD env.length 0=b.val := by simp
  by_cases hp : 0<b.val
  · simp only [hp,↓reduceIte,postR,U.toks,Tm.eval,hb,show ¬(1=0) by omega]
    simp only [budgetT,initLengthEndT,initWindowT,Tm.eval,hWa,hb,clockBudget_val]
  · simp only [hp,↓reduceIte,postR,U.toks,Tm.eval,hb,U.ofBool_toks]

def localGuardU {t s : ℕ} (p : OrdinaryOracleProgram) (action : Action t s) (ℓ : ℕ) : U :=
  .and (positiveU p ℓ) (fitsU action ℓ)

theorem localGuardU_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hC : env.getD 1 0=cap) (hlen : 2 ≤ env.length)
    (action : Action p.base.tapeCount p.base.stateCount) :
    postR (fun i => i.val) (localGuardExpression p width cap action)=
      (localGuardU p action env.length).toks D env := by
  simp only [localGuardExpression,localGuardU,postR,U.toks,postR_clockView,
    positiveU_eq p width cap D env hW hC hlen,fitsU_eq action D env hW (by omega)]

def actionHeadU {t s : ℕ} (action : Action t s) (tape : Fin t) (ℓ : ℕ) (pos : Tm) : U :=
  headSelectionU s tape.val ℓ (.cst (.eq (moveT (action.move tape) (.v ℓ)) pos))

theorem actionHeadU_eq {t s width : ℕ} (action : Action t s) (tape : Fin t) (position : Fin width)
    (D : List Bool) (env : List ℕ) (hW : env.getD 0 0=width) (hlen : 0<env.length)
    (pt : Tm) (hp : pt.eval env=position.val) (hlp : pt.lvOk env.length) :
    postR (fun i => i.val) (headSelection (s := s) tape
      (fun old : Fin width => .const (decide ((action.move tape).apply old.val=position.val))))=
      (actionHeadU action tape env.length pt).toks D env := by
  unfold actionHeadU
  apply headSelectionU_eq tape D env hW hlen
  intro old
  have hpa : pt.eval (env++[old.val])=position.val := by rw [Tm.eval_append _ _ _ hlp,hp]
  simp only [postR,U.toks,Tm.eval,moveT_eval,hpa,boolNat_nonzero]
  simp

def writtenCellU {t s : ℕ} (action : Action t s) (tape : Fin t) (pos : Tm) : U :=
  match action.write tape with
  | none => .inp (cellT t s tape.val pos)
  | some value => .or (.and (.inp (headT s tape.val pos)) (.ofBool value))
      (.and (.not (.inp (headT s tape.val pos))) (.inp (cellT t s tape.val pos)))

theorem writtenCellU_eq {t s width : ℕ} (action : Action t s) (tape : Fin t) (position : Fin width)
    (D : List Bool) (env : List ℕ) (hW : env.getD 0 0=width) (pt : Tm) (hp : pt.eval env=position.val) :
    postR (fun i => i.val) (writtenCellExpression action tape position)=(writtenCellU action tape pt).toks D env := by
  cases hw : action.write tape <;>
    simp only [writtenCellExpression,writtenCellU,hw,postR,U.toks,U.ofBool_toks,cellT,headT,Tm.eval,hp,hW,headIndex_val]
  all_goals simp [cellIndex,finProdFinEquiv,Nat.add_comm]

def lengthSelectionU (p : OrdinaryOracleProgram) (tape ℓ : ℕ) (body : U) : U :=
  .bigOr (.add (.v 0) (.k 1))
    (.and (.inp (lenT p.base.tapeCount p.base.stateCount tape (.v ℓ))) body) (.ofBool false)

theorem lengthSelectionU_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (tape : Fin p.base.tapeCount)
    (D : List Bool) (env : List ℕ) (hW : env.getD 0 0=width) (hlen : 0<env.length)
    (values : Fin (width+1) → BoolExpr (clockBits p width cap)) (body : U)
    (hb : ∀ i, postR (fun j => j.val) (values i)=body.toks D (env++[i.val])) :
    postR (fun i => i.val) (lengthSelection tape values)=
      (lengthSelectionU p tape.val env.length body).toks D env := by
  unfold lengthSelection lengthSelectionU
  refine postR_anyOfFn _ _ D env _ _ _ (by simp only [Tm.eval,hW]) (fun i => ?_) (by simp)
  have hWa : (env++[i.val]).getD 0 0=width := by rw [List.getD_append _ _ _ _ hlen];exact hW
  simp only [postR,U.toks,hb,lenT,Tm.eval,hWa,clockLength_val]
  simp

theorem clockHeadSelectionU_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (tape : Fin p.base.tapeCount)
    (D : List Bool) (env : List ℕ) (hW : env.getD 0 0=width) (hlen : 0<env.length)
    (values : Fin width → BoolExpr (clockBits p width cap)) (body : U)
    (hb : ∀ i, postR (fun j => j.val) (values i)=body.toks D (env++[i.val])) :
    postR (fun i => i.val) (clockHeadSelection tape values)=
      (headSelectionU p.base.stateCount tape.val env.length body).toks D env := by
  unfold clockHeadSelection headSelectionU
  refine postR_anyOfFn _ _ D env _ _ _ (by simp only [Tm.eval,hW]) (fun i => ?_) (by simp)
  have hWa : (env++[i.val]).getD 0 0=width := by rw [List.getD_append _ _ _ _ hlen];exact hW
  simp only [postR,U.toks,hb,headT,Tm.eval,hWa,clockViewIndex,Fin.val_castAdd,headIndex_val]
  simp

def maxT (a b : Tm) : Tm := .ite (.lt a b) b a

theorem maxT_eval (a b : Tm) (env : List ℕ) : (maxT a b).eval env=max (a.eval env) (b.eval env) := by
  simp only [maxT,Tm.eval]
  by_cases h : a.eval env < b.eval env
  · simp [h,Nat.max_eq_right (Nat.le_of_lt h)]
  · simp [h,Nat.max_eq_left (Nat.le_of_not_gt h)]

def actionLengthU (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount)
    (tape : Fin p.base.tapeCount) (ℓ : ℕ) (target : Tm) : U :=
  match action.write tape with
  | none => .inp (lenT p.base.tapeCount p.base.stateCount tape.val target)
  | some _ => lengthSelectionU p tape.val ℓ (headSelectionU p.base.stateCount tape.val (ℓ+1)
      (.cst (.eq (maxT (.v ℓ) (.add (.v (ℓ+1)) (.k 1))) target)))

theorem actionLengthU_eq (p : OrdinaryOracleProgram) (width cap : ℕ)
    (action : Action p.base.tapeCount p.base.stateCount) (tape : Fin p.base.tapeCount) (target : Fin (width+1))
    (D : List Bool) (env : List ℕ) (hW : env.getD 0 0=width) (hlen : 0<env.length)
    (tt : Tm) (ht : tt.eval env=target.val) (hlt : tt.lvOk env.length) :
    postR (fun i => i.val) (actionLengthExpression (cap := cap) action tape target)=
      (actionLengthU p action tape env.length tt).toks D env := by
  cases hw : action.write tape with
  | none => simp only [actionLengthExpression,actionLengthU,hw,postR,U.toks,lenT,Tm.eval,ht,hW,clockLength_val]
  | some value =>
    simp only [actionLengthExpression,actionLengthU,hw]
    apply lengthSelectionU_eq p width cap tape D env hW hlen
    intro length
    have hWa : (env++[length.val]).getD 0 0=width := by rw [List.getD_append _ _ _ _ hlen];exact hW
    have hlenA : (env++[length.val]).length=env.length+1 := by simp
    rw [←hlenA]
    apply clockHeadSelectionU_eq p width cap tape D _ hWa (by simp)
    intro head
    have hta : tt.eval ((env++[length.val])++[head.val])=target.val := by
      rw [List.append_assoc,Tm.eval_append _ _ _ hlt,ht]
    have hlength : ((env++[length.val])++[head.val]).getD env.length 0=length.val := by
      rw [List.getD_append _ _ _ _ (by simp)];simp
    simp only [postR,U.toks,Tm.eval,maxT_eval,hta,hlength,boolNat_nonzero]
    simp

end NearCubicGates.Adapters.Compile.OraclePrint
