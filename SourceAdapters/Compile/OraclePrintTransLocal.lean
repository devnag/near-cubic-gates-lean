import SourceAdapters.Compile.OraclePrintTransLocalParts

/-!
proof of `thm:short-pcp-ours`, Step 4: runtime dispatch for the complete ordinary action vector.
The selectors add no Boolean nodes, and preserve the exact postfix syntax.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
  NearCubicWires.LocalBitMultitape OracleExecution
set_option autoImplicit false

def actionViewU (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount) : U :=
  .ite (.lt (.v 4) (.k p.base.stateCount)) (.cst (.eq (.k action.nextControl.val) (.v 4)))
    (.ite (.lt (.v 4) (initHeadEndT p))
      (pickU (List.ofFn fun tape => actionHeadU action tape 5
        (.md (.sub (.v 4) (.k p.base.stateCount)) (.v 0)))
        (.div (.sub (.v 4) (.k p.base.stateCount)) (.v 0)))
      (pickU (List.ofFn fun tape => writtenCellU action tape
        (.md (.sub (.v 4) (initHeadEndT p)) (.v 0)))
        (.div (.sub (.v 4) (initHeadEndT p)) (.v 0))))

theorem actionViewU_eq (p : OrdinaryOracleProgram) (width cap ell dl : ℕ) (D : List Bool)
    (action : Action p.base.tapeCount p.base.stateCount)
    (index : Fin (windowBits p.base.tapeCount p.base.stateCount width)) :
    postR (fun i => i.val) (actionExpression action index)=
      (actionViewU p action).toks D [width,cap,ell,dl,index.val] := by
  refine Fin.addCases ?_ ?_ index
  · intro q
    have hq := q.isLt
    simp [actionExpression,postR,actionViewU,U.toks,Tm.eval,hq,Fin.ext_iff,boolNat_nonzero]
  · intro rest
    refine Fin.addCases ?_ ?_ rest
    · intro pair
      have hp := pair.isLt
      simp only [actionExpression,Fin.addCases_left,Fin.addCases_right]
      change postR (fun i => i.val) (headSelection pair.divNat (fun old =>
        .const (decide ((action.move pair.divNat).apply old.val=pair.modNat.val))))=_
      have ht : p.base.stateCount+pair.val<p.base.stateCount+p.base.tapeCount*width := by omega
      simp only [actionViewU,U.toks,Tm.eval,initHeadEndT,List.getD,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some,Fin.val_natAdd,Fin.val_castAdd,
        Nat.not_lt_of_ge (Nat.le_add_right _ _),ht,↓reduceIte,show ¬(1=0) by omega]
      rw [pickU_ofFn _ pair.divNat _ D _ (by simp [Tm.eval])]
      exact actionHeadU_eq action pair.divNat pair.modNat D _ rfl (by simp) _
        (by simp [Tm.eval]) (by simp [Tm.lvOk])
    · intro pair
      simp only [actionExpression,Fin.addCases_right]
      change postR (fun i => i.val) (writtenCellExpression action pair.divNat pair.modNat)=_
      have hn : ¬p.base.stateCount+(p.base.tapeCount*width+pair.val)<p.base.stateCount := by omega
      have ht : ¬p.base.stateCount+(p.base.tapeCount*width+pair.val)<p.base.stateCount+p.base.tapeCount*width := by omega
      simp only [actionViewU,U.toks,Tm.eval,initHeadEndT,List.getD,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some,Fin.val_natAdd,hn,ht,↓reduceIte]
      have hsub : p.base.stateCount+(p.base.tapeCount*width+pair.val)-(p.base.stateCount+p.base.tapeCount*width)=pair.val := by omega
      rw [pickU_ofFn _ pair.divNat _ D _ (by simp [Tm.eval,hsub])]
      exact writtenCellU_eq action pair.divNat pair.modNat D _ rfl _
        (by simp [Tm.eval,hsub])

def localRemainingU (p : OrdinaryOracleProgram) (target : Tm) : U :=
  .ite (.lt (.add target (.k 1)) (.add (.v 1) (.k 1)))
    (.inp (budgetT p (.add target (.k 1)))) (.ofBool false)

theorem localRemainingU_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hC : env.getD 1 0=cap) (target : Fin (cap+1))
    (tt : Tm) (ht : tt.eval env=target.val) :
    postR (fun i => i.val) (localRemainingExpression p width cap target)=(localRemainingU p tt).toks D env := by
  unfold localRemainingExpression localRemainingU
  by_cases h : target.val+1<cap+1
  · simp only [h,↓reduceDIte,postR,U.toks,Tm.eval,ht,hC,↓reduceIte,show ¬(1=0) by omega]
    simp only [budgetT,initLengthEndT,initWindowT,Tm.eval,hW,ht,clockBudget_val]
  · simp only [h,↓reduceDIte,postR,U.toks,Tm.eval,ht,hC,↓reduceIte,U.ofBool_toks]

def localActionU (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount) : U :=
  .ite (.lt (.v 4) (initWindowT p)) (actionViewU p action)
    (.ite (.lt (.v 4) (initLengthEndT p))
      (pickU (List.ofFn fun tape => actionLengthU p action tape 5
        (.md (.sub (.v 4) (initWindowT p)) (.add (.v 0) (.k 1))))
        (.div (.sub (.v 4) (initWindowT p)) (.add (.v 0) (.k 1))))
      (localRemainingU p (.sub (.v 4) (initLengthEndT p))))

theorem localActionU_eq (p : OrdinaryOracleProgram) (width cap ell dl : ℕ) (D : List Bool)
    (action : Action p.base.tapeCount p.base.stateCount) (index : Fin (clockBits p width cap)) :
    postR (fun i => i.val) (localActionExpression p width cap action index)=
      (localActionU p action).toks D [width,cap,ell,dl,index.val] := by
  refine Fin.addCases ?_ ?_ index
  · intro view
    have hv := view.isLt
    simp only [localActionExpression,Fin.addCases_left,postR_clockView]
    rw [actionViewU_eq p width cap ell dl D action view]
    simp only [localActionU,U.toks,Tm.eval,initWindowT,List.getD,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,Fin.val_castAdd]
    have h : view.val<p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width) := hv
    simp only [h,↓reduceIte,show ¬(1=0) by omega]
  · intro extra
    refine Fin.addCases ?_ ?_ extra
    · intro pair
      have hp := pair.isLt
      simp only [localActionExpression,Fin.addCases_right,Fin.addCases_left]
      change postR (fun i => i.val) (actionLengthExpression (cap := cap) action pair.divNat pair.modNat)=_
      simp only [localActionU,U.toks,Tm.eval,initWindowT,initLengthEndT,List.getD,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some,Fin.val_natAdd,Fin.val_castAdd,windowBits,
        Nat.not_lt_of_ge (Nat.le_add_right _ _),Nat.add_lt_add_iff_left,hp,↓reduceIte,show ¬(1=0) by omega]
      rw [pickU_ofFn _ pair.divNat _ D _ (by simp [Tm.eval])]
      exact actionLengthU_eq p width cap action pair.divNat pair.modNat D _ rfl (by simp) _
        (by simp [Tm.eval]) (by simp [Tm.lvOk])
    · intro budget
      simp only [localActionExpression,Fin.addCases_right]
      have h : windowBits p.base.tapeCount p.base.stateCount width+
          (p.base.tapeCount*(width+1)+budget.val) ≥
          (p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width))+p.base.tapeCount*(width+1) := by
        simp only [windowBits];omega
      simp only [localActionU,U.toks,Tm.eval,initWindowT,initLengthEndT,List.getD,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some,Fin.val_natAdd]
      have hw : ¬ windowBits p.base.tapeCount p.base.stateCount width+
          (p.base.tapeCount*(width+1)+budget.val) <
          p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width) := by
        simp only [windowBits];omega
      simp only [hw,show ¬ windowBits p.base.tapeCount p.base.stateCount width+
          (p.base.tapeCount*(width+1)+budget.val) <
          (p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width))+p.base.tapeCount*(width+1) by omega,
        ↓reduceIte]
      exact localRemainingU_eq p width cap D _ rfl rfl budget _
        (by simp [Tm.eval,windowBits];omega)

end NearCubicGates.Adapters.Compile.OraclePrint
