import SourceAdapters.Compile.OraclePrintAddress
import SourceAdapters.Compile.OraclePrintCompile

/-!
proof of `thm:short-pcp-ours`, Step 4: one fixed initial-expression template reads
width, cap, seed length, framed data length and coordinate at runtime. Data
bits come from the retained framed data; seed bits remain input references.
The template equality includes static depth and stack bounds.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
  OracleExecution
set_option autoImplicit false

def seedFrameU (pos : Tm) : U :=
  .ite (.eq (.md pos (.k 2)) (.k 0)) (.cst (.lt (.div pos (.k 2)) (.v 2)))
    (.ite (.lt (.div pos (.k 2)) (.v 2)) (.inp (.div pos (.k 2))) (.ofBool false))

theorem seedFrameU_eq (ell pos : ℕ) (pt : Tm) (D : List Bool) (env : List ℕ)
    (he : env.getD 2 0=ell) (hp : pt.eval env=pos) :
    postR (fun i => i.val) (@witnessFrameExpression ell pos)=(seedFrameU pt).toks D env := by
  simp only [seedFrameU,U.toks,Tm.eval,hp,he]
  unfold witnessFrameExpression
  by_cases hm : pos%2=0 <;> by_cases hl : pos/2<ell <;>
    simp [hm,hl,postR]

def initialInputU (pos : Tm) : U :=
  .ite (.eq (.md pos (.k 2)) (.k 0))
    (.cst (.lt (.div pos (.k 2)) (.add (.add (.v 3) (.mul (.k 2) (.v 2))) (.k 1))))
    (.ite (.lt (.div pos (.k 2)) (.v 3)) (.dat (.div pos (.k 2)))
      (seedFrameU (.sub (.div pos (.k 2)) (.v 3))))

theorem initialInputU_eq (r : OracleCompilationRequest) (env : List ℕ) (pos : ℕ) (pt : Tm)
    (he : env.getD 2 0=r.ell) (hd : env.getD 3 0=(RepairOrdinary.frame r.data).length)
    (hp : pt.eval env=pos) :
    postR (fun i => i.val) (initialInputCell r pos)=
      (initialInputU pt).toks (RepairOrdinary.frame r.data) env := by
  simp only [initialInputU,U.toks,Tm.eval,hp,he,hd]
  unfold initialInputCell
  by_cases hm : pos%2=0
  · simp only [hm,↓reduceIte,show ¬(1=0) by omega,postR]
    split <;> simp_all
  · by_cases hl : pos/2<(RepairOrdinary.frame r.data).length
    · simp only [hm,hl,↓reduceIte,show ¬(1=0) by omega,postR]
    · simp only [hm,hl,↓reduceIte]
      exact seedFrameU_eq _ _ _ _ env he (by simp only [Tm.eval,hp,hd])

def initWindowT (p : OrdinaryOracleProgram) : Tm :=
  .add (.k p.base.stateCount) (.add (.mul (.k p.base.tapeCount) (.v 0)) (.mul (.k p.base.tapeCount) (.v 0)))

def initHeadEndT (p : OrdinaryOracleProgram) : Tm :=
  .add (.k p.base.stateCount) (.mul (.k p.base.tapeCount) (.v 0))

def initLengthEndT (p : OrdinaryOracleProgram) : Tm :=
  .add (initWindowT p) (.mul (.k p.base.tapeCount) (.add (.v 0) (.k 1)))

def Ti (p : OrdinaryOracleProgram) : U :=
  let pos := Tm.md (.sub (.v 4) (initHeadEndT p)) (.v 0)
  let tape := Tm.div (.sub (.v 4) (initHeadEndT p)) (.v 0)
  let len := Tm.md (.sub (.v 4) (initWindowT p)) (.add (.v 0) (.k 1))
  let lentape := Tm.div (.sub (.v 4) (initWindowT p)) (.add (.v 0) (.k 1))
  .ite (.lt (.v 4) (initWindowT p))
    (.ite (.lt (.v 4) (.k p.base.stateCount)) (.cst (.eq (.k p.base.machine.start.val) (.v 4)))
      (.ite (.lt (.v 4) (initHeadEndT p))
        (.cst (.eq (.md (.sub (.v 4) (.k p.base.stateCount)) (.v 0)) (.k 0)))
        (.ite (.eq tape (.k 0)) (initialInputU pos) (.ofBool false))))
    (.ite (.lt (.v 4) (initLengthEndT p))
      (.cst (.eq (.ite (.eq lentape (.k 0))
        (.add (.add (.mul (.k 2) (.v 3)) (.mul (.k 4) (.v 2))) (.k 3)) (.k 0)) len))
      (.cst (.eq (.v 1) (.sub (.v 4) (initLengthEndT p)))))

theorem boolNat_nonzero (P : Prop) [Decidable P] : ((if P then 1 else 0 : ℕ) != 0)=decide P := by
  by_cases h : P <;> simp [h]

theorem boolNat_ite {α : Sort _} (P : Prop) [Decidable P] (a b : α) :
    (if (if P then 1 else 0 : ℕ)=0 then a else b)=(if P then b else a) := by
  by_cases h : P <;> simp [h]

theorem Ti_tokens (p : OrdinaryOracleProgram) (D : List Bool) (width cap ell dl j : ℕ) :
    (Ti p).toks D [width,cap,ell,dl,j]=
      if j<p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width) then
        if j<p.base.stateCount then [.cst (decide (p.base.machine.start.val=j))] else
        if j<p.base.stateCount+p.base.tapeCount*width then [.cst (decide ((j-p.base.stateCount)%width=0))] else
        if (j-(p.base.stateCount+p.base.tapeCount*width))/width=0 then
          (initialInputU (.md (.sub (.v 4) (initHeadEndT p)) (.v 0))).toks D [width,cap,ell,dl,j]
        else [.cst false]
      else if j<(p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width))+p.base.tapeCount*(width+1) then
        [.cst (decide ((if (j-(p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width)))/(width+1)=0
          then 2*dl+4*ell+3 else 0)=
          (j-(p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width)))%(width+1)))]
      else [.cst (decide (cap=j-((p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width))+
        p.base.tapeCount*(width+1))))] := by
  simp only [Ti,U.toks,initWindowT,initHeadEndT,initLengthEndT,Tm.eval,List.getD,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,boolNat_ite,boolNat_nonzero,U.ofBool_toks]
  rfl

theorem Ti_eq (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (index : Fin (clockBits p (requestWidth r) r.fuel)) :
    postR (fun i => i.val) (initialExpression p r index)=
      (Ti p).toks (RepairOrdinary.frame r.data)
        [requestWidth r,r.fuel,r.ell,(RepairOrdinary.frame r.data).length,index.val] := by
  rw [Ti_tokens]
  refine Fin.addCases ?_ ?_ index
  · intro view
    refine Fin.addCases ?_ ?_ view
    · intro q
      have hq := q.isLt
      simp [initialExpression,postR,Fin.ext_iff,
        show q.val<p.base.stateCount+(p.base.tapeCount*requestWidth r+p.base.tapeCount*requestWidth r) by omega]
    · intro rest
      refine Fin.addCases ?_ ?_ rest
      · intro pair
        have hp := pair.isLt
        have h1 : p.base.stateCount+pair.val<p.base.stateCount+(p.base.tapeCount*requestWidth r+p.base.tapeCount*requestWidth r) := by omega
        have h2 : p.base.stateCount+pair.val<p.base.stateCount+p.base.tapeCount*requestWidth r := by omega
        simp [initialExpression,postR,finProdFinEquiv,h1,h2]
      · intro pair
        have hp := pair.isLt
        have h1 : p.base.stateCount+(p.base.tapeCount*requestWidth r+pair.val)<
          p.base.stateCount+(p.base.tapeCount*requestWidth r+p.base.tapeCount*requestWidth r) := by omega
        have h2 : ¬p.base.stateCount+(p.base.tapeCount*requestWidth r+pair.val)<
          p.base.stateCount+p.base.tapeCount*requestWidth r := by omega
        have hn : ¬p.base.stateCount+(p.base.tapeCount*requestWidth r+pair.val)<p.base.stateCount := by omega
        simp only [initialExpression,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd,
          h1,h2,hn,↓reduceIte]
        have hsub : p.base.stateCount+(p.base.tapeCount*requestWidth r+pair.val)-
            (p.base.stateCount+p.base.tapeCount*requestWidth r)=pair.val := by omega
        rw [hsub]
        change postR (fun i => i.val) (if pair.val/requestWidth r=0 then initialInputCell r (pair.val%requestWidth r)
          else .const false)=_
        split
        · exact initialInputU_eq r _ _ _ rfl rfl (by change (p.base.stateCount+(p.base.tapeCount*requestWidth r+pair.val)-
            (p.base.stateCount+p.base.tapeCount*requestWidth r))%requestWidth r=pair.val%requestWidth r; rw [hsub])
        · rfl
  · intro extra
    refine Fin.addCases ?_ ?_ extra
    · intro pair
      have hp := pair.isLt
      have hlen : 4*(r.data.length+r.ell)+5=2*(RepairOrdinary.frame r.data).length+4*r.ell+3 := by
        rw [RepairOrdinary.frame_length];omega
      have hsum : (p.base.stateCount+(p.base.tapeCount*requestWidth r+p.base.tapeCount*requestWidth r)+pair.val)-
          (p.base.stateCount+(p.base.tapeCount*requestWidth r+p.base.tapeCount*requestWidth r))=pair.val := by omega
      simp only [initialExpression,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd,
        windowBits,postR,Fin.ext_iff,hlen]
      simp only [Nat.not_lt_of_ge (Nat.le_add_right _ _),↓reduceIte,hsum,
        Nat.add_lt_add_iff_left,hp]
      rfl
    · intro budget
      simp only [initialExpression,Fin.addCases_right,Fin.val_natAdd,windowBits,postR]
      simp
      omega

theorem Ti_eq_nat (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) (j : ℕ)
    (hj : j<clockBits p (requestWidth r) r.fuel) :
    postR (fun i => i.val) (initialExpression p r ⟨j,hj⟩)=
      (Ti p).toks (RepairOrdinary.frame r.data)
        [requestWidth r,r.fuel,r.ell,(RepairOrdinary.frame r.data).length,j] := Ti_eq p r ⟨j,hj⟩

theorem Ti_depth (p : OrdinaryOracleProgram) : (Ti p).depth ≤ 11 := by
  simp [Ti,initialInputU,seedFrameU,U.depth,U.ofBool]

theorem Ti_tneed (p : OrdinaryOracleProgram) : (Ti p).tneed ≤ 16 := by
  simp [Ti,initialInputU,seedFrameU,U.tneed,U.ofBool,Tm.ofBool,Tm.need,
    initWindowT,initHeadEndT,initLengthEndT]

end NearCubicGates.Adapters.Compile.OraclePrint
