import SourceAdapters.Compile.OraclePrintInit

/-!
proof of `thm:short-pcp-ours`, Step 4: pure transition-template selectors and index terms. Fixed
program lists are template syntax; runtime positions are template terms.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
  NearCubicWires.LocalBitMultitape OracleExecution
set_option autoImplicit false

theorem postR_allOfFn_list {width k : ℕ} (ρ : Fin width → ℕ) (F : Fin k → BoolExpr width) (D : List Bool)
    (env : List ℕ) (G : Fin k → U) (hb : ∀ i : Fin k, postR ρ (F i)=(G i).toks D env) :
    postR ρ (allExpression (List.ofFn F))=(U.andList (List.ofFn G)).toks D env := by
  rw [postR_all,U.andList_toks,List.length_ofFn,List.length_ofFn,
    flatMap_ofFn k F (postR ρ) (fun i => if h : i<k then (G ⟨i,h⟩).toks D env else []) (fun i => by simp [hb i]),
    flatMap_ofFn k G (fun u => u.toks D env) (fun i => if h : i<k then (G ⟨i,h⟩).toks D env else []) (fun i => by simp)]

theorem postR_liftClock {p : OrdinaryOracleProgram} {width cap : ℕ} (e : BoolExpr (clockBits p width cap)) :
    postR (fun i => i.val) (liftClockExpression e)=postR (fun i => i.val) e := by
  rw [liftClockExpression,postR_rename]
  rfl

theorem postR_clockView {p : OrdinaryOracleProgram} {width cap : ℕ}
    (e : BoolExpr (windowBits p.base.tapeCount p.base.stateCount width)) :
    postR (fun i => i.val) (renameExpression (clockViewIndex (p := p) (cap := cap)) e)=
      postR (fun i => i.val) e := by
  rw [postR_rename]
  rfl

def headT (s q : ℕ) (pos : Tm) : Tm := .add (.k s) (.add pos (.mul (.v 0) (.k q)))
def budgetT (p : OrdinaryOracleProgram) (b : Tm) : Tm := .add (initLengthEndT p) b

theorem headIndex_val {t s width : ℕ} (tape : Fin t) (pos : Fin width) :
    (@headIndex t s width tape pos).val=s+(pos.val+width*tape.val) := by
  simp [headIndex,finProdFinEquiv]

theorem clockBudget_val (p : OrdinaryOracleProgram) (width cap : ℕ) (b : Fin (cap+1)) :
    (clockBudgetIndex (p := p) (width := width) b).val=
      (p.base.stateCount+(p.base.tapeCount*width+p.base.tapeCount*width))+p.base.tapeCount*(width+1)+b.val := by
  simp [clockBudgetIndex,windowBits,Nat.add_assoc]

def moveT (move : HeadMove) (pos : Tm) : Tm :=
  match move with
  | .left => .sub pos (.k 1)
  | .stay => pos
  | .right => .add pos (.k 1)

theorem moveT_eval (move : HeadMove) (pos : Tm) (env : List ℕ) :
    (moveT move pos).eval env=move.apply (pos.eval env) := by
  cases move <;> rfl

/-- Runtime dispatch among a fixed finite list adds no circuit token. -/
def pickU : List U → Tm → U
  | [], _ => .ofBool false
  | u::us, index => .ite (.eq index (.k 0)) u (pickU us (.sub index (.k 1)))

theorem pickU_eq (us : List U) (D : List Bool) (env : List ℕ) :
    ∀ (i : Fin us.length) (it : Tm), it.eval env=i.val →
      (pickU us it).toks D env=(us.get i).toks D env := by
  induction us with
  | nil => intro i; exact Fin.elim0 i
  | cons u us ih =>
    intro i it
    refine Fin.cases ?_ ?_ i
    · intro he
      simp [pickU,U.toks,Tm.eval,he]
    · intro j he
      simp only [pickU,U.toks,Tm.eval,he,Fin.val_succ,Nat.succ_ne_zero,↓reduceIte]
      exact ih j (.sub it (.k 1)) (by simp only [Tm.eval,he,Fin.val_succ,Nat.add_sub_cancel])

theorem pickU_ofFn {k : ℕ} (f : Fin k → U) (i : Fin k) (it : Tm) (D : List Bool) (env : List ℕ)
    (hi : it.eval env=i.val) :
    (pickU (List.ofFn f) it).toks D env=(f i).toks D env := by
  have h := pickU_eq (List.ofFn f) D env ⟨i.val,by simp⟩ it hi
  simpa using h

end NearCubicGates.Adapters.Compile.OraclePrint
