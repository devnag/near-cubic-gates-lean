import SourceAdapters.Compile.OraclePrintTransCore

/-!
proof of `thm:short-pcp-ours`, Step 4: exact templates for fixed program-row and runtime head/length
selection. Only the finite control and scanned-symbol table is enumerated as
static syntax; every tape-window loop keeps its runtime bound.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
  NearCubicWires.LocalBitMultitape OracleExecution
set_option autoImplicit false

def headSelectionU (s tape ℓ : ℕ) (body : U) : U :=
  .bigOr (.v 0) (.and (.inp (headT s tape (.v ℓ))) body) (.ofBool false)

theorem headSelectionU_eq {t s width : ℕ} (tape : Fin t) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hlen : 0<env.length)
    (values : Fin width → BoolExpr (windowBits t s width)) (body : U)
    (hb : ∀ i, postR (fun j => j.val) (values i)=body.toks D (env++[i.val])) :
    postR (fun i => i.val) (headSelection tape values)=
      (headSelectionU s tape.val env.length body).toks D env := by
  unfold headSelection headSelectionU
  refine postR_anyOfFn _ _ D env _ _ _ (by simp only [Tm.eval,hW]) (fun i => ?_) (by simp)
  have hWa : (env++[i.val]).getD 0 0=width := by rw [List.getD_append _ _ _ _ hlen];exact hW
  simp only [postR,U.toks,hb,headT,Tm.eval,hWa,headIndex_val ]
  simp

def scannedU (t s tape ℓ : ℕ) : U :=
  headSelectionU s tape ℓ (.inp (cellT t s tape (.v ℓ)))

theorem scannedU_eq {t s width : ℕ} (tape : Fin t) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hlen : 0<env.length) :
    postR (fun i => i.val) (@scannedExpression t s width tape)=(scannedU t s tape.val env.length).toks D env := by
  unfold scannedExpression scannedU
  apply headSelectionU_eq tape D env hW hlen
  intro i
  have hWa : (env++[i.val]).getD 0 0=width := by rw [List.getD_append _ _ _ _ hlen];exact hW
  simp only [postR,U.toks,cellT,Tm.eval,hWa]
  simp [cellIndex,finProdFinEquiv,Nat.add_comm]

def rowU {t s : ℕ} (q : Fin s) (scans : Fin t → Bool) (ℓ : ℕ) : U :=
  .and (.inp (.k q.val)) (U.andList (List.ofFn fun tape : Fin t =>
    if scans tape then scannedU t s tape.val ℓ else .not (scannedU t s tape.val ℓ)))

theorem rowU_eq {t s width : ℕ} (q : Fin s) (scans : Fin t → Bool) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hlen : 0<env.length) :
    postR (fun i => i.val) (@rowExpression t s width q scans)=(rowU q scans env.length).toks D env := by
  unfold rowExpression scanPatternExpression rowU
  simp only [postR,U.toks,Tm.eval]
  rw [postR_allOfFn_list _ _ D env
    (fun tape : Fin t => if scans tape then scannedU t s tape.val env.length else .not (scannedU t s tape.val env.length))
    (fun tape => by
      cases hs : scans tape <;> simp [postR,U.toks,scannedU_eq tape D env hW hlen])]
  rfl

def fitsU {t s : ℕ} (action : Action t s) (ℓ : ℕ) : U :=
  U.andList (List.ofFn fun tape : Fin t =>
    headSelectionU s tape.val ℓ (.cst (.lt (moveT (action.move tape) (.v ℓ)) (.v 0))))

theorem fitsU_eq {t s width : ℕ} (action : Action t s) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0=width) (hlen : 0<env.length) :
    postR (fun i => i.val) (@actionFitsExpression t s width action)=(fitsU action env.length).toks D env := by
  unfold actionFitsExpression fitsU
  apply postR_allOfFn_list
  intro tape
  apply headSelectionU_eq tape D env hW hlen
  intro position
  have hWa : (env++[position.val]).getD 0 0=width := by rw [List.getD_append _ _ _ _ hlen];exact hW
  simp only [postR,U.toks,Tm.eval,moveT_eval,hWa,boolNat_nonzero]
  simp

end NearCubicGates.Adapters.Compile.OraclePrint
