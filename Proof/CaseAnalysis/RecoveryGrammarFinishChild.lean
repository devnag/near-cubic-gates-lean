import Proof.CaseAnalysis.RecoveryGrammarBankAtoms
import Proof.Amplification.RecoveryQueryCellReuse

/-! Close a grammar child with one actual continuation. The erased suffix
left by a reverse fold is the same paid false backing as the next stack. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarFinishChild
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (resultHeads resultData)
open RecoveryBoundedGrammarContinue (bank stackCapacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cleaned (D : Fin 78→List Bool) (stack : List Bool):=Function.update D 74 stack

theorem clean_bank (D : Fin 78→List Bool) (stack : List Bool) (z B P : ℕ)
    (hs : D 74=stack++List.replicate z false) (hP : stack.length+z≤P) :
    bank D B P=bank (cleaned D stack) B P := by
  funext i
  refine Fin.addCases (m:=78) (n:=1) ?_ ?_ i
  · intro j
    by_cases hj : j=74
    · subst j
      change ZeroPadding.pad P (D 74)=ZeroPadding.pad P stack
      rw [hs]
      exact RecoveryQueryCell.pad_suffix P stack z hP
    · have hn : (j.castAdd 1 : Fin 79)≠74 := by
        intro he
        have hv:=congrArg Fin.val he
        exact hj (Fin.ext hv)
      simp only [bank,stackCapacity,if_neg hn,resultData,Fin.addCases_left,cleaned,
        Function.update_of_ne hj]
  · intro j;fin_cases j;rfl

variable {s : ℕ}
theorem finish_run (p : Machine 79 s) (fuel : ℕ) (c : Configuration 79 s)
    (r : ExecutionReceipt 79 s) (D fields : Fin 78→List Bool)
    (out stack source tail : List Bool) (ref z B P : ℕ)
    (hr : runFrom p fuel c=some r) (hrB : r.steps≤fuel)
    (rh : r.final.heads=resultHeads out.length stack.length) (rt : r.final.tapes=resultData D B)
    (h20 : D 20=out) (h25 : D 25=List.replicate ref true) (h70 : D 70=source)
    (h73 : D 73=List.replicate B false) (h74 : D 74=stack++List.replicate z false)
    (h75 : D 75=RecoveryBoundedRowReload.word fields++tail)
    (h76 : D 76=List.replicate B true) (h77 : D 77=List.replicate (B+1) false)
    (hP : stack.length+z≤P) (hRef : 2*ref+2≤B)
    (hD : ∀ i,(D (RecoveryBoundedRowErase.work i)).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hp : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ q,runFrom (RecoveryBoundedGrammarContinue.after p)
      (fuel+1+RecoveryBoundedGrammarAfter.budget ref B fields)
      (Composition.leftConfig _ (ZeroPadding.config (stackCapacity P) c))=some q ∧
      q.steps≤fuel+1+RecoveryBoundedGrammarAfter.budget ref B fields ∧
      q.final.heads=resultHeads out.length (RecoveryBoundedAddress.pushed ref stack).length ∧
      q.final.tapes=bank (RecoveryBoundedGrammarBank.ready fields (ref+1) B out
        (RecoveryBoundedAddress.pushed ref stack) (RecoveryBoundedRowReload.word fields++tail) source) B P := by
  obtain ⟨a,ar,af,as,_⟩:=ZeroPadding.run_config p (stackCapacity P) _ _ r hr
  have ah : a.final.heads=resultHeads out.length stack.length := by rw [af];exact rh
  have aData : a.final.tapes=bank (cleaned D stack) B P := by
    rw [af]
    change (fun i=>ZeroPadding.pad (stackCapacity P i) (r.final.tapes i))=_
    rw [rt]
    exact clean_bank D stack z B P h74 hP
  have keep (i : Fin 78) (hi : i≠74) : cleaned D stack i=D i:=Function.update_of_ne hi _ _
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedGrammarContinue.join_run p fuel
    (ZeroPadding.config (stackCapacity P) c) out stack tail (cleaned D stack) fields ref B P
    a ar (as.le.trans hrB) ah aData
    (by rw [keep 25 (by decide)];exact h25) rfl
    (by rw [keep 73 (by decide)];exact h73)
    (by rw [keep 75 (by decide)];exact h75)
    (by rw [keep 76 (by decide)];exact h76)
    (by rw [keep 77 (by decide)];exact h77) hRef
    (by intro i;rw [keep _ (RecoveryBoundedRowErase.work_high i 74 (by decide))];exact hD i) hf hp
  refine ⟨q,qr,qs,qh,?_⟩
  rw [qt,RecoveryBoundedGrammarBank.after_ready fields (cleaned D stack) ref B out stack
    (RecoveryBoundedRowReload.word fields++tail) source
    (by rw [keep 20 (by decide)];exact h20)
    (by rw [keep 70 (by decide)];exact h70)
    (by rw [keep 73 (by decide)];exact h73)
    (by rw [keep 75 (by decide)];exact h75)
    (by rw [keep 76 (by decide)];exact h76)
    (by rw [keep 77 (by decide)];exact h77)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarFinishChild
