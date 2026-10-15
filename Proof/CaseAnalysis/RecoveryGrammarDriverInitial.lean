import Proof.CaseAnalysis.RecoveryGrammarCompiled
import Proof.CaseAnalysis.RecoveryGrammarDriverBank

/-! The two fresh paid backing tapes become the actual finite drivers,
then one physical step positions both heads for the original grammar scan. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
open LocalBitMultitape Composition RecoveryBoundedGrammarDriver
open RecoveryBoundedGrammarCold (scanHeads scanData)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def twoData (A : Fin 112→List Bool) (x y : List Bool):=data (data A x) y

theorem update_bound (A : Fin 112→List Bool) (x y next : List Bool) :
    Function.update (twoData A x y) 112 next=twoData A next y := by
  funext i
  refine Fin.addCases (m:=113) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=112) (n:=1) (fun k=>?_) (fun k=>?_) j
    · have hk : ((k.castAdd 1).castAdd 1 : Fin 114)≠112 := by
        intro he;have hv:=congrArg Fin.val he;change k.val=112 at hv;omega
      simp only [Function.update_of_ne hk,twoData,data,Fin.addCases_left]
    · fin_cases k
      simp [twoData,data,Function.update,Fin.addCases]
  · fin_cases j
    simp [twoData,data,Function.update,Fin.addCases]

theorem update_count (A : Fin 112→List Bool) (x y next : List Bool) :
    Function.update (twoData A x y) 113 next=twoData A x next := by
  funext i
  refine Fin.addCases (m:=113) (n:=1) (fun j=>?_) (fun j=>?_) i
  · have hj : (j.castAdd 1 : Fin 114)≠113 := by
      intro he;have hv:=congrArg Fin.val he;change j.val=113 at hv;omega
    simp only [Function.update_of_ne hj,twoData,data,Fin.addCases_left]
  · fin_cases j
    simp [twoData,data,Function.update,Fin.addCases]

noncomputable def initial:=Composition.machine (Composition.machine (emit true) (emit false)) position
def initialBudget (bound count : ℕ):=((2*bound+8)+1+(2*count+8))+1+1

theorem initial_run (B bound count : ℕ) (H : Fin 112→ℕ) (A : Fin 112→List Bool)
    (hbound : bound+3≤B) (hcount : count+3≤B)
    (rawBound : A 102=ZeroPadding.pad B (List.replicate bound true))
    (rawCount : A 101=ZeroPadding.pad B (List.replicate count true))
    (log : A 78=List.replicate B false) (hb0 : H 102=0) (hc0 : H 101=0) (hl0 : H 78=0) :
    ∃ r,runFrom initial (initialBudget bound count)
      ⟨initial.start,scanHeads H 0 0,twoData A (List.replicate B false) (List.replicate B false)⟩=some r ∧
      r.steps ≤ initialBudget bound count ∧ r.final.heads=scanHeads H 1 1 ∧
      r.final.tapes=scanData A B bound count := by
  let wb:=ZeroPadding.pad B (CompareMachine.word (bound+1))
  let wc:=ZeroPadding.pad B (CompareMachine.word (count+1))
  obtain ⟨a,ar,as,ah,atapes⟩:=emit_run true B bound (scanHeads H 0 0)
    (twoData A (List.replicate B false) (List.replicate B false)) hbound
    (by intro j;fin_cases j <;> simp [ports,twoData,data,Fin.addCases,CloseoutRecoveryGrammarDriverReady.input,rawBound,log])
    (by intro j;fin_cases j <;> simp [ports,scanHeads,heads,Fin.addCases,hb0,hl0])
  change a.final.tapes=Function.update (twoData A _ _) 112 wb at atapes
  rw [update_bound] at atapes
  obtain ⟨b,br,bs,bh,bt⟩:=emit_run false B count (scanHeads H 0 0)
    (twoData A wb (List.replicate B false)) hcount
    (by intro j;fin_cases j <;> simp [ports,twoData,data,Fin.addCases,CloseoutRecoveryGrammarDriverReady.input,rawCount,log])
    (by intro j;fin_cases j <;> simp [ports,scanHeads,heads,Fin.addCases,hc0,hl0])
  change b.final.tapes=Function.update (twoData A _ _) 113 wc at bt
  rw [update_count] at bt
  have br' : runFrom (emit false) (2*count+8) (restart a.final (emit false).start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  obtain ⟨z,zr,zs,zh,zt⟩:=position_run H (twoData A wb wc)
  have zr' : runFrom position 1 (restart b.final position.start)=some z := by
    change runFrom _ _ ⟨_,b.final.heads,b.final.tapes⟩=some z
    rw [bh,bt]
    exact zr
  have first:=Composition.run_join (emit true) (emit false) _ _ _ a b ar br'
  have whole:=Composition.run_join (Composition.machine (emit true) (emit false)) position _ _ _
    (joinedReceipt a b) z first zr'
  refine ⟨joinedReceipt (joinedReceipt a b) z,whole,?_,zh,zt⟩
  change (a.steps+1+b.steps)+1+z.steps ≤ initialBudget bound count
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right as 1) bs) 1) zs.le

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
