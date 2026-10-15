import Proof.CaseAnalysis.RecoveryGrammarFoldRun

/-! One paid save/count/erase/reload continuation serves all original
grammar workers. False backing under the nested stack is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarContinue
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (heads resultHeads resultData)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 78) : Fin 79:=j.castAdd 1
noncomputable def machine:=RecoveryFocus.machine slots RecoveryBoundedGrammarAfter.machine
def stackCapacity (P : ℕ) (i : Fin 79):=if i=74 then P else 0
def bank (A : Fin 78→List Bool) (B P : ℕ) (i : Fin 79):=
  ZeroPadding.pad (stackCapacity P i) (resultData A B i)
noncomputable def input (out stack : List Bool) (A : Fin 78→List Bool) (B P : ℕ):=
  (⟨machine.start,resultHeads out.length stack.length,bank A B P⟩ : Configuration 79 _)

theorem raw_run (out stack tail : List Bool) (A fields : Fin 78→List Bool) (ref B : ℕ)
    (ha : A 25=List.replicate ref true) (hs : A 74=stack) (hw : A 73=List.replicate B false)
    (hp : A 75=RecoveryBoundedRowReload.word fields++tail)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hB : 2*ref+2≤B) (hA : ∀ i,(A (RecoveryBoundedRowErase.work i)).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hpB : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ r,runFrom machine (RecoveryBoundedGrammarAfter.budget ref B fields)
      ⟨machine.start,resultHeads out.length stack.length,resultData A B⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarAfter.budget ref B fields ∧
      r.final.heads=resultHeads out.length (RecoveryBoundedAddress.pushed ref stack).length ∧
      r.final.tapes=resultData (RecoveryBoundedGrammarAfter.output fields A ref B stack) B := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedGrammarAfter.after_run out stack tail A fields ref B
    ha hs hw hp hd hl hB hA hf hpB
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots (Fin.castAdd_injective 78 1)
    RecoveryBoundedGrammarAfter.machine _ (resultHeads out.length stack.length) (resultData A B)
    ⟨RecoveryBoundedGrammarAfter.machine.start,heads out stack,A⟩
    (by intro j;simp only [slots,resultHeads,Fin.addCases_left];rfl)
    (by intro j;simp only [slots,resultData,Fin.addCases_left]) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    refine Fin.addCases (m:=78) (n:=1) ?_ ?_ i
    · intro j
      change r.final.heads (slots j)=_
      rw [rh j,ph]
      simp only [resultHeads,Fin.addCases_left]
      rfl
    · intro j;fin_cases j
      exact (rkeep 78 (by intro j h;have hv:=congrArg Fin.val h;change j.val=78 at hv;omega)).1
  · funext i
    refine Fin.addCases (m:=78) (n:=1) ?_ ?_ i
    · intro j
      change r.final.tapes (slots j)=_
      rw [rt j,pt]
      simp only [resultData,Fin.addCases_left]
    · intro j;fin_cases j
      exact (rkeep 78 (by intro j h;have hv:=congrArg Fin.val h;change j.val=78 at hv;omega)).2

theorem continue_run (out stack tail : List Bool) (A fields : Fin 78→List Bool) (ref B P : ℕ)
    (ha : A 25=List.replicate ref true) (hs : A 74=stack) (hw : A 73=List.replicate B false)
    (hp : A 75=RecoveryBoundedRowReload.word fields++tail)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hB : 2*ref+2≤B) (hA : ∀ i,(A (RecoveryBoundedRowErase.work i)).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hpB : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ r,runFrom machine (RecoveryBoundedGrammarAfter.budget ref B fields)
      (input out stack A B P)=some r ∧
      r.steps≤RecoveryBoundedGrammarAfter.budget ref B fields ∧
      r.final.heads=resultHeads out.length (RecoveryBoundedAddress.pushed ref stack).length ∧
      r.final.tapes=bank (RecoveryBoundedGrammarAfter.output fields A ref B stack) B P := by
  obtain ⟨p,pr,ps,ph,pt⟩:=raw_run out stack tail A fields ref B ha hs hw hp hd hl hB hA hf hpB
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config machine (stackCapacity P) _ _ p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · rw [rf]
    exact ph
  · rw [rf]
    change (fun i=>ZeroPadding.pad (stackCapacity P i) (p.final.tapes i))=_
    rw [pt]
    rfl

variable {s : ℕ}
noncomputable def after (p : Machine 79 s):=Composition.machine p machine

theorem join_run (p : Machine 79 s) (fuel : ℕ) (c : Configuration 79 s)
    (out stack tail : List Bool) (A fields : Fin 78→List Bool) (ref B P : ℕ)
    (r : ExecutionReceipt 79 s) (hr : runFrom p fuel c=some r) (hrB : r.steps≤fuel)
    (rh : r.final.heads=resultHeads out.length stack.length) (rt : r.final.tapes=bank A B P)
    (ha : A 25=List.replicate ref true) (hs : A 74=stack) (hw : A 73=List.replicate B false)
    (hp : A 75=RecoveryBoundedRowReload.word fields++tail)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hB : 2*ref+2≤B) (hA : ∀ i,(A (RecoveryBoundedRowErase.work i)).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hpB : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ q,runFrom (after p) (fuel+1+RecoveryBoundedGrammarAfter.budget ref B fields)
      (Composition.leftConfig _ c)=some q ∧
      q.steps≤fuel+1+RecoveryBoundedGrammarAfter.budget ref B fields ∧
      q.final.heads=resultHeads out.length (RecoveryBoundedAddress.pushed ref stack).length ∧
      q.final.tapes=bank (RecoveryBoundedGrammarAfter.output fields A ref B stack) B P := by
  obtain ⟨q,qr,qs,qh,qt⟩:=continue_run out stack tail A fields ref B P ha hs hw hp hd hl hB hA hf hpB
  have qr' : runFrom machine (RecoveryBoundedGrammarAfter.budget ref B fields)
      (restart r.final machine.start)=some q := by
    change runFrom _ _ ⟨_,r.final.heads,r.final.tapes⟩=some q
    rw [rh,rt]
    exact qr
  have whole:=Composition.run_join p machine _ _ _ r q hr qr'
  refine ⟨joinedReceipt r q,whole,?_,qh,qt⟩
  change r.steps+1+q.steps≤_
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarContinue
