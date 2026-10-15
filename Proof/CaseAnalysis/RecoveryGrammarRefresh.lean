import Proof.CaseAnalysis.RecoveryGrammarPorts

/-! Refresh the actual next-atom packet: paid erasure, original framed
scalar print, and physical rewind. All graph and current-atom fields survive. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 3→Fin 112:=![75,76,77]
noncomputable def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def refresh (p : Selection):=Composition.machine erase (printer p)
def refreshBudget (C index value limit upper B : ℕ):=
  (2*B+4)+1+RecoveryBoundedGrammarPrototype.readyBudget C index value limit upper B

theorem erase_run (B : ℕ) (H : Fin 112→ℕ) (A : Fin 112→List Bool)
    (hH : ∀ j,H (eraseSlots j)=0) (hA : (A 75).length≤B)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false) :
    ∃ r,runFrom erase (2*B+4) ⟨erase.start,H,A⟩=some r ∧ r.steps≤2*B+4 ∧
      r.final.heads=H ∧ r.final.tapes=Function.update A 75 (List.replicate B false) := by
  have e:=RecoveryScratchErase.erase_ready B (B+1) (fun _ : Fin 1=>A 75) (by intro j;exact hA)
  obtain ⟨r,rr,rh,rt,rs⟩:=e.focus_at eraseSlots (by decide) H A
    (by intro j;fin_cases j;rfl;exact hd;exact hl) hH
  refine ⟨r,rr,rs.le,rh,?_⟩
  rw [rt]
  funext i
  by_cases hi : ∃ j,eraseSlots j=i
  · obtain ⟨j,rfl⟩:=hi
    rw [install_slot _ (by decide : Function.Injective eraseSlots)]
    fin_cases j
    · rfl
    · change List.replicate B true=Function.update A 75 (List.replicate B false) 76
      rw [Function.update_of_ne (by decide)]
      exact hd.symm
    · change List.replicate (max (B+1) (B+1)) false=Function.update A 75 (List.replicate B false) 77
      rw [Nat.max_self,Function.update_of_ne (by decide)]
      exact hl.symm
  · rw [install_other _ _ _ i (by intro j he;exact hi ⟨j,he⟩)]
    exact (Function.update_of_ne (fun he=>hi ⟨0,he.symm⟩) _ _).symm

theorem refresh_run (p : Selection) (C index value limit upper B : ℕ)
    (H : Fin 112→ℕ) (A : Fin 112→List Bool)
    (hH : ∀ j,H (scalarPorts p j)=0) (hHs : H 75=0) (hHd : H 76=0) (hHl : H 73=0)
    (hHe : H 77=0)
    (hA : ∀ j,A (scalarPorts p j)=ZeroPadding.pad B
      (RecoveryBoundedGrammarPrototype.scalarValues C index value limit upper j))
    (hAl : A 73=List.replicate B false) (hAd : A 76=List.replicate B true)
    (hAe : A 77=List.replicate (B+1) false) (hAs : (A 75).length≤B)
    (bIndex : 2*index+4≤B) (bLimit : 2*limit+4≤B) (bValue : 2*value+4≤B)
    (bUpper : 2*upper+4≤B) (bC : 2*C+4≤B)
    (bp : (RecoveryBoundedRowReload.word (RecoveryBoundedGrammarPrototype.fields C index value limit upper)).length≤B) :
    ∃ r,runFrom (refresh p) (refreshBudget C index value limit upper B)
      ⟨(refresh p).start,H,A⟩=some r ∧ r.steps≤refreshBudget C index value limit upper B ∧
      r.final.heads=H ∧ r.final.tapes=Function.update A 75 (ZeroPadding.pad B
        (RecoveryBoundedRowReload.word (RecoveryBoundedGrammarPrototype.fields C index value limit upper))) := by
  obtain ⟨a,ar,as,ah,atapes⟩:=erase_run B H A
    (by intro j;fin_cases j;exact hHs;exact hHd;exact hHe) hAs hAd hAe
  obtain ⟨b,br,bs,bh,bt⟩:=printer_run p C index value limit upper B H
    (Function.update A 75 (List.replicate B false)) hH hHs hHd hHl
    (by
      intro j
      rw [Function.update_of_ne (show scalarPorts p j≠75 from by
        intro he;have hv:=scalarPorts_high p j;rw [he] at hv;change 79 ≤ 75 at hv;omega)]
      exact hA j)
    (by rw [Function.update_of_ne (by decide)];exact hAl)
    (by rw [Function.update_of_ne (by decide)];exact hAd) rfl
    bIndex bLimit bValue bUpper bC bp
  have br' : runFrom (printer p) (RecoveryBoundedGrammarPrototype.readyBudget C index value limit upper B)
      (restart a.final (printer p).start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have whole:=Composition.run_join erase (printer p) _ _ _ a b ar br'
  refine ⟨joinedReceipt a b,whole,?_,bh,?_⟩
  · change a.steps+1+b.steps≤refreshBudget C index value limit upper B
    unfold refreshBudget
    omega
  · change b.final.tapes=_
    rw [bt,Function.update_idem]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
