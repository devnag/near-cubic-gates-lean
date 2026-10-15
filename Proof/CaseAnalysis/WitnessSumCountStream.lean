import Proof.CaseAnalysis.WitnessSumGuard
import Proof.CaseAnalysis.RowsCircuitCountHeader

/-! Emit the actual guarded per-sum term count once. The native count
stream delimits the unchanged coefficient and circuit streams in variable
order; the producer directly aliases the retained count at sum port504. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumCountStream
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 19) : Fin 528 :=
  ⟨if i.val=0 then 504 else if i.val=17 then 526 else if i.val=18 then 527 else 509+i.val,by split_ifs <;> omega⟩
noncomputable def machine := RecoveryFocus.machine slots CloseoutRowsCircuitCountHeader.machine
def extra (P : ℕ) (out : List Bool) (i : Fin 18) :=
  if i.val=16 then out else List.replicate P false
def extraHeads (out : List Bool) (i : Fin 18) := if i.val=16 then out.length else 0
def heads (out : List Bool) : Fin 528 → ℕ :=
  Fin.addCases (m:=510) (n:=18) (motive:=fun _=>ℕ) (fun _=>0) (extraHeads out)
def input (P : ℕ) (bank : Fin 510 → List Bool) (out : List Bool) : Fin 528 → List Bool :=
  Fin.addCases (m:=510) (n:=18) (motive:=fun _=>List Bool) bank (extra P out)

theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv := congrArg (fun k : Fin 528=>k.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem old_outside (i : Fin 510) (hi : i≠504) : ∀ j,slots j≠i.castAdd 18 := by
  intro j h
  have hv := congrArg (fun k : Fin 528=>k.val) h
  have hn : i.val≠504 := by intro h;exact hi (Fin.ext h)
  dsimp only [slots,Fin.val_castAdd] at hv
  split_ifs at hv <;> omega

theorem append_run (P : ℕ) (bits out : List Bool) (bank : Fin 510 → List Bool)
    (hcount : bank 504=ZeroPadding.pad P (List.replicate (SumFields.count bits) true))
    (hguard : bank 499=[true])
    (hn : SumFields.count bits ≤ P)
    (hc : EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ P) :
    ∃ result,runFrom machine (CloseoutRowsCircuitCountHeader.budget (SumFields.count bits))
        ⟨machine.start,heads out,input P bank out⟩=some result ∧
      result.steps ≤ CloseoutRowsCircuitCountHeader.budget (SumFields.count bits) ∧
      result.final.heads=heads (out++RepairRepresentation.natWord (SumFields.count bits)) ∧
      result.final.tapes 526=out++RepairRepresentation.natWord (SumFields.count bits) ∧
      result.final.tapes 510=ZeroPadding.pad P (List.replicate (SumFields.count bits) true) ∧
      result.final.tapes 527=List.replicate P false ∧
      result.final.tapes 499=[true] ∧
      (∀ i : Fin 510,i≠504 → result.final.tapes (i.castAdd 18)=bank i) ∧
      (∀ i : Fin 19,i≠17 → (result.final.tapes (slots i)).length ≤ P) := by
  obtain ⟨base,hr,rs,rh,rt,rc,rl,rb⟩ := CloseoutRowsCircuitCountHeader.header_run P (SumFields.count bits) out hn hc
  obtain ⟨r,run,_rf,steps,rheads,rtapes,keep⟩ := RecoveryFocus.dock slots slots_injective
    CloseoutRowsCircuitCountHeader.machine _ (heads out) (input P bank out) _
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i
        · exact hcount
        all_goals rfl) base hr
  have old (i : Fin 510) (hi : i≠504) : r.final.tapes (i.castAdd 18)=bank i := by
    simpa only [input,Fin.addCases_left] using (keep _ (old_outside i hi)).2
  refine ⟨r,run,steps ▸ rs,?_,(rtapes 17).trans rt,(rtapes 1).trans rc,(rtapes 18).trans rl,
    (old 499 (by decide)).trans hguard,old,fun i hi=>by rw [rtapes];exact rb i (by intro h;exact hi (Fin.ext h))⟩
  funext i
  by_cases hs : ∃ j,slots j=i
  · obtain ⟨j,rfl⟩ := hs
    rw [rheads,rh]
    fin_cases j <;> rfl
  · have hkeep := (keep i (by simpa using hs)).1
    have hne : i≠526 := by intro h;apply hs;exact ⟨17,h.symm⟩
    refine hkeep.trans ?_
    revert hne
    refine Fin.addCases (m:=510) (n:=18) ?_ ?_ i
    · intro j _;simp only [heads,Fin.addCases_left]
    · intro j hj
      have hj' : j.val≠16 := by intro h;exact hj (Fin.ext (by change 510+j.val=526;omega))
      simp only [heads,Fin.addCases_right,extraHeads,if_neg hj']

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumCountStream
