import Proof.CaseAnalysis.RowsCountBinary

/-! The canonical list's actual count supplies its binary value and a top
domain template. Both zero and positive lists use the same counted input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCountWord
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (n : ℕ) (i : Fin 14) : List Bool:=if i=0 then CompareMachine.word n else []
def old (i : Fin 5) : Fin 14:=i.castAdd 9
def slots : Fin 10→Fin 14:=![1,5,6,7,8,9,10,11,12,13]
noncomputable def first:=RecoveryFocus.machine old MatrixTemplateCopy.resetMachine
noncomputable def second:=RecoveryFocus.machine slots CloseoutRowsCountBinary.machine
noncomputable def machine:=Composition.machine first second
def budget (n : ℕ):=16*n^2+76*n+49

theorem old_injective : Function.Injective old:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 14=>k.val) h)

theorem word_run (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget n) (input n) out ∧
      out 5=List.replicate n true ∧ out 7=UnaryTemplate.tape n ∧
      out 9=frame (CloseoutRowsCountBinary.bits n) := by
  obtain ⟨r,hr,h1,_h2,_h3,hh,hs⟩:=MatrixTemplateCopy.word_run n
  have hw:ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*n+12)
      (MatrixTemplateCopy.wordInput n) r.final.tapes:=⟨r,hr,rfl,hh,hs.le⟩
  have hf:=hw.focus old old_injective (input n) (by intro i;fin_cases i <;> rfl)
  let middle:=install old (input n) r.final.tapes
  have fresh (i : Fin 14) (hi:5 ≤ i.val) : middle i=[]:=by
    rw [show middle=install old (input n) r.final.tapes by rfl,install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg (fun k : Fin 14=>k.val) hj
      change j.val=i.val at hv;omega)]
    simp only [input,if_neg (show i≠0 by intro h;subst i;omega)]
  obtain ⟨co,hc,c1,c3,c5⟩:=CloseoutRowsCountBinary.count_run n
  have hc':=hc.focus slots (by decide) middle (by
    intro i;fin_cases i
    · exact (install_slot old old_injective _ _ 1).trans h1
    all_goals exact fresh _ (by decide))
  have hall:=ClockJoin.join first second _ _ _ _ _ hf hc'
  have ht:4*n+12+1+CloseoutRowsCountBinary.budget n=budget n:=by
    unfold CloseoutRowsCountBinary.budget budget;omega
  rw [ht] at hall
  exact ⟨_,hall,(install_slot slots (by decide) _ co 1).trans c1,
    (install_slot slots (by decide) _ co 3).trans c3,
    (install_slot slots (by decide) _ co 5).trans c5⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCountWord
