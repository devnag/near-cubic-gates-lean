import Proof.CaseAnalysis.WitnessFamilyInput

/-! The paid preparation output is exactly the existing full-family input,
including its two logs, original canonical family frame and coefficient
width. The sparse incoming tape bank supplies no private allocation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyReady
open LocalBitMultitape FamilyInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem prepared_eq (P H b V T core W L : ℕ) (bits arity out native counts : List Bool)
    (ambient : Fin 94 → List Bool) (hP : 1 ≤ P) :
    FamilyPrepare.output P H b bits (blanked (target P H b V T core W L bits arity out native counts ambient))=
      FamilyPrepare.tapes b bits (target P H b V T core W L bits arity out native counts ambient):=by
  let final:=target P H b V T core W L bits arity out native counts ambient
  funext i
  refine Fin.addCases (m:=3241) (n:=2) ?_ ?_ i
  · intro j
    by_cases h724:j=724
    · subst j;rfl
    by_cases h149:j=149
    · subst j;rfl
    by_cases hraw:j=3064
    · subst j;rfl
    by_cases h721:j=721
    · subst j;rfl
    by_cases h2531:j=2531
    · subst j;rfl
    have l724:j.castAdd 2≠(724 : Fin 3243):=by
      intro he;exact h724 (Fin.ext (congrArg (fun z : Fin 3243=>z.val) he))
    have l149:j.castAdd 2≠(149 : Fin 3243):=by
      intro he;exact h149 (Fin.ext (congrArg (fun z : Fin 3243=>z.val) he))
    have lraw:j.castAdd 2≠(3064 : Fin 3243):=by
      intro he;exact hraw (Fin.ext (congrArg (fun z : Fin 3243=>z.val) he))
    rw [FamilyPrepare.tapes,Fin.addCases_left]
    change Function.update (FamilyReload.output P H b bits
      (FamilyPrepare.tapes b bits (FamilyBank.output P H (blanked final)))) 724 [false] (j.castAdd 2)=final j
    rw [Function.update_of_ne l724,FamilyReload.output,Function.update_of_ne lraw,
      Function.update_of_ne l149,FamilyPrepare.tapes,Fin.addCases_left]
    cases hf:FamilyBank.family j with
    | true =>
      simp only [FamilyBank.output,SelectedErase.output,hf,ite_true]
      exact (family_tapes P H b V T core W L bits arity out native counts ambient j hf hraw).symm
    | false =>
      cases hp:FamilyBank.parser j with
      | true =>
        simp only [FamilyBank.output,SelectedErase.output,hf,hp,ite_true,if_neg h2531]
        exact (parser_tapes P H b V T core W L bits arity out native counts ambient hP j hp h149).symm
      | false =>
        simp only [FamilyBank.output,SelectedErase.output,hf,hp,Bool.false_eq_true,ite_false,if_neg h2531,if_neg h721,
          blanked,Bool.false_or,if_neg (show ¬(j=721 ∨ j=2531 ∨ j=724) by omega)]
  · intro j
    have h724:j.natAdd 3241≠(724 : Fin 3243):=by
      apply Fin.ne_of_val_ne;change 3241+j.val≠724;omega
    have h3064:j.natAdd 3241≠(3064 : Fin 3243):=by
      apply Fin.ne_of_val_ne;change 3241+j.val≠3064;omega
    have h149:j.natAdd 3241≠(149 : Fin 3243):=by
      apply Fin.ne_of_val_ne;change 3241+j.val≠149;omega
    simp only [FamilyPrepare.output,FamilyReload.output,Function.update_of_ne h724,
      Function.update_of_ne h3064,Function.update_of_ne h149,FamilyPrepare.tapes,Fin.addCases_right]

theorem prepare_run (P H b V T core W L : ℕ) (bits arity out native counts : List Bool)
    (ambient : Fin 94 → List Bool) (heads : Fin 3241 → ℕ) (hP : 1 ≤ P)
    (hb : b ≤ P) (hbits : 2*bits.length+1 ≤ H)
    (hh : ∀ i,FamilyBank.parser i=true ∨ FamilyBank.family i=true ∨
      i=720 ∨ i=721 ∨ i=2530 ∨ i=2531 → heads i=0) (h724 : heads 724=0) :
    ∃ r,runFrom FamilyPrepare.machine (FamilyPrepare.budget P H)
      ⟨FamilyPrepare.machine.start,FamilyPrepare.heads heads,
        FamilyPrepare.tapes b bits (blanked (target P H b V T core W L bits arity out native counts ambient))⟩=some r ∧
      r.steps ≤ FamilyPrepare.budget P H ∧ r.final.heads=FamilyPrepare.heads heads ∧
      r.final.tapes=FamilyPrepare.tapes b bits (target P H b V T core W L bits arity out native counts ambient):=by
  obtain ⟨r,run,rs,rh,rt⟩:=FamilyPrepare.prepare_run P H b bits heads
    (blanked (target P H b V T core W L bits arity out native counts ambient)) hb hbits hh
    (by intro i hi;simp only [blanked,hi,Bool.true_or,ite_true])
    (by intro i hi;simp only [blanked,hi,Bool.or_true,ite_true])
    (by rfl) (by rfl) (by rfl) (by rfl) h724 (by rfl)
  exact ⟨r,run,rs,rh,rt.trans (prepared_eq P H b V T core W L bits arity out native counts ambient hP)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyReady
