import Proof.CaseAnalysis.WitnessFamilyPrepare

/-! Exact sparse cold input for the whole family. Every erased coordinate
is genuinely blank before the paid sweeps; source policy and zero mass
are the retained coordinates of the already checked family entry. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyInput
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def target (P H b V T core W L : ℕ) (bits arity out native counts : List Bool) (ambient : Fin 94 → List Bool):=
  FamilyDock.input H V bits (Function.update
    (SumStorage.data P H b core W L T arity out native counts ambient) 724 [false])
def blanked (target : Fin 3241 → List Bool) (i : Fin 3241):=
  if FamilyBank.parser i || FamilyBank.family i then []
  else if i=721 ∨ i=2531 ∨ i=724 then [] else target i

theorem parser_tapes (P H b V T core W L : ℕ) (bits arity out native counts : List Bool)
    (ambient : Fin 94 → List Bool) (hP : 1 ≤ P) (i : Fin 3241)
    (hi : FamilyBank.parser i=true) (h149 : i≠149) :
    target P H b V T core W L bits arity out native counts ambient i=List.replicate P false:=by
  revert hi h149
  refine Fin.addCases (m:=3064) (n:=177) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=3063) (n:=1) ?_ ?_ j
    · intro j
      refine Fin.addCases (m:=3061) (n:=2) ?_ ?_ j
      · intro j
        refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ j
        · intro j
          refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ j
          · intro j
            refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ j
            · intro j
              refine Fin.addCases (m:=826) (n:=1) ?_ ?_ j
              · intro j
                refine Fin.addCases (m:=725) (n:=101) ?_ ?_ j
                · intro j
                  refine Fin.addCases (m:=720) (n:=5) ?_ ?_ j
                  · intro j hi hn
                    have hn149:j.val≠149:=by intro h;exact hn (Fin.ext h)
                    have hn724:((((((j.castAdd 5).castAdd 101).castAdd 1).castAdd 1705).castAdd 1).castAdd 528 : Fin 3061)≠724:=by
                      apply Fin.ne_of_val_ne;change j.val≠724;omega
                    simp only [target,FamilyDock.input,FamilyDock.coreData,FamilyLoad.data,Fin.addCases_left,
                      Function.update_of_ne hn724,SumStorage.data,SumDock.coreData,TermRound.data,TermCommit.data,
                      TermMass.data,TermRead.data,TermPadded.input,TermCoefficient.input,
                      if_neg hn149]
                    by_cases h1:j.val=1
                    · simp only [if_pos h1]
                      rw [CloseoutRowsIntegerReady.pad_empty_frame P hP]
                    · simp [h1,ZeroPadding.pad]
                  · intro j hi _
                    fin_cases j
                    all_goals first
                      | (simp only [FamilyBank.parser,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi;omega)
                      | rfl
                · intro j
                  refine Fin.addCases (m:=94) (n:=7) ?_ ?_ j
                  · intro j hi _
                    simp only [FamilyBank.parser,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi
                    omega
                  · intro j _ _
                    have hn724 : (((((j.natAdd 94).natAdd 725).castAdd 1).castAdd 1705).castAdd 1).castAdd 528 ≠ (724 : Fin 3061):=by
                      apply Fin.ne_of_val_ne
                      change 725+(94+j.val)≠724
                      omega
                    simp only [target,FamilyDock.input,FamilyDock.coreData,FamilyLoad.data,Fin.addCases_left,
                      Function.update_of_ne hn724,
                      SumStorage.data,SumDock.coreData,TermRound.data,TermCommit.data,TermMass.data,
                      Fin.addCases_right,TermMass.tail]
              · intro j hi _
                simp only [FamilyBank.parser,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi;omega
            · intro j hi _
              simp only [FamilyBank.parser,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi;omega
          · intro j hi _
            simp only [FamilyBank.parser,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi;omega
        · intro j hi _
          simp only [FamilyBank.parser,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi;omega
      · intro j hi _
        simp only [FamilyBank.parser,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi;omega
    · intro j hi _
      simp only [FamilyBank.parser,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi;omega
  · intro j hi _
    simp only [FamilyBank.parser,Fin.val_natAdd,decide_eq_true_eq] at hi;omega

theorem family_tapes (P H b V T core W L : ℕ) (bits arity out native counts : List Bool)
    (ambient : Fin 94 → List Bool) (i : Fin 3241)
    (hi : FamilyBank.family i=true) (hraw : i≠3064) :
    target P H b V T core W L bits arity out native counts ambient i=List.replicate H false:=by
  by_cases h722:i=722
  · subst i;rfl
  revert hi hraw h722
  refine Fin.addCases (m:=3064) (n:=177) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=3063) (n:=1) ?_ ?_ j
    · intro j
      refine Fin.addCases (m:=3061) (n:=2) ?_ ?_ j
      · intro j
        refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ j
        · intro j
          refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ j
          · intro j
            refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ j
            · intro j hi _ hn
              have hv:j.val≠722:=by intro h;exact hn (Fin.ext h)
              simp only [FamilyBank.family,Fin.val_castAdd,decide_eq_true_eq] at hi
              omega
            · intro j hi _ _
              simp only [FamilyBank.family,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi
              have h1674:j.val≠1674:=by omega
              have h1688:j.val≠1688:=by omega
              have h1698:j.val≠1698:=by omega
              have h1699:j.val≠1699:=by omega
              have h1703:j.val≠1703:=by omega
              have h1704:j.val≠1704:=by omega
              have hn724 : (((j.natAdd 827).castAdd 1).castAdd 528 : Fin 3061)≠724:=by
                apply Fin.ne_of_val_ne;change 827+j.val≠724;omega
              simp only [target,FamilyDock.input,FamilyDock.coreData,FamilyLoad.data,Fin.addCases_left,
                Function.update_of_ne hn724,SumStorage.data,SumDock.coreData,TermRound.data,Fin.addCases_right,
                TermEnvironment.tapes,h1674,h1688,h1698,h1699,h1703,h1704,ite_false]
          · intro j _ _ _
            have he:j=0:=Fin.eq_zero j
            subst j;rfl
        · intro j hi _ _
          simp only [FamilyBank.family,Fin.val_castAdd,Fin.val_natAdd,decide_eq_true_eq] at hi
          have h501:j≠501:=by intro h;subst j;omega
          have h502:j≠502:=by intro h;subst j;omega
          have h526:j≠526:=by intro h;subst j;omega
          have hn724 : j.natAdd 2533 ≠ (724 : Fin 3061):=by
            apply Fin.ne_of_val_ne;change 2533+j.val≠724;omega
          simp only [target,FamilyDock.input,FamilyDock.coreData,FamilyLoad.data,Fin.addCases_left,
            Function.update_of_ne hn724,SumStorage.data,Fin.addCases_right,SumStorage.extra,if_neg h501,if_neg h502,if_neg h526]
      · intro j _ _ _
        fin_cases j <;> rfl
    · intro j _ _ _
      have he:j=0:=Fin.eq_zero j
      subst j;rfl
  · intro j hi hn _
    simp only [FamilyBank.family,Fin.val_natAdd,decide_eq_true_eq] at hi
    have h0:j.val≠0:=by intro h;exact hn (Fin.ext (by change 3064+j.val=3064;omega))
    have h174:j.val≠174:=by omega
    simp only [target,FamilyDock.input,Fin.addCases_right,FamilyDock.extra,if_neg h0,if_neg h174]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyInput
