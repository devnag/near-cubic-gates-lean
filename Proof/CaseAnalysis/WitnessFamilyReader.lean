import Proof.CaseAnalysis.WitnessFamilyDock

/-! The original canonical family header is docked once into the loop's
actual fields. Every raw header has a total run and exact decision;
only the subsequent enclosing gate decides whether to enter the loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyDock
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem core_other (H : ℕ) (base : Fin 3061 → List Bool) (flag : Bool)
    (source nextSource driver nextDriver : List Bool) (i : Fin 3064)
    (h3061 : i≠3061) (h3063 : i≠3063) (h724 : i≠724) :
    coreData H base source driver i=
      coreData H (Function.update base 724 [flag]) nextSource nextDriver i := by
  revert h3061 h3063 h724
  refine Fin.addCases (m:=3063) (n:=1) ?_ ?_ i
  · intro j
    simp only [coreData,Fin.addCases_left]
    refine Fin.addCases (m:=3061) (n:=2) ?_ ?_ j
    · intro j _ _ hj
      have hn:j≠724:=by intro h;subst j;exact hj rfl
      simp only [FamilyLoad.data,Fin.addCases_left,Function.update_of_ne hn]
    · intro j hj _ _
      fin_cases j
      · exact (hj rfl).elim
      · simp only [FamilyLoad.data,Fin.addCases_right]
        rfl
  · intro j _ hj _
    fin_cases j
    exact (hj rfl).elim

theorem header_run (H V : ℕ) (bits : List Bool) (baseHeads : Fin 3061 → ℕ) (base : Fin 3061 → List Bool)
    (hhead : baseHeads 724=0) (hflag : base 724=[false]) (hraw : 2*bits.length+1 ≤ H)
    (hbudget : FamilyCount.budget bits V+1 ≤ H) :
    ∃ after r,runFrom reader (FamilyCount.budget bits V) ⟨reader.start,heads baseHeads,input H V bits base⟩=some r ∧
      r.steps ≤ FamilyCount.budget bits V ∧ r.final.heads=heads baseHeads ∧
      r.final.tapes=Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>List Bool)
        (coreData H (Function.update base 724 [FamilyCount.accepted bits V])
          ((FamilyFields.words bits).flatMap frame++FamilyFields.tail H bits)
          (ZeroPadding.pad H (CompareMachine.word (FamilyCount.count bits)))) after ∧
      after 174=List.replicate V true ∧ r.final.heads 724=0 ∧ r.final.tapes 724=[FamilyCount.accepted bits V] := by
  obtain ⟨bank,⟨small,hsmall,st,sh,ss⟩,actual,stream,count,flag,_support⟩:=FamilyFields.header_run H V bits hraw hbudget
  obtain ⟨r,run,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots slots_injective FamilyCount.machine _
    (heads baseHeads) (input H V bits base) _ (heads_reader baseHeads hhead) (input_reader H V bits base hflag) small hsmall
  have rhfull:r.final.heads=heads baseHeads:=by
    funext i
    by_cases hs:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh,sh,heads_reader baseHeads hhead]
    · exact (keep i (by simpa using hs)).1
  let after:=fun i : Fin 177=>r.final.tapes (i.natAdd 3064)
  have fields (i : Fin 177):r.final.tapes (slots i)=bank i:=by rw [rt,st]
  refine ⟨after,r,run,rs.trans_le ss,rhfull,?_,?_,?_,(fields 172).trans flag⟩
  · funext i
    refine Fin.addCases (m:=3064) (n:=177) ?_ ?_ i
    · intro j
      simp only [Fin.addCases_left]
      by_cases hs:j=3061
      · subst j;exact (fields 30).trans stream
      by_cases hd:j=3063
      · subst j;exact (fields 41).trans count
      by_cases hf:j=724
      · subst j;exact (fields 172).trans flag
      rw [(keep _ (core_outside j hs hd hf)).2,input,Fin.addCases_left]
      exact core_other H base (FamilyCount.accepted bits V) (List.replicate H false) _ (List.replicate H false) _ j hs hd hf
    · intro j;simp only [Fin.addCases_right,after]
  · change r.final.tapes (slots 174)=List.replicate V true
    exact (fields 174).trans actual
  · rw [rhfull];exact hhead

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyDock
