import Proof.CaseAnalysis.WitnessFamilyLoad
import Proof.Amplification.RecoveryRowStructureField

/-! The one loaded raw sum and the one verdict write are exactly the
already-checked sum entry. This is a tape identity, not another parser
or serializer; the family source remains outside the sum bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoad
open LocalBitMultitape RecoveryRootRound
open private core_data_other from Proof.CaseAnalysis.WitnessSumReader
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loaded (H : ℕ) (bits : List Bool) (base : Fin 3061 → List Bool) :=
  Function.update (Function.update base 2534 (ZeroPadding.pad H (frame bits))) 724 [false]

theorem loaded_input (P H b core W L T : ℕ) (bits arity out native counts : List Bool)
    (ambient : Fin 94 → List Bool) :
    loaded H bits (SumStorage.data P H b core W L T arity out native counts ambient)=
      SumDock.input P H b core W L T bits arity out native counts ambient := by
  funext i
  refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ i
  · intro j
    by_cases h724:j=724
    · subst j
      change loaded H bits (SumStorage.data P H b core W L T arity out native counts ambient) (724 : Fin 3061)=_
      unfold loaded
      rw [Function.update_self]
      rfl
    have h724':j.castAdd 528≠(724 : Fin 3061):=by intro h;exact h724 (Fin.ext (congrArg (fun i : Fin 3061=>i.val) h))
    have hraw:j.castAdd 528≠(2534 : Fin 3061):=by
      intro h;have hv:=congrArg Fin.val h;change j.val=2534 at hv;omega
    simp only [loaded,Function.update_of_ne h724',Function.update_of_ne hraw,
      SumStorage.data,SumDock.input,Fin.addCases_left]
    by_cases h722:j=722
    · subst j
      change SumDock.coreData P H b core W L _ out native _ true ambient
          ((((((2 : Fin 5).natAdd 720).castAdd 101).castAdd 1).castAdd 1705).castAdd 1) =
        SumDock.coreData P H b core W L _ out native _ false ambient
          ((((((2 : Fin 5).natAdd 720).castAdd 101).castAdd 1).castAdd 1705).castAdd 1)
      simp only [SumDock.coreData,Fin.addCases_left,TermRound.data,TermCommit.data,TermMass.data,
        TermRead.data,Fin.addCases_right]
      rfl
    by_cases h2532:j=2532
    · subst j
      change SumDock.coreData P H b core W L _ out native _ true ambient ((0 : Fin 1).natAdd 2532)=
        SumDock.coreData P H b core W L _ out native _ false ambient ((0 : Fin 1).natAdd 2532)
      simp only [SumDock.coreData,Fin.addCases_right]
    exact core_data_other P H b core W L (List.replicate H false) (List.replicate H false) out native
      (List.replicate H false) (List.replicate H false) true false ambient j h722 h724 h2532
  · intro j
    have h724:j.natAdd 2533≠(724 : Fin 3061):=by
      intro h;have hv:=congrArg Fin.val h;change 2533+j.val=724 at hv;omega
    simp only [loaded,Function.update_of_ne h724]
    by_cases h1:j=1
    · subst j
      change Function.update (SumStorage.data P H b core W L T arity out native counts ambient)
        (2534 : Fin 3061) (ZeroPadding.pad H (frame bits)) 2534=_
      rw [Function.update_self]
      rfl
    have hraw:j.natAdd 2533≠(2534 : Fin 3061):=by
      intro h;have hv:=congrArg Fin.val h;apply h1;apply Fin.ext;change 2533+j.val=2534 at hv;omega
    simp only [Function.update_of_ne hraw,SumStorage.data,SumDock.input,Fin.addCases_right]
    by_cases h501:j=501
    · subst j;rfl
    by_cases h502:j=502
    · subst j;rfl
    by_cases h526:j=526
    · subst j;rfl
    have hn1:j.val≠1:=by intro h;exact h1 (Fin.ext h)
    have hn501:j.val≠501:=by intro h;exact h501 (Fin.ext h)
    have hn502:j.val≠502:=by intro h;exact h502 (Fin.ext h)
    have hn526:j.val≠526:=by intro h;exact h526 (Fin.ext h)
    simp only [SumStorage.extra,if_neg h501,if_neg h502,if_neg h526,
      SumDock.extra,if_neg hn1,if_neg hn501,if_neg hn502,if_neg hn526]

theorem loaded_data (H : ℕ) (bits source : List Bool) (base : Fin 3061 → List Bool) :
    Function.update (data H (Function.update base 2534 (ZeroPadding.pad H (frame bits))) source) 724 [false]=
      data H (loaded H bits base) source := by
  change Function.update (Fin.addCases (m:=3061) (n:=2) (motive:=fun _=>List Bool)
      (Function.update base 2534 (ZeroPadding.pad H (frame bits))) ![source,List.replicate H false])
      ((724 : Fin 3061).castAdd 2) [false]=_
  rw [←RecoveryRowStructure.bank_update_left]
  rfl

noncomputable def prepare:=Composition.machine loader prime
def budget (bits : List Bool):=4*bits.length+5

theorem prepare_run (H : ℕ) (bits pre tail : List Bool) (baseHeads : Fin 3061 → ℕ)
    (base : Fin 3061 → List Bool) (hh : baseHeads 2534=0) (hb : base 2534=List.replicate H false)
    (hflagHead : baseHeads 724=0) (hflag : base 724=[true]) (hraw : 2*bits.length+1 ≤ H) :
    ∃ r,runFrom prepare (budget bits)
      ⟨prepare.start,heads pre.length baseHeads,data H base (pre++frame bits++tail)⟩=some r ∧
      r.steps ≤ budget bits ∧ r.final.heads=heads (pre.length+2*bits.length+1) baseHeads ∧
      r.final.tapes=data H (loaded H bits base) (pre++frame bits++tail) := by
  obtain ⟨first,hfirst,fs,fh,ft⟩:=load_run H bits pre tail baseHeads base hh hb hraw
  obtain ⟨last,hlast,ls,lh,lt⟩:=prime_run (heads (pre.length+2*bits.length+1) baseHeads)
    (data H (Function.update base 2534 (ZeroPadding.pad H (frame bits))) (pre++frame bits++tail))
    hflagHead (by
      change Function.update base 2534 (ZeroPadding.pad H (frame bits)) 724=[true]
      rw [Function.update_of_ne (by decide)];exact hflag)
  have lastRun : runFrom prime 1 ⟨prime.start,first.final.heads,first.final.tapes⟩=some last := by
    rw [fh,ft];exact hlast
  obtain ⟨r,run,rs,rh,rt⟩:=joined loader prime (4*bits.length+3) 1 _ _ first last hfirst lastRun (by omega) (by omega)
  have eq:4*bits.length+3+1+1=budget bits:=by unfold budget;omega
  rw [eq] at run rs
  refine ⟨r,run,rs,rh.trans lh,?_⟩
  rw [rt,lt,loaded_data]

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoad
