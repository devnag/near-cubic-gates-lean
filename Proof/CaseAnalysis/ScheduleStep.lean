import Proof.CaseAnalysis.ScheduleStepTest
import Proof.CaseAnalysis.ScheduleStepReplace
import Proof.CaseAnalysis.ScheduleStepReset

/-! One complete ordinary schedule iteration: paid loads, actual test,
conditional best replacement, full workspace return, and index increment. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Step
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def prepare (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :=
  Composition.machine (load sources k D) (test sources k D copies clock)
def suffix (sources : EightSources) (k D : Nat) := Composition.machine (eraseWork sources k D) (increment sources k D)
def numberStates {t states : Nat} (_ : Machine t states) := states
def sizes (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) : Fin 3→Nat :=
  ![numberStates (prepare sources k D copies clock),9,9]
def programs (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :
    (j : Fin 3)→Machine (tapes sources k D) (sizes sources k D copies clock j)
  | ⟨0,_⟩=>prepare sources k D copies clock
  | ⟨1,_⟩=>replace sources k D
  | ⟨2,_⟩=>suffix sources k D
  | ⟨j+3,h⟩=>False.elim (by omega)
def next (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (j : Fin 3) (_ : Fin (sizes sources k D copies clock j)) (bits : Fin (tapes sources k D)→Bool) : Option (Fin 3) :=
  if j.val=0 then if bits (flagTarget sources k D) then some 1 else some 2
  else if j.val=1 then some 2 else none
def machine (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :=
  RecoveryCalls.machine (sizes sources k D copies clock) (programs sources k D copies clock) 0 (next sources k D copies clock)
def prefixBudget (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (s n : Nat) :=
  ((2*s+6)+1+(2*n+6))+1+Test.budget sources k D copies clock s n
def suffixBudget (C s : Nat) := (2*C+4)+1+(2*s+5)
def budget (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (C s n : Nat) :=
  prefixBudget sources k D copies clock s n+((2*C+4)+1+(2*2^s+6))+suffixBudget C s+3
def nextBest (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (s n best : Nat) :=
  if CloseoutLanguage.widthAt sources k clock copies D s ≤ n/2 then 2^s else best

theorem suffix_run (sources : EightSources) (k D C s n best : Nat)
    (ambient : Fin (tapes sources k D)→List Bool)
    (hwork : ∀ i,(ambient (work sources k D i)).length ≤ C)
    (hp : ∀ i,ambient (port sources k D i)=persistent C s n best i) :
    ClockJoin.ReadyRun (suffix sources k D) (suffixBudget C s) ambient (bank sources k D C (s+1) n best) :=
  ClockJoin.join _ _ _ _ _ _ _ (erase_run sources k D C s n best ambient hwork hp)
    (increment_run sources k D C s n best)

theorem port_injective (sources : EightSources) (k D : Nat) : Function.Injective (port sources k D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  change workTapes sources k D+a.val=workTapes sources k D+b.val at hv
  omega

theorem step_run (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (C s n best : Nat) (hD : 1 ≤ D)
    (hs : s+2 ≤ C) (hn : n+2 ≤ C) (hbest : best ≤ C) (hN : 2^s+2 ≤ C)
    (hC : Test.budget sources k D copies clock s n+1 ≤ C) :
    ClockJoin.ReadyRun (machine sources k D copies clock) (budget sources k D copies clock C s n)
      (bank sources k D C s n best) (bank sources k D C (s+1) n (nextBest sources k D copies clock s n best)) := by
  obtain ⟨a,ha,ap,aw,ac,atape,af⟩:=test_run sources k D copies clock s n C best hD (by omega) (by omega) hC
  have hp:=ClockJoin.join _ _ _ _ _ _ _ (load_run sources k D C s n best hs hn) ha
  obtain ⟨tp,htp,hprefix⟩:=Reusable.exact_time hp
  have hscan : readTapeBit (a (flagTarget sources k D)) 0=
      decide (CloseoutLanguage.widthAt sources k clock copies D s ≤ n/2) := by
    rw [af,ZeroPadding.read_pad]
    rfl
  let ss:=sizes sources k D copies clock
  let pp:=programs sources k D copies clock
  let nn:=next sources k D copies clock
  by_cases hfit : CloseoutLanguage.widthAt sources k clock copies D s ≤ n/2
  · have hfirst:=hprefix.call ss pp 0 nn 0 1 (by intro q;simp [nn,next,hscan,hfit])
    have hb : (a (port sources k D 2)).length ≤ C := by
      rw [ap 2]
      change (ZeroPadding.pad C (List.replicate best true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate,max_eq_left hbest]
    have hreplace:=replace_run sources k D C (2^s) a hN hb (ap 3) (ap 4) atape ac
    let b:=Function.update a (port sources k D 2) (ZeroPadding.pad C (List.replicate (2^s) true))
    have bp (i : Fin 5) : b (port sources k D i)=persistent C s n (2^s) i := by
      by_cases hi : i=2
      · subst i;dsimp only [b];rw [Function.update_self];rfl
      · have hpi : port sources k D i≠port sources k D 2 := fun he=>hi (port_injective sources k D he)
        dsimp only [b]
        rw [Function.update_of_ne hpi,ap i]
        fin_cases i <;> first | rfl | contradiction
    have bw (i : Fin (workTapes sources k D)) : (b (work sources k D i)).length ≤ C := by
      dsimp only [b]
      rw [Function.update_of_ne (port_away sources k D i 2)]
      exact aw i
    have hreturn:=suffix_run sources k D C s n (2^s) b bw bp
    obtain ⟨tr,htr,hr⟩:=Reusable.exact_time hreplace
    obtain ⟨tf,htf,hf⟩:=Reusable.exact_time hreturn
    have hmid:=hr.call ss pp 0 nn 1 2 (by intro q;rfl)
    have hlast:=hf.stop ss pp 0 nn 2 (by intro q;rfl)
    have hall:=(hfirst.trans hmid).trans hlast
    obtain ⟨r,hrun,hfinal,hsteps⟩:=hall.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have htime : (tp+1+(tr+1))+(tf+1) ≤ budget sources k D copies clock C s n := by
      change tp ≤ prefixBudget sources k D copies clock s n at htp
      unfold budget
      omega
    have hmore:=run_moreFuel (machine sources k D copies clock) _
      (budget sources k D copies clock C s n-((tp+1+(tr+1))+(tf+1))) _ r hrun
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,hmore,?_,?_,hsteps.le.trans htime⟩
    · rw [hfinal]
      simp only [nextBest,hfit,↓reduceIte]
      rfl
    · intro i;rw [hfinal];rfl
  · have hfirst:=hprefix.call ss pp 0 nn 0 2 (by intro q;simp [nn,next,hscan,hfit])
    have hreturn:=suffix_run sources k D C s n best a aw ap
    obtain ⟨tf,htf,hf⟩:=Reusable.exact_time hreturn
    have hlast:=hf.stop ss pp 0 nn 2 (by intro q;rfl)
    have hall:=hfirst.trans hlast
    obtain ⟨r,hrun,hfinal,hsteps⟩:=hall.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have htime : (tp+1)+(tf+1) ≤ budget sources k D copies clock C s n := by
      change tp ≤ prefixBudget sources k D copies clock s n at htp
      unfold budget
      omega
    have hmore:=run_moreFuel (machine sources k D copies clock) _
      (budget sources k D copies clock C s n-((tp+1)+(tf+1))) _ r hrun
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,hmore,?_,?_,hsteps.le.trans htime⟩
    · rw [hfinal]
      simp only [nextBest,hfit,↓reduceIte]
      rfl
    · intro i;rw [hfinal];rfl

end
end NearCubicWires.RepairSource.CloseoutSchedule.Step
