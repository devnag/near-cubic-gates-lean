import Proof.CaseAnalysis.ScheduleCandidate
import Proof.CaseAnalysis.ScheduleCompare

/-! One actual schedule test retains the candidate source-length template
and computes the exact Boolean condition used by the canonical language. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Test
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (sources : EightSources) (k D : Nat) := Candidate.tapes sources k D+5
def old (sources : EightSources) (k D : Nat) (i : Fin (Candidate.tapes sources k D)) :
    Fin (tapes sources k D) := i.castAdd 5
def extra (sources : EightSources) (k D : Nat) (i : Fin 5) : Fin (tapes sources k D) :=
  i.natAdd (Candidate.tapes sources k D)
def width (sources : EightSources) (k D : Nat) :=
  Candidate.widthSlots sources k D (Width.outputSlot D)
def compareSlots (sources : EightSources) (k D : Nat) : Fin 6→Fin (tapes sources k D) :=
  ![old sources k D (width sources k D),extra sources k D 0,extra sources k D 1,
    extra sources k D 2,extra sources k D 3,extra sources k D 4]
theorem old_injective (sources : EightSources) (k D : Nat) : Function.Injective (old sources k D) := by
  intro a b h;exact Fin.ext (congrArg (fun i : Fin (tapes sources k D)=>i.val) h)
theorem compare_injective (sources : EightSources) (k D : Nat) : Function.Injective (compareSlots sources k D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  have hw:=(width sources k D).isLt
  fin_cases a <;> fin_cases b <;> simp [compareSlots,old,extra] at hv ⊢ <;> omega
def input (sources : EightSources) (k D s n : Nat) : Fin (tapes sources k D)→List Bool :=
  Fin.addCases (Candidate.input sources k D s) (fun i : Fin 5=>if i.val=0 then List.replicate n true else [])
def candidate (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :=
  RecoveryFocus.machine (old sources k D) (Candidate.machine sources k D copies clock)
def compare (sources : EightSources) (k D : Nat) :=
  RecoveryFocus.machine (compareSlots sources k D) RawCompare.machine
def machine (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :=
  Composition.machine (candidate sources k D copies clock) (compare sources k D)
def budget (sources : EightSources) (k D copies : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (s n : Nat) :=
  Candidate.budget sources k D copies clock s+1+
    RawCompare.budget (2*CloseoutLanguage.widthAt sources k clock copies D s) n

theorem width_ge (sources : EightSources) (k D : Nat) : 17≤(width sources k D).val := by
  have hr:=Candidate.native_range sources k D (nativeRaw sources k)
  unfold width Candidate.widthSlots
  split_ifs
  · exact hr.1
  · change 17≤18+Candidate.nativeTapes sources k+(Width.outputSlot D).val
    omega

theorem test_run (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (s n : Nat) (hD : 1≤D) : ∃ out,
    ClockJoin.ReadyRun (machine sources k D copies clock) (budget sources k D copies clock s n)
      (input sources k D s n) out ∧
    out (old sources k D (Candidate.powerSlots sources k D 13))=UnaryTemplate.tape (2^s) ∧
    out (extra sources k D 0)=List.replicate n true ∧
    out (extra sources k D 3)=[decide (CloseoutLanguage.widthAt sources k clock copies D s≤n/2)] := by
  obtain ⟨a,ha,hN,hm⟩:=Candidate.candidate_run sources k D copies clock s hD
  have hac:=ha.focus (old sources k D) (old_injective sources k D) (input sources k D s n)
    (by intro i;exact Fin.addCases_left i)
  let b:=install (old sources k D) (input sources k D s n) a
  have hb (i : Fin 5) : b (extra sources k D i)=if i.val=0 then List.replicate n true else [] := by
    dsimp only [b]
    rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
      change j.val=Candidate.tapes sources k D+i.val at hv;omega)]
    exact Fin.addCases_right i
  have hcmp:=(RawCompare.compare_run (2*CloseoutLanguage.widthAt sources k clock copies D s) n).focus
    (compareSlots sources k D) (compare_injective sources k D) b (by
      intro i;fin_cases i
      · exact (install_slot _ (old_injective sources k D) _ a (width sources k D)).trans hm
      · exact hb 0
      · exact hb 1
      · exact hb 2
      · exact hb 3
      · exact hb 4)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hac hcmp,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have hw:=width_ge sources k D
      fin_cases j <;> simp [compareSlots,old,extra,Candidate.powerSlots] at hv <;> omega)]
    exact (install_slot _ (old_injective sources k D) _ _ _).trans hN
  · exact install_slot _ (compare_injective sources k D) _ _ 1
  · have he : (2*CloseoutLanguage.widthAt sources k clock copies D s≤n) =
        (CloseoutLanguage.widthAt sources k clock copies D s≤n/2) := by apply propext;omega
    change install (compareSlots sources k D) b _ (compareSlots sources k D 4)=_
    rw [install_slot _ (compare_injective sources k D)]
    change [decide (2*CloseoutLanguage.widthAt sources k clock copies D s≤n)]=_
    simp only [he]

end
end NearCubicWires.RepairSource.CloseoutSchedule.Test
