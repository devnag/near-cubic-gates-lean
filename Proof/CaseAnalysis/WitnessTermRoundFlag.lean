import Proof.CaseAnalysis.WitnessTermRound

/-! The same circuit verdict is folded into the retained coefficient
verdict in one physical step. Arbitrary false allocation after that cell
is retained, so no singleton copy or flag normalization is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagOutput (left right : List Bool) :=
  writeTapeBit right 0 (readTapeBit right 0 && readTapeBit left 0)
def flagged (input : Fin 2532 → List Bool) :=
  Function.update input 719 (flagOutput (input 2527) (input 719))

private theorem flag_ready (left right : List Bool) :
    ReadyRun CloseoutRowsIntegerRound.flagMachine 1 ![left,right] ![left,flagOutput left right] := by
  let last : Configuration 2 2 := ⟨1,fun _=>0,![left,flagOutput left right]⟩
  have hs : step CloseoutRowsIntegerRound.flagMachine
      (initialConfiguration CloseoutRowsIntegerRound.flagMachine ![left,right])=some last := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rf,rs⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs⟩

theorem flag_run (heads : Fin 2532 → ℕ) (input : Fin 2532 → List Bool)
    (hh : heads 2527=0 ∧ heads 719=0) :
    ∃ r,runFrom foldFlag 1 ⟨foldFlag.start,heads,input⟩=some r ∧
      r.steps=1 ∧ r.final.heads=heads ∧ r.final.tapes=flagged input := by
  obtain ⟨r,hr,rh,rt,rs⟩ := (flag_ready (input 2527) (input 719)).focus_at
    flagSlots (by decide) heads input (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i
        · exact hh.1
        · exact hh.2)
  refine ⟨r,hr,rs,rh,?_⟩
  rw [rt]
  funext i
  by_cases h719 : i=719
  · subst i
    rw [flagged,Function.update_self]
    exact install_slot flagSlots (by decide) input _ 1
  rw [flagged,Function.update_of_ne h719]
  by_cases h2527 : i=2527
  · subst i;exact install_slot flagSlots (by decide) input _ 0
  · exact install_other _ _ _ _ (by
      intro j
      fin_cases j
      · exact Ne.symm h2527
      · exact Ne.symm h719)

theorem flag_value (input : Fin 2532 → List Bool) :
    readTapeBit (flagged input 719) 0=(readTapeBit (input 719) 0 && readTapeBit (input 2527) 0) := by
  rw [flagged,Function.update_self]
  cases input 719 <;> rfl

theorem flag_accepted (input : Fin 2532 → List Bool)
    (hr : readTapeBit (input 719) 0=true) (hl : readTapeBit (input 2527) 0=true) :
    flagged input=input := by
  have he : flagOutput (input 2527) (input 719)=input 719 := by
    unfold flagOutput
    rw [hr,hl]
    cases ht : input 719 with
    | nil => rw [ht] at hr;change false=true at hr;cases hr
    | cons bit tail =>
      have hb : bit=true := by rw [ht] at hr;exact hr
      rw [hb];rfl
  unfold flagged
  rw [he]
  exact Function.update_eq_self _ _

theorem flag_bound (P : ℕ) (left right : List Bool) (hP : 1 ≤ P) (hr : right.length ≤ P) :
    (flagOutput left right).length ≤ P := by
  rw [flagOutput,RecoveryTapeSupport.write_length]
  exact Nat.max_le.mpr ⟨hr,hP⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
