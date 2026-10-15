import Proof.Gates.GateRecovery.Bundle
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleTest
import Proof.Circuits.DecompositionCountDrivers
import Proof.Circuits.MatrixBucketDimensionsIncrement
import Proof.PCP.PCPPairReusable
import Proof.Amplification.RecoveryFocusRetained

namespace GR

/-! Reusable schedule calls preserve exact input fields and paid blank
workspace. The full test's physical time bounds every materialized port. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Reusable
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem exact_time {t states cost : Nat} {p : Machine t states}
    {input output : Fin t→List Bool} (h : ClockJoin.ReadyRun p cost input output) :
    ∃ time, time≤cost ∧ RecoveryRootRound.ReadyRun p time input output := by
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  have he:=ready_of_run p cost input r hr hh
  rw [ht] at he
  exact ⟨r.steps,hs,he⟩

theorem copy (sourceCap C n : Nat) (hC : n+2≤C) :
    ClockJoin.ReadyRun (UWalkUnary.machine false false) (2*n+6)
      ![ZeroPadding.pad sourceCap (UnaryTemplate.tape n),List.replicate C false,List.replicate C false]
      ![ZeroPadding.pad sourceCap (UnaryTemplate.tape n),ZeroPadding.pad C (List.replicate n true),
        List.replicate C false] := by
  have hp:=PCPPairReusable.padded_ready _ _ _
    (DecompositionCountDrivers.template_ready false false n) ![sourceCap,C,C]
  have hi : (fun i : Fin 3=>ZeroPadding.pad (![sourceCap,C,C] i)
      (![UnaryTemplate.tape n,[],[]] i))=
      ![ZeroPadding.pad sourceCap (UnaryTemplate.tape n),List.replicate C false,List.replicate C false] := by
    funext i;fin_cases i <;> simp [ZeroPadding.pad]
  have ho : (fun i : Fin 3=>ZeroPadding.pad (![sourceCap,C,C] i)
      (![UnaryTemplate.tape n,UWalkUnary.output false false n,List.replicate (n+2) false] i))=
      ![ZeroPadding.pad sourceCap (UnaryTemplate.tape n),ZeroPadding.pad C (List.replicate n true),
        List.replicate C false] := by
    funext i;fin_cases i
    · rfl
    · rfl
    · change ZeroPadding.pad C (List.replicate (n+2) false)=List.replicate C false
      rw [Rewind.Workspace.pad_zeros,max_eq_left hC]
  rw [hi,ho] at hp
  exact hp

theorem increment (C s : Nat) : ClockJoin.ReadyRun MatrixBucketDimensions.Increment.machine
    (2*s+5) (fun _=>ZeroPadding.pad C (UnaryTemplate.tape s))
      (fun _=>ZeroPadding.pad C (UnaryTemplate.tape (s+1))) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=MatrixBucketDimensions.Increment.increment_run s
  exact PCPPairReusable.padded_ready _ _ _ ⟨r,hr,ht,hh,hs.le⟩ (fun _=>C)

theorem test (sources : GateEightSources) (k D copies ext : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (s n C : Nat) (hD : 1≤D)
    (hs : s≤C) (hn : n≤C) (hC : Test.budget sources k D copies ext clock s n+1≤C) : ∃ out,
    ClockJoin.ReadyRun (Test.machine sources k D copies ext clock) (Test.budget sources k D copies ext clock s n)
      (fun i=>ZeroPadding.pad C (Test.input sources k D s n i)) out ∧
    out (Test.old sources k D (Candidate.powerSlots sources k D 13))=
      ZeroPadding.pad C (UnaryTemplate.tape (2^s)) ∧
    out (Test.extra sources k D 0)=ZeroPadding.pad C (List.replicate n true) ∧
    out (Test.extra sources k D 3)=ZeroPadding.pad C
      [decide (CloseoutLanguage.widthAt sources k clock copies ext D s≤n/2)] ∧
    (∀ i,(out i).length≤C) := by
  obtain ⟨a,ha,hN,hnative,hflag⟩:=Test.test_run sources k D copies ext clock s n hD
  have hp:=PCPPairReusable.padded_ready _ _ _ ha (fun _=>C)
  obtain ⟨r,hr,ht,hh,hsteps⟩:=hp
  have hinput (i : Fin (Test.tapes sources k D)) : (Test.input sources k D s n i).length≤C := by
    refine Fin.addCases (motive:=fun i=>(Test.input sources k D s n i).length≤C) ?_ ?_ i
    · intro j
      simp only [Test.input,Fin.addCases_left]
      unfold Candidate.input
      split_ifs <;> simp only [List.length_replicate,List.length_nil] <;> omega
    · intro j
      simp only [Test.input,Fin.addCases_right]
      split_ifs <;> simp only [List.length_replicate,List.length_nil] <;> omega
  have hsupport:=RecoveryTapeSupport.run_support (Test.machine sources k D copies ext clock) _ _ r hr C 0
    (by intro i;exact Nat.zero_le _) (by
      intro i
      change (ZeroPadding.pad C (Test.input sources k D s n i)).length ≤ max C (0+1)
      rw [ZeroPadding.pad_length,max_eq_left (hinput i)]
      exact Nat.le_max_left _ _)
  refine ⟨_,⟨r,hr,ht,hh,hsteps⟩,?_,?_,?_,?_⟩
  · exact congrArg (ZeroPadding.pad C) hN
  · exact congrArg (ZeroPadding.pad C) hnative
  · exact congrArg (ZeroPadding.pad C) hflag
  · intro i
    have h:=hsupport i
    rw [ht] at h
    exact h.trans (max_le le_rfl (by omega))

end
end NearCubicWires.RepairSource.CloseoutSchedule.Reusable

end GR
