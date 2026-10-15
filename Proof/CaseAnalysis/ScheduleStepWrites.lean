import Proof.CaseAnalysis.ScheduleStepLayout

/-! Focused physical copies and one-field erase are literal updates of the
retained schedule bank. Update notation only describes their proved output. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Reusable
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem copy_into {t : Nat} (slots : Fin 3→Fin t) (inj : Function.Injective slots)
    (sourceCap C n : Nat) (hC : n+2≤C) (ambient : Fin t→List Bool)
    (hsource : ambient (slots 0)=ZeroPadding.pad sourceCap (UnaryTemplate.tape n))
    (htarget : ambient (slots 1)=List.replicate C false)
    (hlog : ambient (slots 2)=List.replicate C false) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slots (UWalkUnary.machine false false)) (2*n+6) ambient
      (Function.update ambient (slots 1) (ZeroPadding.pad C (List.replicate n true))) := by
  have h:=(copy sourceCap C n hC).focus slots inj ambient (by
    intro i;fin_cases i
    · exact hsource
    · exact htarget
    · exact hlog)
  have h01 : slots 0≠slots 1 := fun he=>(by decide : (0 : Fin 3)≠1) (inj he)
  have h21 : slots 2≠slots 1 := fun he=>(by decide : (2 : Fin 3)≠1) (inj he)
  have he : install slots ambient
      ![ZeroPadding.pad sourceCap (UnaryTemplate.tape n),ZeroPadding.pad C (List.replicate n true),List.replicate C false]=
      Function.update ambient (slots 1) (ZeroPadding.pad C (List.replicate n true)) := by
    apply HierarchyWidth.install_eq _ inj
    · intro i;fin_cases i
      · change Function.update ambient (slots 1) _ (slots 0)=_
        rw [Function.update_of_ne h01]
        exact hsource
      · simp
      · change Function.update ambient (slots 1) _ (slots 2)=_
        rw [Function.update_of_ne h21]
        exact hlog
    · intro i hi
      exact Function.update_of_ne (Ne.symm (hi 1)) _ _
  rw [he] at h
  exact h

theorem erase_one {t : Nat} (slots : Fin 3→Fin t) (inj : Function.Injective slots)
    (C : Nat) (ambient : Fin t→List Bool) (hlen : (ambient (slots 0)).length≤C)
    (hdriver : ambient (slots 1)=List.replicate C true)
    (hlog : ambient (slots 2)=List.replicate (C+1) false) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1)) (2*C+4) ambient
      (Function.update ambient (slots 0) (List.replicate C false)) := by
  have h:=(RecoveryScratchErase.erase_ready C (C+1) (fun _ : Fin 1=>ambient (slots 0))
    (by intro i;exact hlen)).focus slots inj ambient (by
      intro i;fin_cases i
      · rfl
      · exact hdriver
      · exact hlog)
  have h10 : slots 1≠slots 0 := fun he=>(by decide : (1 : Fin 3)≠0) (inj he)
  have h20 : slots 2≠slots 0 := fun he=>(by decide : (2 : Fin 3)≠0) (inj he)
  have hout : (Fin.addCases (m:=2) (n:=1)
      (Fin.addCases (m:=1) (n:=1) (fun _ : Fin 1=>List.replicate C false) (fun _ : Fin 1=>List.replicate C true))
      (fun _ : Fin 1=>List.replicate (max (C+1) (C+1)) false))=
      ![List.replicate C false,List.replicate C true,List.replicate (C+1) false] := by
    funext i;fin_cases i <;> simp only [Nat.max_self] <;> rfl
  rw [hout] at h
  have he : install slots ambient ![List.replicate C false,List.replicate C true,List.replicate (C+1) false]=
      Function.update ambient (slots 0) (List.replicate C false) := by
    apply HierarchyWidth.install_eq _ inj
    · intro i;fin_cases i
      · simp
      · change Function.update ambient (slots 0) _ (slots 1)=_
        rw [Function.update_of_ne h10]
        exact hdriver
      · change Function.update ambient (slots 0) _ (slots 2)=_
        rw [Function.update_of_ne h20]
        exact hlog
    · intro i hi
      exact Function.update_of_ne (Ne.symm (hi 0)) _ _
  rw [he] at h
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  exact ⟨r,hr,ht,hh,hs.le⟩

end
end NearCubicWires.RepairSource.CloseoutSchedule.Reusable
