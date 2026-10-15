import Proof.Amplification.RecoveryAssignmentRewind

/-! Physical counter erasure before every reused assignment scan. Other
tapes are retained; the dedicated unary driver and reset storage are reused. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 3→Fin 16 := ![8,15,14]
theorem eraseSlots_injective : Function.Injective eraseSlots := by decide
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)

private theorem vector_three (a b c : List Bool) :
    (fun i : Fin 3=>Fin.addCases (fun j : Fin 2=>Fin.addCases (fun _ : Fin 1=>a) (fun _ : Fin 1=>b) j)
      (fun _ : Fin 1=>c) i)=![a,b,c] := by
  funext i; fin_cases i <;> rfl

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem erase_counter_ready (tapes : Fin 16→List Bool) (total resetCapacity : Nat)
    (hb : (tapes 8).length≤total) (hd : tapes 15=List.replicate total true)
    (hr : tapes 14=List.replicate resetCapacity false) (hc : total+1≤resetCapacity) :
    ReadyRun eraseMachine (2*total+4) tapes (Function.update tapes 8 (List.replicate total false)) := by
  obtain ⟨base,hbase,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready total resetCapacity
    (fun _ : Fin 1=>tapes 8) (by intro i; exact hb)
  rw [vector_three] at hbase ht
  rw [Nat.max_eq_left hc] at ht
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config eraseSlots eraseSlots_injective
    (RecoveryScratchErase.resetMachine 1) (fun _ : Fin 16=>0) tapes _ _ base hbase
  have hin : RecoveryFocus.config eraseSlots (fun _ : Fin 16=>0) tapes
      (initialConfiguration (RecoveryScratchErase.resetMachine 1)
        ![tapes 8,List.replicate total true,List.replicate resetCapacity false])=
      initialConfiguration eraseMachine tapes := by
    apply focus_configuration eraseSlots eraseSlots_injective
    · rfl
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> simp [initialConfiguration,eraseSlots,hd,hr]
    · intro i _; rfl
    · intro i _; rfl
  rw [hin] at hrun
  have he : base.final=(⟨base.final.control,fun _=>0,
      ![List.replicate total false,List.replicate total true,List.replicate resetCapacity false]⟩ : Configuration 3 4) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [he] at hfinal
  have hout : RecoveryFocus.config eraseSlots (fun _ : Fin 16=>0) tapes
      (⟨base.final.control,fun _=>0,
        ![List.replicate total false,List.replicate total true,List.replicate resetCapacity false]⟩ : Configuration 3 4)=
      (⟨base.final.control,fun _=>0,Function.update tapes 8 (List.replicate total false)⟩ : Configuration 16 4) := by
    apply focus_configuration eraseSlots eraseSlots_injective
    · rfl
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> simp [eraseSlots,hd,hr]
    · intro i _; rfl
    · intro i hi
      exact (Function.update_of_ne (Ne.symm (hi 0)) _ _).symm
  rw [hout] at hfinal
  exact ⟨r,hrun,by rw [hfinal],by intro i; rw [hfinal],hsteps.trans hs⟩

end NearCubicWires.RepairOrdinary.RecoveryAssignment
