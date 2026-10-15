import Proof.PCP.PCPPNativeResourceQuery
import Proof.Amplification.RecoveryProjectionDimensionUnary

/-! The retained original native oracle supplies R and size; the original
hierarchy Q frame supplies Q. All three raw counters are physically decoded
and the very same oracle descriptor returns at head zero. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeMetadataPrefix
open LocalBitMultitape SourceInterfaces RecoveryRootRound RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oracleSlots (i : Fin 40) : Fin 47 := i.castAdd 7
def querySlots (i : Fin 7) : Fin 47 := i.natAdd 40
theorem oracle_injective : Function.Injective oracleSlots := by decide
theorem query_injective : Function.Injective querySlots := by decide
def input (bits : List Bool) (Q : ℕ) (i : Fin 47) :=
  if i=0 then bits else if i=40 then frame Q.bits else []
noncomputable def first := RecoveryFocus.machine oracleSlots PCPPNativeOracleCold.machine
noncomputable def second := RecoveryFocus.machine querySlots RecoveryProjectionDimension.machine
noncomputable def machine := Composition.machine first second
def budget (R Q s : ℕ) := PCPPNativeOracleCold.budget R s+1+RecoveryProjectionDimension.budget Q.bits

theorem metadata_run {R : ℕ} (oracle : BooleanCircuit R) (Q : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget R Q oracle.size) (input (PCPPNative.descriptor oracle) Q) out ∧
    out 0=PCPPNative.descriptor oracle ∧ out 32=List.replicate oracle.size true ∧
    out 36=List.replicate R true ∧ out 45=List.replicate Q true ∧
    out 43=VerifierDecoding.CompareMachine.word Q := by
  obtain ⟨oraw,ho,hbits,hs,hR,_,_⟩ := PCPPNativeOracleCold.oracle_run oracle
  have ha := ho.focus oracleSlots oracle_injective (input (PCPPNative.descriptor oracle) Q) (by
    intro i
    by_cases hi : i=0
    · subst i; rfl
    · have h0 : oracleSlots i≠0 := by intro he; apply hi; apply Fin.ext; exact congrArg (fun j : Fin 47 => j.val) he
      have h40 : oracleSlots i≠40 := by
        intro he; have hv := congrArg (fun j : Fin 47 => j.val) he
        change i.val=40 at hv
        omega
      simp [input,PCPPNativeOracleCold.input,hi,h0,h40])
  let a := install oracleSlots (input (PCPPNative.descriptor oracle) Q) oraw
  have fresh (i : Fin 7) : a (querySlots i)=RecoveryProjectionDimension.input Q.bits i := by
    dsimp only [a]
    rw [install_other _ _ _ _ (by
      intro j he
      have hv := congrArg (fun j : Fin 47 => j.val) he
      change j.val=40+i.val at hv
      omega)]
    fin_cases i <;> rfl
  obtain ⟨qraw,hq,hcount,hraw⟩ := RecoveryProjectionDimension.unary_ready Q.bits
  rw [RecoveryUnpair.bits_value] at hcount hraw
  have hb := hq.focus querySlots query_injective a fresh
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ ha hb,?_,?_,?_,?_,?_⟩
  · exact (install_other _ _ _ _ (by decide)).trans
      ((install_slot _ oracle_injective _ _ 0).trans hbits)
  · exact (install_other _ _ _ _ (by decide)).trans
      ((install_slot _ oracle_injective _ _ 32).trans hs)
  · exact (install_other _ _ _ _ (by decide)).trans
      ((install_slot _ oracle_injective _ _ 36).trans hR)
  · exact (install_slot _ query_injective _ _ 5).trans hraw
  · exact (install_slot _ query_injective _ _ 3).trans hcount

end NearCubicWires.RepairOrdinary.PCPPNativeMetadataPrefix
