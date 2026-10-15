import Proof.PCP.PCPPNativeOracleOutputCold

namespace NearCubicWires.RepairOrdinary.PCPPNativeOracleScalars
open LocalBitMultitape SourceInterfaces RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldSlots (i : Fin 22) : Fin 27 := i.castAdd 5
def negativeSlots : Fin 4 → Fin 27 := ![19,20,22,23]
def positiveSlots : Fin 4 → Fin 27 := ![24,14,25,26]
theorem cold_injective : Function.Injective coldSlots := by decide
theorem negative_injective : Function.Injective negativeSlots := by decide
theorem positive_injective : Function.Injective positiveSlots := by decide
def input (bits : List Bool) (s : ℕ) (i : Fin 27) := if i=0 then bits else if i=18 then List.replicate s true else []
noncomputable def first := RecoveryFocus.machine coldSlots PCPPNativeOracleOutputCold.machine
noncomputable def second := RecoveryFocus.machine negativeSlots ClockUnarySum.machine
noncomputable def third := RecoveryFocus.machine positiveSlots PCPPNativeAddress.machine
noncomputable def machine := Composition.machine (Composition.machine first second) third
def budget {R : ℕ} (oracle : BooleanCircuit R) := PCPPNativeOracleOutputCold.budget oracle+1+
  (2*(oracle.size+oracle.size)+6)+1+(2*0+4*oracle.output.val+6)

theorem scalar_run {R : ℕ} (oracle : BooleanCircuit R) : ∃ out,
    ClockJoin.ReadyRun machine (budget oracle) (input (PCPPNative.descriptor oracle) oracle.size) out ∧
    out 0=PCPPNative.descriptor oracle ∧ out 22=List.replicate (2*oracle.size) true ∧
    out 25=List.replicate (2*oracle.output.val+1) true := by
  obtain ⟨cold,hcold,c0,c14,_,c19,c20⟩ := PCPPNativeOracleOutputCold.cold_run oracle
  have ha := hcold.focus coldSlots cold_injective (input (PCPPNative.descriptor oracle) oracle.size)
    (by intro i; fin_cases i <;> rfl)
  let a := install coldSlots (input (PCPPNative.descriptor oracle) oracle.size) cold
  have low (i : Fin 22) : a (coldSlots i)=cold i := install_slot _ cold_injective _ _ _
  have high (i : Fin 27) (hi : 22 ≤ i.val) : a i=[] := by
    dsimp only [a]
    rw [install_other _ _ _ _ (by
      intro j he
      have hv := congrArg (fun i : Fin 27 => i.val) he
      change j.val=i.val at hv
      omega)]
    have h0 : i≠0 := by intro he; subst i; contradiction
    have h18 : i≠18 := by intro he; subst i; contradiction
    simp only [input,h0,h18,ite_false]
  have hb := (ClockUnarySum.sum_ready oracle.size oracle.size).focus negativeSlots negative_injective a (by
    intro i; fin_cases i
    · exact (low 19).trans c19
    · exact (low 20).trans c20
    · exact high 22 (by decide)
    · exact high 23 (by decide))
  let b := install negativeSlots a ![List.replicate oracle.size true,List.replicate oracle.size true,
    List.replicate (oracle.size+oracle.size) true,List.replicate (oracle.size+oracle.size+2) false]
  have hc := (PCPPNativeAddress.address_ready 0 oracle.output.val).focus positiveSlots positive_injective b (by
    intro i; fin_cases i
    · exact (install_other _ _ _ _ (by decide)).trans (high 24 (by decide))
    · exact (install_other _ _ _ _ (by decide)).trans ((low 14).trans c14)
    · exact (install_other _ _ _ _ (by decide)).trans (high 25 (by decide))
    · exact (install_other _ _ _ _ (by decide)).trans (high 26 (by decide)))
  have h := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ ha hb) hc
  refine ⟨_,h,?_,?_,?_⟩
  · exact (install_other _ _ _ _ (by decide)).trans ((install_other _ _ _ _ (by decide)).trans ((low 0).trans c0))
  · have h2 := install_slot negativeSlots negative_injective a
      ![List.replicate oracle.size true,List.replicate oracle.size true,
        List.replicate (oracle.size+oracle.size) true,List.replicate (oracle.size+oracle.size+2) false] 2
    rw [install_other positiveSlots b _ (22 : Fin 27) (by decide)]
    simpa [b,negativeSlots,two_mul] using h2
  · change install positiveSlots b _ (positiveSlots 2)=_
    rw [install_slot _ positive_injective]
    simp [PCPPSubstitution.address]

end NearCubicWires.RepairOrdinary.PCPPNativeOracleScalars
