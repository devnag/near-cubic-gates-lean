import Proof.CaseAnalysis.RecoveryProjectionLayout

/-! Dock the existing cold scalar producer at the original projector cells.
All other bank cells and all subsequent worker logs begin physically empty. -/
namespace NearCubicWires.RepairOrdinary.RecoveryProjectionCold
open LocalBitMultitape RepairSource RecoveryRootRound SourceInterfaces
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def scalarMachine :=
  RecoveryFocus.machine scalarSlots RecoveryPCPFormulaResumeColdScalars.machine
def scalarBudget (R Q : ℕ) := RecoveryPCPFormulaResumeColdScalars.budget R.bits Q.bits

theorem scalar_input (R Q B : ℕ) (queries : List Bool) (i : Fin 66) :
    input R Q B queries (scalarSlots i)=RecoveryPCPFormulaResumeColdScalars.input R.bits Q.bits i := by
  fin_cases i <;> rfl

theorem scalar_ready (R Q B : ℕ) (queries : List Bool) : ∃ A,
    ClockJoin.ReadyRun scalarMachine (scalarBudget R Q) (input R Q B queries) A ∧
      (∀ i,A (bankSlots i)=beforeBank R Q queries i) ∧
      A 103=List.replicate (2^R) true ∧
      (∀ i : Fin 113,(104 : ℕ)≤(i : Fin 113).val→A i=if i=104 then List.replicate B true else []) := by
  obtain ⟨out,hr,h3,h17,h31,_h37,_h58,h61,h64⟩ :=
    RecoveryPCPFormulaResumeColdScalars.scalars_ready R.bits Q.bits
  simp only [DimensionProducer.bits_value] at h3 h17 h31 h61 h64
  let A:=install scalarSlots (input R Q B queries) out
  have h:=hr.focus scalarSlots scalar_injective (input R Q B queries) (scalar_input R Q B queries)
  refine ⟨A,h,?_,?_,?_⟩
  · intro i
    fin_cases i
    all_goals first
      | exact (install_slot scalarSlots scalar_injective _ out 3).trans h3
      | exact (install_slot scalarSlots scalar_injective _ out 17).trans h17
      | exact (install_slot scalarSlots scalar_injective _ out 31).trans h31
      | exact (install_slot scalarSlots scalar_injective _ out 64).trans h64
      | exact (install_other scalarSlots _ out _ (by decide)).trans (by rfl)
  · exact (install_slot scalarSlots scalar_injective _ out 61).trans h61
  · intro i hi
    dsimp only [A]
    rw [install_other _ _ _ _ (scalar_outside_high i hi)]
    have h37 : i≠37 := by intro h;subst i;norm_num at hi
    have h65 : i≠65 := by intro h;subst i;norm_num at hi
    have h28 : i≠28 := by intro h;subst i;norm_num at hi
    simp only [input,h37,h65,h28,ite_false]

end NearCubicWires.RepairOrdinary.RecoveryProjectionCold
