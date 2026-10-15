import Proof.Hierarchy.CompetitorCrossCapacity
import Proof.PCP.ProjectionNormalizationDriverAtoms

/-! Native table scalars from four raw inputs. Capacity, cell-count and
packet-count sentinels, and native byte count are produced by actual runs. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossScalarDrivers
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w b n p : ℕ) : Fin 32 → List Bool := fun i =>
  if i.val=0 then List.replicate w true else if i.val=1 then List.replicate b true
  else if i.val=2 then List.replicate n true else if i.val=3 then List.replicate p true else []
def powerSlots (i : Fin 18) : Fin 32 :=
  if i.val=0 then 0 else if i.val=7 then 4 else ⟨i.val+4,by omega⟩
def nSlots : Fin 4 → Fin 32 := ![2,22,23,24]
def pSlots : Fin 4 → Fin 32 := ![3,25,26,27]
def bSlots : Fin 3 → Fin 32 := ![1,28,29]
def productSlots : Fin 4 → Fin 32 := ![2,28,30,31]
noncomputable def power := RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 2 4096)
noncomputable def nCounter := RecoveryFocus.machine nSlots Counter.machine
noncomputable def pCounter := RecoveryFocus.machine pSlots Counter.machine
noncomputable def bTemplate := RecoveryFocus.machine bSlots (DimensionTemplate.machine false)
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def machine := Composition.machine power (Composition.machine nCounter
  (Composition.machine pCounter (Composition.machine bTemplate product)))
def budget (w b n p : ℕ) := PCPSerializerCapacity.Power.budget 2 4096 w+1+
  (Counter.budget n+1+(Counter.budget p+1+((2*b+8)+1+WilliamsUnaryProduct.budget n b)))

theorem power_injective : Function.Injective powerSlots := by decide
theorem power_value (i : Fin 18) : (powerSlots i).val=
    if i.val=0 then 0 else if i.val=7 then 4 else i.val+4 := by
  unfold powerSlots
  split_ifs <;> rfl

theorem drivers_run (w b n p : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget w b n p) (input w b n p) out ∧
      (∀ i : Fin 4,out (i.castAdd 28)=input w b n p (i.castAdd 28)) ∧
      out 4=List.replicate (CompetitorPlane.capacity w) true ∧
      out 23=CompareMachine.word n ∧ out 26=CompareMachine.word p ∧
      out 30=List.replicate (n*b) true := by
  obtain ⟨a,ha,ha0,ha7⟩ := PCPSerializerCapacity.Power.capacity_run 2 4096 w
  have hpower := bounded_focus powerSlots power_injective _ _ _ ha (input w b n p) (by
    intro i
    by_cases h0 : i.val=0
    · simp [powerSlots,h0,input,DimensionPolynomial.input]
    by_cases h7 : i.val=7
    · simp [powerSlots,h7,input,DimensionPolynomial.input]
    · simp [powerSlots,h0,h7,input,DimensionPolynomial.input])
  let atapes := install powerSlots (input w b n p) a
  have first_keep (i : Fin 32) (hi : (0 < i.val ∧ i.val < 4) ∨ 22 ≤ i.val) :
      atapes i=input w b n p i := by
    apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    rw [power_value] at hv
    split_ifs at hv <;> omega
  obtain ⟨nout,hn,hn0,hn2⟩ := DriverAtoms.counter_run n
  have hnCounter := bounded_focus nSlots (by decide) _ _ _ hn atapes (by
    intro i
    fin_cases i
    · exact first_keep 2 (Or.inl (by decide))
    all_goals exact first_keep _ (Or.inr (by decide)))
  let btapes := install nSlots atapes nout
  obtain ⟨pout,hp,hp0,hp2⟩ := DriverAtoms.counter_run p
  have hpCounter := bounded_focus pSlots (by decide) _ _ _ hp btapes (by
    intro i
    fin_cases i
    · exact (install_other nSlots _ _ _ (by decide)).trans (first_keep 3 (Or.inl (by decide)))
    all_goals exact (install_other nSlots _ _ _ (by decide)).trans (first_keep _ (Or.inr (by decide))))
  let ctapes := install pSlots btapes pout
  have hbTemplate := bounded_focus bSlots (by decide) _ _ _ (DimensionTemplate.ready false b) ctapes (by
    intro i
    fin_cases i
    · exact (install_other pSlots _ _ _ (by decide)).trans
        ((install_other nSlots _ _ _ (by decide)).trans (first_keep 1 (Or.inl (by decide))))
    · exact (install_other pSlots _ _ _ (by decide)).trans
        ((install_other nSlots _ _ _ (by decide)).trans (first_keep 28 (Or.inr (by decide))))
    · exact (install_other pSlots _ _ _ (by decide)).trans
        ((install_other nSlots _ _ _ (by decide)).trans (first_keep 29 (Or.inr (by decide)))))
  let dtapes := install bSlots ctapes (DimensionTemplate.output false b)
  have hproduct := bounded_focus productSlots (by decide) _ _ _ (CompetitorDimensions.unary_ready n b) dtapes (by
    intro i
    fin_cases i
    · exact (install_other bSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans ((install_slot nSlots (by decide) _ _ 0).trans hn0))
    · exact install_slot bSlots (by decide) _ _ 1
    · exact (install_other bSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans
          ((install_other nSlots _ _ _ (by decide)).trans (first_keep 30 (Or.inr (by decide)))))
    · exact (install_other bSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans
          ((install_other nSlots _ _ _ (by decide)).trans (first_keep 31 (Or.inr (by decide))))))
  let out := install productSlots dtapes (WilliamsUnaryProduct.output n b)
  have hlast := ClockJoin.join _ _ _ _ _ _ _ hbTemplate hproduct
  have htail := ClockJoin.join _ _ _ _ _ _ _ hpCounter hlast
  have hrest := ClockJoin.join _ _ _ _ _ _ _ hnCounter htail
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hpower hrest,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact (install_other productSlots _ _ _ (by decide)).trans
        ((install_other bSlots _ _ _ (by decide)).trans
          ((install_other pSlots _ _ _ (by decide)).trans
            ((install_other nSlots _ _ _ (by decide)).trans ((install_slot powerSlots power_injective _ a 0).trans ha0))))
    · exact (install_other productSlots _ _ _ (by decide)).trans (install_slot bSlots (by decide) _ _ 0)
    · exact install_slot productSlots (by decide) _ _ 0
    · exact (install_other productSlots _ _ _ (by decide)).trans
        ((install_other bSlots _ _ _ (by decide)).trans ((install_slot pSlots (by decide) _ _ 0).trans hp0))
  · exact (install_other productSlots _ _ _ (by decide)).trans
      ((install_other bSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans
          ((install_other nSlots _ _ _ (by decide)).trans ((install_slot powerSlots power_injective _ a 7).trans ha7))))
  · exact (install_other productSlots _ _ _ (by decide)).trans
      ((install_other bSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans ((install_slot nSlots (by decide) _ _ 2).trans hn2)))
  · exact (install_other productSlots _ _ _ (by decide)).trans
      ((install_other bSlots _ _ _ (by decide)).trans ((install_slot pSlots (by decide) _ _ 2).trans hp2))
  · exact install_slot productSlots (by decide) _ _ 2

end NearCubicWires.RepairOrdinary.CompetitorCrossScalarDrivers
