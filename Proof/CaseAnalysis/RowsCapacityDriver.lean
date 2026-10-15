import Proof.CaseAnalysis.RowsPreparationFits
import Proof.Amplification.RecoveryPCPFormulaResumeCountCold
import Proof.PCP.ProjectionDimensionPowerBounds

/-! Execute the retained true capacity driver from two short native
dimensions: a fixed fourth power and the existing binary-to-unary power
counter, followed by one paid multiplication. No exponential driver is input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCapacityDriver
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def powerSlots (i : Fin 11) : Fin 22 := i.castAdd 11
def countSlots (i : Fin 7) : Fin 22 := ⟨11+i.val,by have hi:=i.isLt; omega⟩
def successorSlots : Fin 3→Fin 22 := ![15,18,19]
def productSlots : Fin 4→Fin 22 := ![9,18,20,21]
theorem power_injective : Function.Injective powerSlots := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 22=>k.val) h)
theorem count_injective : Function.Injective countSlots := by
  intro i j h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp [countSlots] at hv
  omega
def input (S R : ℕ) : Fin 22→List Bool :=
  fun i=>if i=0 then UnaryTemplate.tape S else if i=11 then CompareMachine.word R else []
noncomputable def power := RecoveryFocus.machine powerSlots (DimensionPower.machine 4 4096)
noncomputable def count := RecoveryFocus.machine countSlots RecoveryPCPFormulaResumeCountCold.readyMachine
noncomputable def successor := RecoveryFocus.machine successorSlots (UWalkUnary.machine true true)
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def first := Composition.machine power count
noncomputable def second := Composition.machine first successor
noncomputable def machine := Composition.machine second product
def budget (S R : ℕ) := DimensionPower.cost 4096 S 4+1+
  RecoveryPCPFormulaResumeCountCold.budget R+1+(2*(2^R-1)+6)+1+
  WilliamsUnaryProduct.budget (4096*S^4) (2^R)

theorem power_outside (i : Fin 22) (hi : 11 ≤ i.val) : ∀ j,powerSlots j≠i := by
  intro j h
  have hv:=congrArg Fin.val h
  have hj:=j.isLt
  change j.val=i.val at hv
  omega
theorem count_outside (i : Fin 22) (hi : i.val<11 ∨ 18 ≤ i.val) : ∀ j,countSlots j≠i := by
  intro j h
  have hv:=congrArg Fin.val h
  have hj:=j.isLt
  change 11+j.val=i.val at hv
  omega

theorem driver_run (S R : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget S R) (input S R) out ∧
      out 20=List.replicate (4096*S^4*2^R) true ∧
      out 0=UnaryTemplate.tape S ∧ out 11=CompareMachine.word R := by
  obtain ⟨powers,hpowers,p0,p9⟩ := DimensionPower.power_run 4 4096 S
  have hpower := hpowers.focus powerSlots power_injective (input S R) (by
    intro i
    fin_cases i <;> rfl)
  let a := install powerSlots (input S R) powers
  obtain ⟨counts,hcounts,c0,c4⟩ := RecoveryPCPFormulaResumeCountCold.count_ready R
  have hcount := hcounts.focus countSlots count_injective a (by
    intro i
    rw [show a (countSlots i)=install powerSlots (input S R) powers (countSlots i) from rfl,
      install_other _ _ _ _ (power_outside _ (by dsimp [countSlots]; omega))]
    fin_cases i <;> rfl)
  let b := install countSlots a counts
  have b15 : b 15=CompareMachine.word (2^R-1) :=
    (install_slot countSlots count_injective a counts 4).trans c4
  have b9 : b 9=List.replicate (4096*S^4) true := by
    rw [show b 9=a 9 from install_other countSlots a counts 9 (count_outside 9 (by decide))]
    exact (install_slot powerSlots power_injective (input S R) powers 9).trans p9
  have bfresh (i : Fin 22) (hi : 18 ≤ i.val) : b i=[] := by
    rw [show b i=a i from install_other countSlots a counts i (count_outside i (Or.inr hi))]
    rw [show a i=input S R i from install_other powerSlots (input S R) powers i (power_outside i (by omega))]
    simp only [input,show i≠0 by intro h; subst i; contradiction,show i≠11 by intro h; subst i; contradiction,
      ↓reduceIte]
  have hsucc := (UWalkUnary.ready true true 0 (2^R-1)).focus successorSlots (by decide) b (by
    intro i
    fin_cases i
    · change b 15=ZeroPadding.pad 0 (CompareMachine.word (2^R-1))
      simpa only [ZeroPadding.pad_zero] using b15
    · exact bfresh 18 (by decide)
    · exact bfresh 19 (by decide))
  let c := install successorSlots b (UWalkUnary.result true true 0 (2^R-1))
  have c18 : c 18=CompareMachine.word (2^R) := by
    rw [show c 18=(UWalkUnary.result true true 0 (2^R-1)) 1 from install_slot successorSlots (by decide) b _ 1]
    have he : 2^R-1+1=2^R := by have h:=Nat.two_pow_pos R; omega
    simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word,he]
  have hprod := (RowTupleDerivedEnumeration.product_ready (4096*S^4) (2^R)).focus
    productSlots (by decide) c (by
      intro i
      fin_cases i
      · exact (install_other successorSlots b _ 9 (by decide)).trans b9
      · exact c18
      · exact (install_other successorSlots b _ 20 (by decide)).trans (bfresh 20 (by decide))
      · exact (install_other successorSlots b _ 21 (by decide)).trans (bfresh 21 (by decide)))
  let out := install productSlots c (RowTupleDerivedEnumeration.productOutput (4096*S^4) (2^R))
  have whole := ClockJoin.join second product _ _ _ _ _
    (ClockJoin.join first successor _ _ _ _ _ (ClockJoin.join power count _ _ _ _ _ hpower hcount) hsucc) hprod
  refine ⟨out,whole,install_slot productSlots (by decide) c _ 2,?_,?_⟩
  · rw [show out 0=c 0 from install_other productSlots c _ 0 (by decide)]
    rw [show c 0=b 0 from install_other successorSlots b _ 0 (by decide)]
    rw [show b 0=a 0 from install_other countSlots a counts 0 (count_outside 0 (by decide))]
    exact (install_slot powerSlots power_injective (input S R) powers 0).trans p0
  · rw [show out 11=c 11 from install_other productSlots c _ 11 (by decide)]
    rw [show c 11=b 11 from install_other successorSlots b _ 11 (by decide)]
    exact (install_slot countSlots count_injective a counts 0).trans c0

end NearCubicWires.RepairOrdinary.CloseoutRowsCapacityDriver
