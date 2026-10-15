import Proof.Hierarchy.CompetitorProducedScalarDecision
import Proof.Hierarchy.CompetitorSelectedDimensions

/-! Produce the bulk scalar caller's common width from actual raw record
width and record count. The fixed threshold width is printed by the program;
all copies, successor templates and multiplication are paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRecordScalarDrivers
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.ProjectionNormalization CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (b n : ℕ) : Fin 28 → List Bool := fun i =>
  if i=0 then List.replicate b true else if i=19 then List.replicate n true else []
def dimensionSlots (i : Fin 19) : Fin 28 := i.castAdd 9
def constantSlots : Fin 2 → Fin 28 := ![20,21]
def sumSlots : Fin 4 → Fin 28 := ![15,20,22,23]
def templateSlots : Fin 3 → Fin 28 := ![19,24,25]
def productSlots : Fin 4 → Fin 28 := ![22,24,26,27]
noncomputable def dimensions := RecoveryFocus.machine dimensionSlots CompetitorDimensions.machine
noncomputable def constant (l : ℕ) := RecoveryFocus.machine constantSlots
  (HierarchyFixedWord.machine (List.replicate (l+1) true))
noncomputable def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def template := RecoveryFocus.machine templateSlots (DimensionTemplate.machine true)
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def machine (l : ℕ) := Composition.machine dimensions
  (Composition.machine (constant l) (Composition.machine sum (Composition.machine template product)))
def budget (b l n : ℕ) := CompetitorDimensions.budget b+1+
  ((2*(l+1)+2)+1+((2*(width b+(l+1))+6)+1+((2*n+8)+1+
    WilliamsUnaryProduct.budget (width b+(l+1)) (n+1))))

theorem dimension_injective : Function.Injective dimensionSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 28 => k.val) h)

theorem drivers_run (b l n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine l) (budget b l n) (input b n) out ∧
      out 0=List.replicate b true ∧ out 15=List.replicate (width b) true ∧
      out 19=List.replicate n true ∧
      out 26=List.replicate (CompetitorProducedScalar.commonWidth b l n) true := by
  obtain ⟨d,hd,d0,d15,_⟩ := CompetitorDimensions.dimensions_run b
  let data1 := install dimensionSlots (input b n) d
  have h1 := bounded_focus dimensionSlots dimension_injective _ _ _ hd (input b n)
    (by intro i; fin_cases i <;> rfl)
  have fresh (i : Fin 28) (hi : 19 ≤ i.val) : data1 i=input b n i := by
    apply install_other
    intro j h
    have hv := congrArg Fin.val h
    change j.val=i.val at hv
    omega
  let c := ![List.replicate (l+1) true,List.replicate (l+1) false]
  have hc : ClockJoin.ReadyRun (HierarchyFixedWord.machine (List.replicate (l+1) true))
      (2*(l+1)+2) (fun _ => []) c := by
    simpa only [List.length_replicate] using
      CompetitorDimensionConstants.fixed_ready (List.replicate (l+1) true)
  let data2 := install constantSlots data1 c
  have h2 := bounded_focus constantSlots (by decide) _ _ _ hc data1 (by
    intro i; fin_cases i <;> exact fresh _ (by decide))
  let summed := ![List.replicate (width b) true,List.replicate (l+1) true,
    List.replicate (width b+(l+1)) true,List.replicate (width b+(l+1)+2) false]
  let data3 := install sumSlots data2 summed
  have h3 := bounded_focus sumSlots (by decide) _ _ _ (ClockUnarySum.sum_ready (width b) (l+1)) data2 (by
    intro i; fin_cases i
    · exact (install_other constantSlots _ _ 15 (by decide)).trans
        ((install_slot dimensionSlots dimension_injective _ d 15).trans d15)
    · exact install_slot constantSlots (by decide) _ c 0
    · exact (install_other constantSlots _ _ 22 (by decide)).trans (fresh _ (by decide))
    · exact (install_other constantSlots _ _ 23 (by decide)).trans (fresh _ (by decide)))
  let data4 := install templateSlots data3 (DimensionTemplate.output true n)
  have h4 := bounded_focus templateSlots (by decide) _ _ _ (DimensionTemplate.ready true n) data3 (by
    intro i; fin_cases i
    · exact (install_other sumSlots _ _ 19 (by decide)).trans
        ((install_other constantSlots _ _ 19 (by decide)).trans (fresh _ (by decide)))
    · exact (install_other sumSlots _ _ 24 (by decide)).trans
        ((install_other constantSlots _ _ 24 (by decide)).trans (fresh _ (by decide)))
    · exact (install_other sumSlots _ _ 25 (by decide)).trans
        ((install_other constantSlots _ _ 25 (by decide)).trans (fresh _ (by decide))))
  let data5 := install productSlots data4 (WilliamsUnaryProduct.output (width b+(l+1)) (n+1))
  have h5 := bounded_focus productSlots (by decide) _ _ _
    (CompetitorDimensions.unary_ready (width b+(l+1)) (n+1)) data4 (by
    intro i; fin_cases i
    · exact (install_other templateSlots _ _ 22 (by decide)).trans (install_slot sumSlots (by decide) _ summed 2)
    · exact install_slot templateSlots (by decide) _ (DimensionTemplate.output true n) 1
    · exact (install_other templateSlots _ _ 26 (by decide)).trans
        ((install_other sumSlots _ _ 26 (by decide)).trans
          ((install_other constantSlots _ _ 26 (by decide)).trans (fresh _ (by decide))))
    · exact (install_other templateSlots _ _ 27 (by decide)).trans
        ((install_other sumSlots _ _ 27 (by decide)).trans
          ((install_other constantSlots _ _ 27 (by decide)).trans (fresh _ (by decide)))))
  have htail := ClockJoin.join template product _ _ _ _ _ h4 h5
  have hsum := ClockJoin.join sum (Composition.machine template product) _ _ _ _ _ h3 htail
  have hconstant := ClockJoin.join (constant l) (Composition.machine sum (Composition.machine template product))
    _ _ _ _ _ h2 hsum
  have hall := ClockJoin.join dimensions
    (Composition.machine (constant l) (Composition.machine sum (Composition.machine template product)))
    _ _ _ _ _ h1 hconstant
  refine ⟨data5,hall,?_,?_,?_,?_⟩
  · exact (install_other productSlots _ _ 0 (by decide)).trans
      ((install_other templateSlots _ _ 0 (by decide)).trans
        ((install_other sumSlots _ _ 0 (by decide)).trans
          ((install_other constantSlots _ _ 0 (by decide)).trans
            ((install_slot dimensionSlots dimension_injective _ d 0).trans d0))))
  · exact (install_other productSlots _ _ 15 (by decide)).trans
      ((install_other templateSlots _ _ 15 (by decide)).trans (install_slot sumSlots (by decide) _ summed 0))
  · exact (install_other productSlots _ _ 19 (by decide)).trans
      (install_slot templateSlots (by decide) _ (DimensionTemplate.output true n) 0)
  · have hout := install_slot productSlots (by decide) data4
      (WilliamsUnaryProduct.output (width b+(l+1)) (n+1)) 2
    have hw : (width b+(l+1))*(n+1)=CompetitorProducedScalar.commonWidth b l n := by
      unfold CompetitorProducedScalar.commonWidth CompetitorThresholdCold.runtimeWidth CompetitorSumWidth.width
      ring
    exact hout.trans (congrArg (fun k => List.replicate k true) hw)

end NearCubicWires.RepairOrdinary.CompetitorRecordScalarDrivers
