import Proof.Hierarchy.CompetitorDimensions

/-! The dimension prefix supplies the actual W/C tapes of the cold scalar
decision from its single short-width driver. All scalar work and fixed
threshold work remain blank for the following executed consumer. -/
namespace NearCubicWires.RepairOrdinary.CompetitorDimensionedDecision
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 110) : Fin 126 := i.castAdd 16
def dimensionSlots (i : Fin 19) : Fin 126 :=
  if i.val=0 then 84 else if i.val=15 then 6 else if i.val=17 then 90
  else if h : i.val<15 then ⟨i.val+109,by omega⟩ else if i.val=16 then 124 else 125
def shortInput (b : ℕ) (xs : List CompetitorValidity.Estimate) : Fin 110 → List Bool := fun i =>
  if i.val=6 ∨ i.val=90 then [] else CompetitorThresholdCold.input b xs i
def input (b : ℕ) (xs : List CompetitorValidity.Estimate) : Fin 126 → List Bool :=
  Fin.addCases (m := 110) (n := 16) (motive := fun _ => List Bool) (shortInput b xs) (fun _ => [])
noncomputable def prepareProgram := RecoveryFocus.machine dimensionSlots CompetitorDimensions.machine

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 126 => a.val) h)
theorem dimension_injective : Function.Injective dimensionSlots := by decide
theorem dimension_other (j : Fin 19) (i : Fin 110) (h6 : i≠6) (h84 : i≠84) (h90 : i≠90) :
    dimensionSlots j≠native i := by
  intro h
  have hv := congrArg (fun a : Fin 126 => a.val) h
  change (dimensionSlots j).val=i.val at hv
  have hv6 : i.val≠6 := fun he => h6 (Fin.ext he)
  have hv84 : i.val≠84 := fun he => h84 (Fin.ext he)
  have hv90 : i.val≠90 := fun he => h90 (Fin.ext he)
  simp only [dimensionSlots] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem prepare_run (b : ℕ) (xs : List CompetitorValidity.Estimate) :
    ∃ out,ClockJoin.ReadyRun prepareProgram (CompetitorDimensions.budget b) (input b xs) out ∧
      (∀ i,out (native i)=CompetitorThresholdCold.input b xs i) := by
  obtain ⟨dimensions,hr,h0,h15,h17⟩ := CompetitorDimensions.dimensions_run b
  have hin : ∀ i,input b xs (dimensionSlots i)=CompetitorDimensions.input b i := by
    intro i
    fin_cases i <;> rfl
  have hf := bounded_focus dimensionSlots dimension_injective _ _ _ hr (input b xs) hin
  refine ⟨install dimensionSlots (input b xs) dimensions,hf,?_⟩
  intro i
  by_cases h6 : i=6
  · subst i
    exact (install_slot dimensionSlots dimension_injective _ dimensions 15).trans h15
  · by_cases h84 : i=84
    · subst i
      exact (install_slot dimensionSlots dimension_injective _ dimensions 0).trans h0
    · by_cases h90 : i=90
      · subst i
        exact (install_slot dimensionSlots dimension_injective _ dimensions 17).trans h17
      · have hother := install_other dimensionSlots (input b xs) dimensions (native i)
          (fun j => dimension_other j i h6 h84 h90)
        have hv6 : i.val≠6 := fun he => h6 (Fin.ext he)
        have hv90 : i.val≠90 := fun he => h90 (Fin.ext he)
        simpa only [input,native,Fin.addCases_left,shortInput,hv6,hv90,or_self,if_false] using hother

end NearCubicWires.RepairOrdinary.CompetitorDimensionedDecision
