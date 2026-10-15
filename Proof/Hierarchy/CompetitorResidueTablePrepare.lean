import Proof.Hierarchy.CompetitorResidueTableClear
import Proof.Hierarchy.CompetitorDimensions

/-! Cold residue-table preparation from the real raw W/Q fields, P/N bank
and cell-count driver. Capacity and the second width tape are produced. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dimensionSlots (i : Fin 19) : Fin 46 :=
  if i=0 then 9 else if i=17 then 21 else ⟨i.val+27,by omega⟩
def copySlots : Fin 4 → Fin 46 := ![9,10,20,11]
def bodySlots (i : Fin 27) : Fin 46 := i.castAdd 19
def input (w q n : ℕ) (source : List Bool) : Fin 46 → List Bool := fun i =>
  if i=9 then List.replicate w true else if i=4 then List.replicate q true
  else if i=19 then source else if i=27 then CompareMachine.word n else []
noncomputable def dimensionsProgram := RecoveryFocus.machine dimensionSlots CompetitorDimensions.machine
noncomputable def copyProgram := RecoveryFocus.machine copySlots ClockUnarySum.machine
noncomputable def coldClearProgram := RecoveryFocus.machine bodySlots clearProgram
noncomputable def coldPrepareProgram := Composition.machine dimensionsProgram
  (Composition.machine copyProgram coldClearProgram)
def coldPrepareBudget (w : ℕ) := CompetitorDimensions.budget w+2*w+2*capacity w+12

theorem dimension_injective : Function.Injective dimensionSlots := by decide
theorem body_injective : Function.Injective bodySlots := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 46 => a.val) h)

theorem cold_prepare_run (w q n : ℕ) (source : List Bool) :
    ∃ out,ClockJoin.ReadyRun coldPrepareProgram (coldPrepareBudget w) (input w q n source) out ∧
      Store w q source [] (out ∘ bodySlots) ∧ out 27=CompareMachine.word n := by
  obtain ⟨dimensions,hready,hw,_,hcap⟩ := CompetitorDimensions.dimensions_run w
  have hin : ∀ i,input w q n source (dimensionSlots i)=CompetitorDimensions.input w i := by
    intro i
    fin_cases i <;> simp [dimensionSlots,input,CompetitorDimensions.input,
      CompetitorDimensions.extendTapes,CompetitorDimensions.bootstrapInput,Fin.addCases]
  let first := install dimensionSlots (input w q n source) dimensions
  have hfirst := CompetitorRationalProducts.bounded_focus dimensionSlots dimension_injective _ _ _ hready
    (input w q n source) hin
  have first9 : first 9=List.replicate w true :=
    (install_slot dimensionSlots dimension_injective _ dimensions 0).trans hw
  have first21 : first 21=List.replicate (capacity w) true :=
    (install_slot dimensionSlots dimension_injective _ dimensions 17).trans hcap
  have first_keep (i : Fin 46) (hi : ∀ j,dimensionSlots j≠i) : first i=input w q n source i :=
    install_other dimensionSlots _ _ i hi
  let copied : Fin 4 → List Bool :=
    ![List.replicate w true,[],List.replicate w true,List.replicate (w+2) false]
  have copyReady : ClockJoin.ReadyRun ClockUnarySum.machine (2*w+6)
      ![List.replicate w true,[],[],[]] copied := by
    obtain ⟨r,hr,ht,hh,hs⟩ := ClockUnarySum.sum_ready w 0
    exact ⟨r,by simpa using hr,by simpa [copied] using ht,hh,by omega⟩
  have hcopy : ∀ i,first (copySlots i)=![List.replicate w true,[],[],[]] i := by
    intro i
    fin_cases i
    · exact first9
    · exact first_keep 10 (by decide)
    · exact first_keep 20 (by decide)
    · exact first_keep 11 (by decide)
  let second := install copySlots first copied
  have hsecond := CompetitorRationalProducts.bounded_focus copySlots (by decide) _ _ _ copyReady first hcopy
  have second_keep (i : Fin 46) (hd : ∀ j,dimensionSlots j≠i) (hc : ∀ j,copySlots j≠i) :
      second i=input w q n source i :=
    (install_other copySlots first copied i hc).trans (first_keep i hd)
  have second9 : second 9=List.replicate w true := install_slot copySlots (by decide) _ copied 0
  have second20 : second 20=List.replicate w true := install_slot copySlots (by decide) _ copied 2
  have second4 : second 4=List.replicate q true := second_keep 4 (by decide) (by decide)
  have second19 : second 19=source := second_keep 19 (by decide) (by decide)
  have second8 : second 8=[] := second_keep 8 (by decide) (by decide)
  have second21 : second 21=List.replicate (capacity w) true :=
    (install_other copySlots _ copied 21 (by decide)).trans first21
  have second22 : second 22=[] := second_keep 22 (by decide) (by decide)
  have hblank : ∀ i,(second ∘ bodySlots) (workSlots i)=[] := by
    intro i
    fin_cases i
    all_goals first
      | exact second_keep 0 (by decide) (by decide)
      | exact second_keep 1 (by decide) (by decide)
      | exact second_keep 2 (by decide) (by decide)
      | exact second_keep 3 (by decide) (by decide)
      | exact second_keep 5 (by decide) (by decide)
      | exact second_keep 6 (by decide) (by decide)
      | exact second_keep 7 (by decide) (by decide)
      | exact install_slot copySlots (by decide) first copied 1
  obtain ⟨clearReady,hstore⟩ := cold_clear_run w q source (second ∘ bodySlots)
    second9 second20 second4 second19 second8 second21 second22 hblank
  let out := install bodySlots second (coldCleared w (second ∘ bodySlots))
  have hclear := CompetitorRationalProducts.bounded_focus bodySlots body_injective _ _ _ clearReady second
    (by intro i; rfl)
  have htail := ClockJoin.join copyProgram coldClearProgram _ _ _ _ _ hsecond hclear
  have hall := ClockJoin.join dimensionsProgram (Composition.machine copyProgram coldClearProgram)
    _ _ _ _ _ hfirst htail
  have hcost : CompetitorDimensions.budget w+1+((2*w+6)+1+(2*capacity w+4))=coldPrepareBudget w := by
    unfold coldPrepareBudget
    omega
  rw [hcost] at hall
  refine ⟨out,hall,?_,?_⟩
  · have he : out ∘ bodySlots=coldCleared w (second ∘ bodySlots) := by
      funext i
      exact install_slot bodySlots body_injective second _ i
    rw [he]
    exact hstore
  · exact (install_other bodySlots second _ 27 (by
      intro i hi
      have hv := congrArg (fun a : Fin 46 => a.val) hi
      change i.val=27 at hv
      omega)).trans (second_keep 27 (by decide) (by decide))

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
