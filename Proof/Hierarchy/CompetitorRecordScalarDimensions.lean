import Proof.Hierarchy.CompetitorRecordScalarDrivers
import Proof.PCP.ProjectionNormalizationDriverAtoms

/-! Complete cold scalar metadata: the actual record width and count
produce the common width, both wide widths, workspace capacity and loop
counter. No scalar allocation word remains a supplied input. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRecordScalarDimensions
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.ProjectionNormalization CompetitorRationalDecision
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 28) : Fin 49 := i.castAdd 21
def input (b n : ℕ) : Fin 49 → List Bool :=
  Fin.addCases (m := 28) (n := 21) (motive := fun _ => List Bool)
    (CompetitorRecordScalarDrivers.input b n) (fun _ => [])
def dimensionSlots (i : Fin 19) : Fin 49 := if i=0 then 26 else ⟨i.val+27,by omega⟩
def counterSlots : Fin 4 → Fin 49 := ![19,46,47,48]
noncomputable def first (l : ℕ) := ClockJoin.lifted (e := 21) (Equiv.refl (Fin 49))
  (CompetitorRecordScalarDrivers.machine l)
noncomputable def dimensions := RecoveryFocus.machine dimensionSlots CompetitorDimensions.machine
noncomputable def counter := RecoveryFocus.machine counterSlots Counter.machine
noncomputable def machine (l : ℕ) := Composition.machine (first l) (Composition.machine dimensions counter)
def budget (b l n : ℕ) := CompetitorRecordScalarDrivers.budget b l n+1+
  (CompetitorDimensions.budget (CompetitorProducedScalar.commonWidth b l n)+1+Counter.budget n)

theorem dimension_injective : Function.Injective dimensionSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [dimensionSlots] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem dimensions_run (b l n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine l) (budget b l n) (input b n) out ∧
      out 15=List.replicate (width b) true ∧
      out 42=List.replicate (width (CompetitorProducedScalar.commonWidth b l n)) true ∧
      out 26=List.replicate (CompetitorProducedScalar.commonWidth b l n) true ∧
      out 44=List.replicate (CompetitorReusableDecision.capacity (CompetitorProducedScalar.commonWidth b l n)) true ∧
      out 47=CompareMachine.word n := by
  let t := CompetitorProducedScalar.commonWidth b l n
  obtain ⟨d,hd,_,d15,d19,d26⟩ := CompetitorRecordScalarDrivers.drivers_run b l n
  let data1 : Fin 49 → List Bool := Fin.addCases (m := 28) (n := 21)
    (motive := fun _ => List Bool) d (fun _ => [])
  have h1 : ClockJoin.ReadyRun (first l) (CompetitorRecordScalarDrivers.budget b l n) (input b n) data1 :=
    ClockJoin.lift (e := 21) (Equiv.refl (Fin 49)) _ _ _ _ (fun _ => []) hd
  obtain ⟨w,hw,w0,w15,w17⟩ := CompetitorDimensions.dimensions_run t
  let data2 := install dimensionSlots data1 w
  have h2 := bounded_focus dimensionSlots dimension_injective _ _ _ hw data1 (by
    intro i; fin_cases i
    · exact d26
    all_goals rfl)
  obtain ⟨c,hc,_,c2⟩ := DriverAtoms.counter_run n
  have h3 := bounded_focus counterSlots (by decide) _ _ _ hc data2 (by
    intro i; fin_cases i
    · exact (install_other dimensionSlots _ _ 19 (by decide)).trans d19
    · exact install_other dimensionSlots _ _ 46 (by decide)
    · exact install_other dimensionSlots _ _ 47 (by decide)
    · exact install_other dimensionSlots _ _ 48 (by decide))
  have htail := ClockJoin.join dimensions counter _ _ _ _ _ h2 h3
  have hall := ClockJoin.join (first l) (Composition.machine dimensions counter) _ _ _ _ _ h1 htail
  refine ⟨install counterSlots data2 c,hall,?_,?_,?_,?_,?_⟩
  · exact (install_other counterSlots _ _ 15 (by decide)).trans
      ((install_other dimensionSlots _ _ 15 (by decide)).trans d15)
  · exact (install_other counterSlots _ _ 42 (by decide)).trans
      ((install_slot dimensionSlots dimension_injective _ w 15).trans w15)
  · exact (install_other counterSlots _ _ 26 (by decide)).trans
      ((install_slot dimensionSlots dimension_injective _ w 0).trans w0)
  · exact (install_other counterSlots _ _ 44 (by decide)).trans
      ((install_slot dimensionSlots dimension_injective _ w 17).trans w17)
  · exact (install_slot counterSlots (by decide) _ c 2).trans c2

end NearCubicWires.RepairOrdinary.CompetitorRecordScalarDimensions
