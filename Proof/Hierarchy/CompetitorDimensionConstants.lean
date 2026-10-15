import Proof.Hierarchy.CompetitorRuntimeScalarWidth
import Proof.MachineModel.OrdinaryMatrixTemplateEntries
import Proof.MachineModel.OrdinaryWilliamsUnaryProduct

/-! The fixed coefficients one, two and 4096 of the scalar-width/capacity
formula are printed by the actual finite program before its unary calls. -/
namespace NearCubicWires.RepairOrdinary.CompetitorDimensionConstants
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 3) : Fin 2 → Fin 6 := if j.val=0 then ![0,1] else if j.val=1 then ![2,3] else ![4,5]
noncomputable def partProgram (j : Fin 3) (bits : List Bool) := RecoveryFocus.machine (slots j) (HierarchyFixedWord.machine bits)
noncomputable def machine := Composition.machine (partProgram 0 [true])
  (Composition.machine (partProgram 1 (UnaryTemplate.tape 2)) (partProgram 2 (UnaryTemplate.tape 4096)))

theorem fixed_ready (bits : List Bool) : ClockJoin.ReadyRun (HierarchyFixedWord.machine bits)
    (2*bits.length+2) (fun _ => []) ![bits,List.replicate bits.length false] := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready bits
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem constants_run : ∃ out,ClockJoin.ReadyRun machine 8214 (fun _ => []) out ∧
    out 0=[true] ∧ out 2=UnaryTemplate.tape 2 ∧ out 4=UnaryTemplate.tape 4096 := by
  let one := ![[true],List.replicate 1 false]
  let two := ![UnaryTemplate.tape 2,List.replicate (UnaryTemplate.tape 2).length false]
  let factor := ![UnaryTemplate.tape 4096,List.replicate (UnaryTemplate.tape 4096).length false]
  let first := install (slots 0) (fun _ : Fin 6 => []) one
  have hfirst := bounded_focus (slots 0) (by decide) _ _ _ (fixed_ready [true]) (fun _ : Fin 6 => []) (by intro i; rfl)
  have hiTwo : ∀ i,first (slots 1 i)=[] := by
    intro i
    exact install_other (slots 0) _ _ (slots 1 i) (by fin_cases i <;> decide)
  let second := install (slots 1) first two
  have hsecond := bounded_focus (slots 1) (by decide) _ _ _ (fixed_ready (UnaryTemplate.tape 2)) first hiTwo
  have hiFactor : ∀ i,second (slots 2 i)=[] := by
    intro i
    exact (install_other (slots 1) _ _ (slots 2 i) (by fin_cases i <;> decide)).trans
      (install_other (slots 0) _ _ (slots 2 i) (by fin_cases i <;> decide))
  let out := install (slots 2) second factor
  have hthird := bounded_focus (slots 2) (by decide) _ _ _ (fixed_ready (UnaryTemplate.tape 4096)) second hiFactor
  have htail := ClockJoin.join (partProgram 1 (UnaryTemplate.tape 2)) (partProgram 2 (UnaryTemplate.tape 4096))
    _ _ _ _ _ hsecond hthird
  have hall := ClockJoin.join (partProgram 0 [true])
    (Composition.machine (partProgram 1 (UnaryTemplate.tape 2)) (partProgram 2 (UnaryTemplate.tape 4096)))
    _ _ _ _ _ hfirst htail
  have hc : (2*([true] : List Bool).length+2)+1+
      ((2*(UnaryTemplate.tape 2).length+2)+1+(2*(UnaryTemplate.tape 4096).length+2))=8214 := by
    simp [UnaryTemplate.tape]
  rw [hc] at hall
  refine ⟨out,hall,?_,?_,?_⟩
  · exact (install_other (slots 2) _ _ 0 (by decide)).trans
      ((install_other (slots 1) _ _ 0 (by decide)).trans (install_slot (slots 0) (by decide) _ one 0))
  · exact (install_other (slots 2) _ _ 2 (by decide)).trans (install_slot (slots 1) (by decide) _ two 0)
  · exact install_slot (slots 2) (by decide) _ factor 0

end NearCubicWires.RepairOrdinary.CompetitorDimensionConstants
