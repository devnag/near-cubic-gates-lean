import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleLiteral

namespace GR

/-! Cold schedule metadata from the actual framed language input. The
length, repeat driver, n template and literal initial index are all written. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Metadata
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def lengthSlots : Fin 2 → Fin 8 := ![0,1]
def copySlots : Fin 3 → Fin 8 := ![1,2,3]
def templateSlots : Fin 3 → Fin 8 := ![2,4,5]
def literalSlots : Fin 2 → Fin 8 := ![6,7]
def lengthProgram := RecoveryFocus.machine lengthSlots ClockNumericPrep.ellMachine
def copyProgram := RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
def templateProgram := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def literalProgram (word : List Bool) := RecoveryFocus.machine literalSlots (HierarchyFixedWord.machine word)
def machine := Composition.machine (Composition.machine (Composition.machine lengthProgram copyProgram) templateProgram) (literalProgram (UnaryTemplate.tape 1))
def input (bits : List Bool) : Fin 8 → List Bool := ![frame bits,[],[],[],[],[],[],[]]
def counted (bits : List Bool) : Fin 8 → List Bool :=
  ![frame bits,CompareMachine.word bits.length,[],[],[],[],[],[]]
def copied (bits : List Bool) : Fin 8 → List Bool :=
  ![frame bits,CompareMachine.word bits.length,List.replicate bits.length true,
    List.replicate (bits.length+2) false,[],[],[],[]]
def templated (bits : List Bool) : Fin 8 → List Bool :=
  ![frame bits,CompareMachine.word bits.length,List.replicate bits.length true,
    List.replicate (bits.length+2) false,UnaryTemplate.tape bits.length,
    List.replicate (bits.length+3) false,[],[]]
def output (bits word : List Bool) : Fin 8 → List Bool :=
  fun i => if i.val=6 then word else if i.val=7 then List.replicate word.length false else templated bits i

@[simp] theorem output_fields (bits word : List Bool) :
    output bits word 0 = frame bits ∧
    output bits word 1 = CompareMachine.word bits.length ∧
    output bits word 4 = UnaryTemplate.tape bits.length ∧ output bits word 6 = word :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem length_run (bits : List Bool) :
    ClockJoin.ReadyRun lengthProgram (4*bits.length+5) (input bits) (counted bits) := by
  have h := (HierarchyAllocation.length_ready bits).focus lengthSlots (by decide) (input bits)
    (by intro i; fin_cases i <;> rfl)
  have he : install lengthSlots (input bits)
      ![frame bits,false::List.replicate bits.length true] = counted bits := by
    apply HierarchyAllocation.install_eq _ (by decide)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  rw [he] at h
  exact h

theorem copy_run (bits : List Bool) :
    ClockJoin.ReadyRun copyProgram (2*bits.length+6) (counted bits) (copied bits) := by
  have hb := UWalkUnary.ready false false 0 bits.length
  simp only [UWalkUnary.input,UWalkUnary.result,UWalkUnary.source,ZeroPadding.pad_zero] at hb
  have h := hb.focus copySlots (by decide) (counted bits) (by intro i; fin_cases i <;> rfl)
  have he : install copySlots (counted bits)
      ![CompareMachine.word bits.length,UWalkUnary.output false false bits.length,
        List.replicate (bits.length+2) false] = copied bits := by
    apply HierarchyAllocation.install_eq _ (by decide)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  rw [he] at h
  exact h

theorem template_run (bits : List Bool) :
    ClockJoin.ReadyRun templateProgram (2*bits.length+8) (copied bits) (templated bits) := by
  have h := (DimensionTemplate.ready false bits.length).focus templateSlots (by decide) (copied bits)
    (by intro i; fin_cases i <;> rfl)
  have he : install templateSlots (copied bits) (DimensionTemplate.output false bits.length) = templated bits := by
    apply HierarchyAllocation.install_eq _ (by decide)
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  rw [he] at h
  exact h

theorem literal_run (bits word : List Bool) :
    ClockJoin.ReadyRun (literalProgram word) (2*word.length+2) (templated bits) (output bits word) := by
  have h := (literal_ready word).focus literalSlots (by decide) (templated bits)
    (by intro i; fin_cases i <;> rfl)
  have he : install literalSlots (templated bits) ![word,List.replicate word.length false] = output bits word := by
    apply HierarchyAllocation.install_eq _ (by decide)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h6 : i.val ≠ 6 := fun hv => hi 0 (Fin.ext hv.symm)
      have h7 : i.val ≠ 7 := fun hv => hi 1 (Fin.ext hv.symm)
      simp only [output,if_neg h6,if_neg h7]
  rw [he] at h
  exact h

theorem metadata_run (bits : List Bool) :
    ClockJoin.ReadyRun machine (8*bits.length+30) (input bits) (output bits (UnaryTemplate.tape 1)) := by
  have h := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (length_run bits) (copy_run bits))
      (template_run bits)) (literal_run bits (UnaryTemplate.tape 1))
  have he : ((4*bits.length+5+1+(2*bits.length+6))+1+(2*bits.length+8))+1+8 = 8*bits.length+30 := by omega
  change ClockJoin.ReadyRun machine (((4*bits.length+5+1+(2*bits.length+6))+1+(2*bits.length+8))+1+8) _ _ at h
  simpa only [he] using h

end
end NearCubicWires.RepairSource.CloseoutSchedule.Metadata

end GR
