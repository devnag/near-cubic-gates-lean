import Proof.CaseAnalysis.ScheduleBound
import Proof.Amplification.RecoveryPCPFormulaResumeSearchCountFrame

/-! The selected raw source length is physically framed for the existing
ordinary refuter. Both conversions use already checked machines. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Output
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def templateSlots : Fin 3 → Fin 4 := ![0,1,2]
def frameSlots : Fin 2 → Fin 4 := ![1,3]
theorem template_injective : Function.Injective templateSlots := by decide
theorem frame_injective : Function.Injective frameSlots := by decide
def first := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def second := RecoveryFocus.machine frameSlots RecoveryPCPFormulaResumeSearchCount.frameMachine
def machine := Composition.machine first second
def input (C n : Nat) : Fin 4 → List Bool := ![ZeroPadding.pad C (List.replicate n true),[],[],[]]

theorem template_word (n : Nat) :
    ZeroPadding.pad (n+2) (CompareMachine.word n) = UnaryTemplate.tape n := by
  simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem framed_ready (n : Nat) :
    ClockJoin.ReadyRun RecoveryPCPFormulaResumeSearchCount.frameMachine (4*n+6)
      ![UnaryTemplate.tape n,[]] ![UnaryTemplate.tape n,frame (List.replicate n true)] := by
  have h := PCPPairReusable.padded_ready _ _ _
    (RecoveryPCPFormulaResumeSearchCount.frame_ready n) (![n+2,0] : Fin 2 → Nat)
  have hi : (fun i : Fin 2 => ZeroPadding.pad ((![n+2,0] : Fin 2 → Nat) i)
      (RecoveryPCPFormulaResumeSearchCount.frameInput n i)) = ![UnaryTemplate.tape n,[]] := by
    funext i; fin_cases i
    · exact template_word n
    · rfl
  have ho : (fun i : Fin 2 => ZeroPadding.pad ((![n+2,0] : Fin 2 → Nat) i)
      (RecoveryPCPFormulaResumeSearchCount.frameOutput n i)) =
        ![UnaryTemplate.tape n,frame (List.replicate n true)] := by
    funext i; fin_cases i
    · exact template_word n
    · exact ZeroPadding.pad_zero _
  rw [hi,ho] at h
  exact h

theorem output_run (C n : Nat) : ∃ out,
    ClockJoin.ReadyRun machine (6*n+15) (input C n) out ∧
    out 3 = frame (List.replicate n true) := by
  let caps : Fin 3 → Nat := ![C,0,0]
  let localOut := fun i => ZeroPadding.pad (caps i) (DimensionTemplate.output false n i)
  have ht := PCPPairReusable.padded_ready _ _ _ (DimensionTemplate.ready false n) caps
  let a := install templateSlots (input C n) localOut
  have ha := ht.focus templateSlots template_injective (input C n) (by
    intro i; fin_cases i <;> rfl)
  have hin (i : Fin 2) : a (frameSlots i) = (![UnaryTemplate.tape n,[]] : Fin 2 → List Bool) i := by
    fin_cases i
    · change install templateSlots (input C n) localOut (templateSlots 1) = _
      rw [install_slot _ template_injective]
      exact ZeroPadding.pad_zero _
    · exact install_other templateSlots (input C n) localOut 3 (by
        intro j; fin_cases j <;> decide)
  have hb := (framed_ready n).focus frameSlots frame_injective a hin
  refine ⟨install frameSlots a (![UnaryTemplate.tape n,frame (List.replicate n true)] : Fin 2 → List Bool),?_,?_⟩
  · have h := ClockJoin.join _ _ _ _ _ _ _ ha hb
    have hc : (2*n+8)+1+(4*n+6) = 6*n+15 := by omega
    rw [hc] at h
    exact h
  · exact install_slot frameSlots frame_injective a
      (![UnaryTemplate.tape n,frame (List.replicate n true)] : Fin 2 → List Bool) 1

end
end NearCubicWires.RepairSource.CloseoutSchedule.Output
