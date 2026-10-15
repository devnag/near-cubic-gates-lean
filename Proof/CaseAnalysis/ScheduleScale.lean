import Proof.PCP.ProjectionDimensionTemplate
import Proof.PCP.ProjectionDimensionPowerBounds
import Proof.MachineModel.UWalkUnary
import Proof.MachineModel.ClockUnarySum

/-! Pay the fixed-copy scaling of q+1+r using existing unary operations.
The two short inputs are already produced; every other tape starts blank. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Scale
open LocalBitMultitape RepairOrdinary RecoveryRootRound VerifierDecoding
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def copySlots : Fin 3→Fin 12 := ![1,2,3]
def sumSlots : Fin 4→Fin 12 := ![0,2,4,5]
def templateSlots : Fin 3→Fin 12 := ![4,6,7]
def powerSlots : Fin (DimensionPower.tapes 1)→Fin 12 := ![6,8,9,10,11]
def copy := RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
def template := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def power (copies : Nat) := RecoveryFocus.machine powerSlots (DimensionPower.machine 1 copies)
def machine (copies : Nat) := Composition.machine
  (Composition.machine (Composition.machine copy sum) template) (power copies)
def input (q r : Nat) : Fin 12→List Bool := ![List.replicate q true,CompareMachine.word r,[],[],[],[],[],[],[],[],[],[]]
def afterCopy (q r : Nat) := install copySlots (input q r) (UWalkUnary.result false false 0 r)
def afterSum (q r : Nat) := install sumSlots (afterCopy q r)
  ![List.replicate q true,List.replicate r true,List.replicate (q+r) true,List.replicate (q+r+2) false]
def afterTemplate (q r : Nat) := install templateSlots (afterSum q r) (DimensionTemplate.output false (q+r))
def budget (copies q r : Nat) := (2*r+6)+1+(2*(q+r)+6)+1+(2*(q+r)+8)+1+DimensionPower.cost copies (q+r) 1

theorem scale_run (copies q r : Nat) : ∃ out,
    ClockJoin.ReadyRun (machine copies) (budget copies q r) (input q r) out ∧
      out 10=List.replicate (copies*(q+r)) true := by
  have hc:=(UWalkUnary.ready false false 0 r).focus copySlots (by decide) (input q r) (by
    intro i;fin_cases i
    · simp [input,copySlots,UWalkUnary.input,UWalkUnary.source]
    all_goals rfl)
  change ClockJoin.ReadyRun copy (2*r+6) (input q r) (afterCopy q r) at hc
  have hs:=(ClockUnarySum.sum_ready q r).focus sumSlots (by decide) (afterCopy q r) (by
    intro i;fin_cases i
    · rw [afterCopy,install_other _ _ _ _ (by decide)];rfl
    · change install copySlots _ _ (copySlots 1)=_
      rw [install_slot _ (by decide)]
      simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead]
    all_goals rw [afterCopy,install_other _ _ _ _ (by decide)];rfl)
  change ClockJoin.ReadyRun sum (2*(q+r)+6) (afterCopy q r) (afterSum q r) at hs
  have ht:=(DimensionTemplate.ready false (q+r)).focus templateSlots (by decide) (afterSum q r) (by
    intro i;fin_cases i
    · change install sumSlots _ _ (sumSlots 2)=_
      rw [install_slot _ (by decide)]
      rfl
    all_goals
      rw [afterSum,install_other _ _ _ _ (by decide),afterCopy,install_other _ _ _ _ (by decide)]
      rfl)
  change ClockJoin.ReadyRun template (2*(q+r)+8) (afterSum q r) (afterTemplate q r) at ht
  obtain ⟨powerOut,hp,_,hv⟩:=DimensionPower.power_run 1 copies (q+r)
  have hpf:=hp.focus powerSlots (by decide) (afterTemplate q r) (by
    intro i;fin_cases i
    · change install templateSlots _ _ (templateSlots 1)=_
      rw [install_slot _ (by decide)]
      simp [DimensionTemplate.output]
      rfl
    all_goals
      rw [afterTemplate,install_other _ _ _ _ (by decide),afterSum,install_other _ _ _ _ (by decide),
        afterCopy,install_other _ _ _ _ (by decide)]
      rfl)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hc hs) ht) hpf,?_⟩
  change install powerSlots _ _ (powerSlots (DimensionPower.valueSlot 1 1 le_rfl))=_
  rw [install_slot _ (by decide),hv,pow_one]

theorem budget_bound (copies q r : Nat) : budget copies q r ≤ (16*copies+64)*(q+r+2)^2 := by
  have hp:=DimensionPower.cost_bound 1 copies (q+r) 1 le_rfl
  have hpow : (q+r+1)^2 ≤ (q+r+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have hlarge : q+r+2 ≤ (q+r+2)^2 := Nat.le_self_pow (by decide) _
  have hone : 1 ≤ (q+r+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hmul:=Nat.mul_le_mul_left (6*copies) hpow
  have hconst:=Nat.mul_le_mul_left (2*copies+9) hone
  unfold budget
  norm_num only at hp
  nlinarith

end
end NearCubicWires.RepairSource.CloseoutSchedule.Scale
