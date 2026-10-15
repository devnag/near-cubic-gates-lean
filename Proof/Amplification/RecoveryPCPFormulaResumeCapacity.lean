import Proof.Amplification.RecoveryPCPFormulaResumeSparse
import Proof.Amplification.RecoveryProjectionCapacity
import Proof.MachineModel.ClockUnarySum

/-! From the original binary R/Q fields, execute both unary parsers, the
existing row capacity, the physical R+Q sum and the exact source-clause
capacity. Every true driver required by the formula loop is actual data. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCapacity
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
open RadixSemantics VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rSlots (i : Fin 28) : Fin 55 := i.castAdd 27
def qSlots (i : Fin 7) : Fin 55 := ⟨28+i.val,by have hi:=i.isLt; omega⟩
def sumSlots : Fin 4→Fin 55 := ![5,33,35,36]
def powerSlots (i : Fin 18) : Fin 55 :=
  if i=0 then 35 else if i=7 then 37 else ⟨37+i.val,by have hi:=i.isLt; omega⟩
theorem r_injective : Function.Injective rSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 55=>i.val) h)
theorem q_injective : Function.Injective qSlots := by
  intro i j h; apply Fin.ext
  have hv:=congrArg (fun i : Fin 55=>i.val) h
  dsimp [qSlots] at hv; omega
theorem sum_injective : Function.Injective sumSlots := by decide
theorem power_injective : Function.Injective powerSlots := by
  intro i j h; apply Fin.ext
  have hv:=congrArg (fun i : Fin 55=>i.val) h
  dsimp [powerSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
noncomputable def rMachine := RecoveryFocus.machine rSlots (RecoveryProjectionCapacity.machine 1048576)
noncomputable def qMachine := RecoveryFocus.machine qSlots RecoveryProjectionDimension.machine
noncomputable def sumMachine := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def powerMachine := RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 2 536870912)
noncomputable def dimensions := Composition.machine rMachine qMachine
noncomputable def summed := Composition.machine dimensions sumMachine
noncomputable def machine := Composition.machine summed powerMachine
def input (rBits qBits : List Bool) (i : Fin 55) :=
  if i=0 then frame rBits else if i=28 then frame qBits else []
def budget (rBits qBits : List Bool) :=
  RecoveryProjectionCapacity.budget 1048576 rBits+1+RecoveryProjectionDimension.budget qBits+1+
    (2*(value rBits+value qBits)+6)+1+PCPSerializerCapacity.Power.budget 2 536870912 (value rBits+value qBits)

theorem dimensions_run (rBits qBits : List Bool) : ∃ out,
    ClockJoin.ReadyRun dimensions
      (RecoveryProjectionCapacity.budget 1048576 rBits+1+RecoveryProjectionDimension.budget qBits)
      (input rBits qBits) out ∧
      out 3=CompareMachine.word (value rBits) ∧ out 5=List.replicate (value rBits) true ∧
      out 17=List.replicate (RecoveryProjectionRows.capacity (value rBits)) true ∧
      out 31=CompareMachine.word (value qBits) ∧ out 33=List.replicate (value qBits) true ∧
      (∀ i : Fin 20,out (i.natAdd 35)=[]) := by
  obtain ⟨r,hr,r3,r5,r17⟩ := RecoveryProjectionCapacity.capacity_ready 1048576 rBits
  let mid:=install rSlots (input rBits qBits) r
  have first:=hr.focus rSlots r_injective (input rBits qBits) (by intro i; fin_cases i <;> rfl)
  obtain ⟨q,hq,q3,q5⟩ := RecoveryProjectionDimension.unary_ready qBits
  have second:=hq.focus qSlots q_injective mid (by
    intro i
    dsimp only [mid]
    rw [install_other _ _ _ _ (by
      intro j h; have hv:=congrArg (fun i : Fin 55=>i.val) h; have hj:=j.isLt
      dsimp [rSlots,qSlots] at hv; omega)]
    fin_cases i <;> rfl)
  let out:=install qSlots mid q
  have whole:=ClockJoin.join rMachine qMachine _ _ _ _ _ first second
  have old (i : Fin 28) : out (rSlots i)=r i := by
    dsimp only [out,mid]
    rw [install_other _ _ _ _ (by
      intro j h; have hv:=congrArg (fun i : Fin 55=>i.val) h; have hi:=i.isLt
      dsimp [rSlots,qSlots] at hv; omega),install_slot rSlots r_injective]
  refine ⟨out,whole,(old 3).trans r3,(old 5).trans r5,(old 17).trans r17,?_,?_,?_⟩
  · exact (install_slot qSlots q_injective mid q 3).trans q3
  · exact (install_slot qSlots q_injective mid q 5).trans q5
  · intro i
    dsimp only [out,mid]
    rw [install_other _ _ _ _ (by
      intro j h; have hv:=congrArg (fun i : Fin 55=>i.val) h; have hj:=j.isLt
      dsimp [qSlots] at hv; omega),install_other _ _ _ _ (by
      intro j h; have hv:=congrArg (fun i : Fin 55=>i.val) h; have hj:=j.isLt
      dsimp [rSlots] at hv; omega)]
    simp only [input]
    rw [if_neg (by intro h; have hv:=congrArg (fun i : Fin 55=>i.val) h; change 35+i.val=0 at hv; omega),
      if_neg (by intro h; have hv:=congrArg (fun i : Fin 55=>i.val) h; change 35+i.val=28 at hv; omega)]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCapacity
