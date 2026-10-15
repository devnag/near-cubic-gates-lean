import Proof.MachineModel.OrdinarySourceSATLiftWorkspace
import Proof.PCP.PCPSerializerCapacityFocus

/-! Fixed physical banks for the budgeted query lift. Input/budget parsing,
power production, source simulation and final output all use separate banks
apart from the explicitly shared source query and capacity driver. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : OrdinaryOracleProgram) := p.base.tapeCount+181
def core (p : OrdinaryOracleProgram) (i : Fin p.base.tapeCount) : Fin (tapes p) := ⟨1+i.val,by dsimp [tapes]; omega⟩
def kernel (p : OrdinaryOracleProgram) (i : Fin 156) : Fin (tapes p) :=
  if i.val=0 then core p p.queryTape else ⟨p.base.tapeCount+i.val,by dsimp [tapes]; omega⟩
def power (p : OrdinaryOracleProgram) (i : Fin 18) : Fin (tapes p) :=
  if i.val=7 then kernel p 1 else ⟨p.base.tapeCount+156+i.val,by dsimp [tapes]; omega⟩
def parse (p : OrdinaryOracleProgram) (i : Fin 5) : Fin (tapes p) :=
  ⟨p.base.tapeCount+174+i.val,by dsimp [tapes]; omega⟩
def output (p : OrdinaryOracleProgram) : Fin (tapes p) := ⟨p.base.tapeCount+179,by dsimp [tapes]; omega⟩
def log (p : OrdinaryOracleProgram) : Fin (tapes p) := ⟨p.base.tapeCount+180,by dsimp [tapes]; omega⟩
def inputSlot (p : OrdinaryOracleProgram) : Fin (tapes p) := ⟨0,by dsimp [tapes]; omega⟩
def outerSlots (p : OrdinaryOracleProgram) : Fin 3 → Fin (tapes p) := ![inputSlot p,parse p 0,parse p 1]
def firstSlots (p : OrdinaryOracleProgram) : Fin 3 → Fin (tapes p) := ![parse p 0,core p ⟨0,by have := p.base.twoTapes; omega⟩,parse p 3]
def secondSlots (p : OrdinaryOracleProgram) : Fin 3 → Fin (tapes p) := ![parse p 0,parse p 2,parse p 3]
def budgetSlots (p : OrdinaryOracleProgram) : Fin 3 → Fin (tapes p) := ![parse p 2,power p 0,parse p 4]
def finalSlots (p : OrdinaryOracleProgram) : Fin 3 → Fin (tapes p) := ![core p p.base.outputTape,output p,log p]

theorem core_injective (p : OrdinaryOracleProgram) : Function.Injective (core p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun i : Fin (tapes p) => i.val) h
  dsimp [core] at hv
  omega

theorem kernel_injective (p : OrdinaryOracleProgram) : Function.Injective (kernel p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun i : Fin (tapes p) => i.val) h
  have hq := p.queryTape.isLt
  dsimp [kernel,core] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem core_kernel_disjoint (p : OrdinaryOracleProgram) (i : Fin p.base.tapeCount)
    (j : Fin 156) (hj : j≠0) : core p i≠kernel p j := by
  intro he
  have hjv : j.val≠0 := by intro h; exact hj (Fin.ext h)
  have hi := i.isLt
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  simp only [core,kernel,if_neg hjv] at hv
  omega

def wiring (p : OrdinaryOracleProgram) : Wiring p (tapes p) where
  core := core p
  kernel := kernel p
  core_injective := core_injective p
  kernel_injective := kernel_injective p
  shared := rfl
  disjoint := core_kernel_disjoint p

def ports (p : OrdinaryOracleProgram) : Ports (tapes p) where
  twoTapes := by dsimp [tapes]; omega
  outputTape := output p
  outputFresh := by dsimp [output]; omega
  queryTape := kernel p Kernel.outputSlot
  queryFresh := by simp [kernel,Kernel.outputSlot,Kernel.bank]

theorem power_injective (p : OrdinaryOracleProgram) : Function.Injective (power p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun i : Fin (tapes p) => i.val) h
  dsimp [power,kernel] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem outer_injective (p : OrdinaryOracleProgram) : Function.Injective (outerSlots p) := by
  intro i j h
  have hv := congrArg (fun i : Fin (tapes p) => i.val) h
  fin_cases i <;> fin_cases j <;> simp_all [outerSlots,inputSlot,parse]

theorem first_injective (p : OrdinaryOracleProgram) : Function.Injective (firstSlots p) := by
  intro i j h
  have hv := congrArg (fun i : Fin (tapes p) => i.val) h
  fin_cases i <;> fin_cases j <;> simp_all [firstSlots,parse,core]

theorem second_injective (p : OrdinaryOracleProgram) : Function.Injective (secondSlots p) := by
  intro i j h
  have hv := congrArg (fun i : Fin (tapes p) => i.val) h
  fin_cases i <;> fin_cases j <;> simp_all [secondSlots,parse]

theorem budget_injective (p : OrdinaryOracleProgram) : Function.Injective (budgetSlots p) := by
  intro i j h
  have hv := congrArg (fun i : Fin (tapes p) => i.val) h
  fin_cases i <;> fin_cases j <;> simp_all [budgetSlots,parse,power]

theorem final_injective (p : OrdinaryOracleProgram) : Function.Injective (finalSlots p) := by
  intro i j h
  have hv := congrArg (fun i : Fin (tapes p) => i.val) h
  have ho := p.base.outputTape.isLt
  fin_cases i <;> fin_cases j <;> simp_all [finalSlots,core,output,log] <;> omega

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
