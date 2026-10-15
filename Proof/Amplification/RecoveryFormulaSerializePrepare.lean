import Proof.Amplification.RecoveryFormulaCountWhole
import Proof.PCP.PCPTraversalFocused
import Proof.MachineModel.UInputFields

/-! Actual count and source loading for the existing balanced serializer.
The only external input is its framed field stream; every native count,
source field and scratch tape follows from the two executed calls. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countSlots : Fin 3→Fin 131 := ![0,3,129]
def unwrapSlots : Fin 3→Fin 131 := ![0,1,130]
def nativeSlots (i : Fin 128) : Fin 131 := ⟨i.val+1,by have h:=i.isLt; omega⟩
theorem count_injective : Function.Injective countSlots := by decide
theorem unwrap_injective : Function.Injective unwrapSlots := by decide
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; apply Fin.ext; have hv:=congrArg (fun i : Fin 131=>i.val) h; dsimp [nativeSlots] at hv; omega

def input (fields : List (List Bool)) : Fin 131→List Bool :=
  fun i=>if i.val=0 then frame (FieldList.stream fields) else []
noncomputable def counted (fields : List (List Bool)) := install countSlots (input fields)
  ![frame (FieldList.stream fields),VerifierDecoding.CompareMachine.word fields.length,
    List.replicate (RecoveryFormulaCount.rawBudget fields) false]
noncomputable def prepared (fields : List (List Bool)) := install unwrapSlots (counted fields)
  ![frame (FieldList.stream fields),FieldList.stream fields,List.replicate (FieldList.stream fields).length false]

noncomputable def countMachine := RecoveryFocus.machine countSlots RecoveryFormulaCount.machine
noncomputable def unwrapMachine := RecoveryFocus.machine unwrapSlots Streaming.machine
noncomputable def prepareMachine := Composition.machine countMachine unwrapMachine
def prepareBudget (fields : List (List Bool)) := 8*(FieldList.stream fields).length+9

theorem count_ready (fields : List (List Bool)) :
    ClockJoin.ReadyRun countMachine (RecoveryFormulaCount.budget fields) (input fields) (counted fields) :=
  (RecoveryFormulaCount.ready fields).focus countSlots count_injective (input fields)
    (by intro i; fin_cases i <;> rfl)

theorem counted_unwrap (fields : List (List Bool)) (i : Fin 3) :
    counted fields (unwrapSlots i)=![frame (FieldList.stream fields),[],[]] i := by
  fin_cases i
  · change install countSlots _ _ (countSlots 0)=_
    rw [install_slot _ count_injective]
    rfl
  · rw [counted,install_other _ _ _ _ (by decide)]
    rfl
  · rw [counted,install_other _ _ _ _ (by decide)]
    rfl

theorem prepare_ready (fields : List (List Bool)) :
    ClockJoin.ReadyRun prepareMachine (prepareBudget fields) (input fields) (prepared fields) := by
  have hu := (UInputFields.unwrap_ready (FieldList.stream fields)).focus unwrapSlots unwrap_injective
    (counted fields) (counted_unwrap fields)
  have hall := ClockJoin.join _ _ _ _ _ _ _ (count_ready fields) hu
  simpa only [prepareMachine,unwrapMachine,prepared,RecoveryFormulaCount.budget,prepareBudget,show
    (4*(FieldList.stream fields).length+6)+1+(4*(FieldList.stream fields).length+2)=
      8*(FieldList.stream fields).length+9 by omega] using hall

theorem prepared_native (fields : List (List Bool)) (i : Fin 128) :
    prepared fields (nativeSlots i)=PCPTraversal.input (FieldList.stream fields) fields.length i := by
  classical
  by_cases hi0 : i=0
  · subst i
    change install unwrapSlots _ _ (unwrapSlots 1)=_
    rw [install_slot _ unwrap_injective]
    rfl
  have hout : ∀ j,unwrapSlots j≠nativeSlots i := by
    intro j he
    have hv:=congrArg (fun k : Fin 131=>k.val) he
    have hi:=i.isLt
    have hn:i.val≠0 := fun h=>hi0 (Fin.ext h)
    fin_cases j <;> dsimp [unwrapSlots,nativeSlots] at hv <;> omega
  rw [prepared,install_other _ _ _ _ hout]
  by_cases hi2 : i=2
  · subst i
    change install countSlots _ _ (countSlots 1)=_
    rw [install_slot _ count_injective]
    rfl
  have hc : ∀ j,countSlots j≠nativeSlots i := by
    intro j he
    have hv:=congrArg (fun k : Fin 131=>k.val) he
    have hi:=i.isLt
    have hn:i.val≠2 := fun h=>hi2 (Fin.ext h)
    fin_cases j <;> dsimp [countSlots,nativeSlots] at hv <;> omega
  rw [counted,install_other _ _ _ _ hc]
  simp [input,nativeSlots,PCPTraversal.input,hi0,hi2]

end NearCubicWires.RepairSource.RecoveryFormulaSerialize
