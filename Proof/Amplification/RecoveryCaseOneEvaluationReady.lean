import Proof.Amplification.RecoveryCaseOneEvaluatorReady
import Proof.Amplification.RecoveryCaseOneEvaluationFrame

/-! Actual generated schema plus address reaches the canonical output bit
through the physical assembler and the existing complete-table evaluator. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneEvaluation
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fieldSlots (i : Fin 8) : Fin 28 := i.castAdd 20
def evalSlots (i : Fin 21) : Fin 28 := if i=0 then 6 else ⟨7+i.val,by have hi:=i.isLt; omega⟩
theorem field_injective : Function.Injective fieldSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 28=>i.val) h)
theorem eval_injective : Function.Injective evalSlots := by
  intro i j h
  have hv:=congrArg (fun i : Fin 28=>i.val) h
  apply Fin.ext
  dsimp [evalSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
def first := RecoveryFocus.machine fieldSlots RecoveryCaseOneEvaluationPayload.framedMachine
def last := RecoveryFocus.machine evalSlots RecoveryCaseOneEvaluator.machine
def machine := Composition.machine first last
def schema {n : Nat} (f : BoolFunction n) := frame n.bits++boolFunctionTable f
def input (left right : List Bool) (i : Fin 28) : List Bool :=
  if i.val=0 then frame left else if i.val=1 then frame right else []
def budget {n : Nat} (f : BoolFunction n) (address : BitInput n) :=
  RecoveryCaseOneEvaluationPayload.framedBudget (schema f) (List.ofFn address)+1+
    RecoveryCaseOneEvaluator.budget f address

theorem ready {n : Nat} (f : BoolFunction n) (address : BitInput n) :
    ∃ out,ClockJoin.ReadyRun machine (budget f address) (input (schema f) (List.ofFn address)) out ∧
      out 26=frame (f address).toNat.bits := by
  obtain ⟨framed,hframed,framedValue⟩ := RecoveryCaseOneEvaluationPayload.framed_ready (schema f) (List.ofFn address)
  let a:=install fieldSlots (input (schema f) (List.ofFn address)) framed
  have ha:=hframed.focus fieldSlots field_injective (input (schema f) (List.ofFn address)) (by
    intro i; fin_cases i <;> rfl)
  obtain ⟨evaluated,hevaluated,evaluatedValue⟩ := RecoveryCaseOneEvaluator.ready f address
  have hb:=hevaluated.focus evalSlots eval_injective a (by
    intro i
    rw [RecoveryCaseOneEvaluator.input_lookup]
    by_cases hi : i=0
    · subst i
      exact (install_slot fieldSlots field_injective _ framed 6).trans framedValue
    · have hiv : i.val≠0 := fun h=>hi (Fin.ext h)
      simp only [evalSlots,hi,hiv,ite_false]
      dsimp only [a]
      rw [install_other _ _ _ _ (by
        intro j h
        have hv:=congrArg (fun i : Fin 28=>i.val) h
        have hj:=j.isLt
        change j.val=7+i.val at hv
        omega)]
      simp only [input]
      split_ifs <;> first | rfl | omega)
  have whole:=ClockJoin.join first last _ _ _ _ _ ha hb
  exact ⟨_,whole,(install_slot evalSlots eval_injective a evaluated 19).trans evaluatedValue⟩

end
end NearCubicWires.RepairSource.RecoveryCaseOneEvaluation
