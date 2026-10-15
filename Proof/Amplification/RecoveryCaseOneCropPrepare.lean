import Proof.Amplification.RecoveryCaseOneGeneratedArity

/-! Retain the actual generated schema and target address while its arity
is physically decoded into the crop driver's unary template. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneCropPrepare
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def archiveSlots (i : Fin 4) : Fin 18 := i.castAdd 14
def aritySlots (i : Fin 14) : Fin 18 := if i=0 then 1 else ⟨3+i.val,by have hi:=i.isLt; omega⟩
theorem archive_injective : Function.Injective archiveSlots := by
  intro i j h; exact Fin.ext (congrArg (fun z : Fin 18=>z.val) h)
theorem arity_injective : Function.Injective aritySlots := by
  intro i j h
  have hv:=congrArg (fun z : Fin 18=>z.val) h
  apply Fin.ext
  dsimp only [aritySlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def first := RecoveryFocus.machine archiveSlots RecoveryCaseOneArchive.machine
def last := RecoveryFocus.machine aritySlots RecoveryCaseOneGeneratedArity.machine
def machine := Composition.machine first last
def input (schema address : List Bool) (i : Fin 18) :=
  if i.val=0 then frame schema else if i.val=17 then frame address else []
def budget (n : Nat) (tail : List Bool) :=
  RecoveryCaseOneArchive.budget (frame n.bits++tail)+1+RecoveryCaseOneGeneratedArity.budget n tail

theorem ready (n : Nat) (tail address : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget n tail) (input (frame n.bits++tail) address) out ∧
      out 0=frame (frame n.bits++tail) ∧ out 15=UnaryTemplate.tape n ∧ out 17=frame address := by
  let schema:=frame n.bits++tail
  obtain ⟨archived,harchived,original,archivedValue⟩:=RecoveryCaseOneArchive.archive_ready schema
  let a:=install archiveSlots (input schema address) archived
  have ha:=harchived.focus archiveSlots archive_injective (input schema address) (by
    intro i; fin_cases i <;> rfl)
  obtain ⟨parsed,hparsed,parsedValue⟩:=RecoveryCaseOneGeneratedArity.ready n tail
  have hb:=hparsed.focus aritySlots arity_injective a (by
    intro i
    rw [RecoveryCaseOneGeneratedArity.input_lookup]
    by_cases hi : i=0
    · subst i
      exact (install_slot archiveSlots archive_injective _ archived 1).trans archivedValue
    · have hiv : i.val≠0 := fun h=>hi (Fin.ext h)
      simp only [aritySlots,hi,hiv,ite_false]
      dsimp only [a]
      rw [install_other _ _ _ _ (by
        intro j h
        have hv:=congrArg (fun z : Fin 18=>z.val) h
        have hj:=j.isLt
        change j.val=3+i.val at hv
        omega)]
      have hiBound:=i.isLt
      simp only [input]
      split_ifs <;> first | rfl | omega)
  have whole:=ClockJoin.join first last _ _ _ _ _ ha hb
  refine ⟨_,whole,?_,(install_slot aritySlots arity_injective a parsed 12).trans parsedValue,?_⟩
  · rw [install_other aritySlots a parsed 0 (by decide)]
    exact (install_slot archiveSlots archive_injective _ archived 0).trans original
  · rw [install_other aritySlots a parsed 17 (by decide)]
    exact (install_other archiveSlots _ archived 17 (by decide)).trans rfl

end
end NearCubicWires.RepairSource.RecoveryCaseOneCropPrepare
