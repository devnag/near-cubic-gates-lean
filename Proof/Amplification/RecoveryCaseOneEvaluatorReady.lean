import Proof.Amplification.RecoveryCaseOneEvaluatorReset

/-! One fixed evaluator consumes the physically supplied full table and
address and returns the canonical framed Boolean language output. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneEvaluator
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def resetSlots (i : Fin 19) : Fin 21 := i.castAdd 2
def boolSlots : Fin 3→Fin 21 := ![17,19,20]
theorem reset_injective : Function.Injective resetSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 21=>i.val) h)
theorem bool_injective : Function.Injective boolSlots := by decide
def first := RecoveryFocus.machine resetSlots resetMachine
def last := RecoveryFocus.machine boolSlots RecoveryCaseOneBooleanOutput.machine
def machine := Composition.machine first last
def input (word : List Bool) : Fin 21→List Bool :=
  Fin.addCases (m:=19) (n:=2) (motive:=fun _=>List Bool) (resetInput word) (fun _=>[])
def budget {n : Nat} (f : BoolFunction n) (address : BitInput n) := resetBudget f address+1+8

theorem input_lookup (word : List Bool) (i : Fin 21) : input word i=if i.val=0 then frame word else [] := by
  refine Fin.addCases (m:=19) (n:=2) (fun j=>?_) (fun j=>?_) i
  · simp only [input,Fin.addCases_left,Fin.val_castAdd,reset_input]
    rfl
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem ready {n : Nat} (f : BoolFunction n) (address : BitInput n) :
    ∃ out,ClockJoin.ReadyRun machine (budget f address) (input (GeneratedAmplifier.payload f address)) out ∧
      out 19=frame (f address).toNat.bits := by
  obtain ⟨raw,hraw,rawValue⟩ := reset_ready f address
  let a:=install resetSlots (input (GeneratedAmplifier.payload f address)) raw
  have ha:=hraw.focus resetSlots reset_injective (input (GeneratedAmplifier.payload f address)) (by
    intro i; simp only [input,resetSlots,Fin.addCases_left])
  obtain ⟨encoded,hencoded,encodedValue⟩ := RecoveryCaseOneBooleanOutput.ready (f address)
  have hfresh (i : Fin 21) (hi : (19 : Nat)≤(i : Fin 21).val) : a i=[] := by
    dsimp only [a]
    rw [install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg (fun i : Fin 21=>i.val) h
      have hj:=j.isLt
      change j.val=i.val at hv
      omega),input_lookup,if_neg (by omega)]
  have hb:=hencoded.focus boolSlots bool_injective a (by
    intro i; fin_cases i
    · exact (install_slot resetSlots reset_injective _ raw 17).trans rawValue
    · exact hfresh 19 (by decide)
    · exact hfresh 20 (by decide))
  have whole:=ClockJoin.join first last _ _ _ _ _ ha hb
  exact ⟨_,whole,(install_slot boolSlots bool_injective a encoded 1).trans encodedValue⟩

end
end NearCubicWires.RepairSource.RecoveryCaseOneEvaluator
