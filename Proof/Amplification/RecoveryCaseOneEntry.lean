import Proof.Amplification.RecoveryCaseOneEntryPair
import Proof.MachineModel.UInputFields

/-! One ordinary external word supplies the original hierarchy input and
address. Its unframing, field loading, reconstruction and returns are paid. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneEntry
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fieldSlots (i : Fin 10) : Fin 14 := i.castAdd 4
def pairSlots : Fin 6→Fin 14 := ![3,5,10,11,12,13]
theorem field_injective : Function.Injective fieldSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 14=>i.val) h)
theorem pair_injective : Function.Injective pairSlots := by decide
def first := RecoveryFocus.machine fieldSlots UInputFields.machine
def last := RecoveryFocus.machine pairSlots RecoveryCaseOneEntryPair.machine
def machine := Composition.machine first last
def word (x bound address : List Bool) := VerifierInputFields.source x bound address []
def input (raw : List Bool) : Fin 14→List Bool :=
  Fin.addCases (m:=10) (n:=4) (motive:=fun _=>List Bool) (UInputFields.input raw) (fun _=>[])
def budget (x bound address : List Bool) := 12*(word x bound address).length+5+1+RecoveryCaseOneEntryPair.budget x bound

theorem input_lookup (raw : List Bool) (i : Fin 14) : input raw i=if i.val=0 then frame raw else [] := by
  refine Fin.addCases (m:=10) (n:=4) (fun j=>?_) (fun j=>?_) i
  · simp only [input,Fin.addCases_left,UInputFields.input,Fin.val_castAdd]
    rfl
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem ready (x bound address : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget x bound address) (input (word x bound address)) out ∧
      out 10=frame x++frame bound ∧ out 7=frame address := by
  let raw:=word x bound address
  obtain ⟨g,_hg,hfields⟩ := UInputFields.entry_ready x bound address []
  let a:=install fieldSlots (input raw) (UInputFields.output raw x bound address g)
  have ha:=hfields.focus fieldSlots field_injective (input raw) (by
    intro i; simp only [input,fieldSlots,Fin.addCases_left]; rfl)
  have a3 : a 3=frame x := install_slot fieldSlots field_injective _ _ 3
  have a5 : a 5=frame bound := install_slot fieldSlots field_injective _ _ 5
  have a7 : a 7=frame address := install_slot fieldSlots field_injective _ _ 7
  have fresh (i : Fin 14) (hi : (10 : Nat)≤(i : Fin 14).val) : a i=[] := by
    dsimp only [a]
    rw [install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg (fun i : Fin 14=>i.val) h
      have hj:=j.isLt
      change j.val=i.val at hv
      omega),input_lookup,if_neg (by omega)]
  obtain ⟨paired,hpaired,pairedValue⟩ := RecoveryCaseOneEntryPair.ready x bound
  have hb:=hpaired.focus pairSlots pair_injective a (by
    intro i; fin_cases i
    · exact a3
    · exact a5
    · exact fresh 10 (by decide)
    · exact fresh 11 (by decide)
    · exact fresh 12 (by decide)
    · exact fresh 13 (by decide))
  have whole:=ClockJoin.join first last _ _ _ _ _ ha hb
  refine ⟨_,whole,(install_slot pairSlots pair_injective a paired 2).trans pairedValue,?_⟩
  exact (install_other pairSlots a paired 7 (by decide)).trans a7

end
end NearCubicWires.RepairSource.RecoveryCaseOneEntry
