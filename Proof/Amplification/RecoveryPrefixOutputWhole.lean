import Proof.Amplification.RecoveryPrefixOutput

/-! Whole final prefix extraction, including physical production of the
copy length from its actual terminated unary template. The caller first seals the
retained sentinel driver with its missing final false cell. The existing power producer
and bounded copier are joined; the high sentinel is absent from the output. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixOutput
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def powerSlots : Fin (DimensionPower.tapes 1)→Fin 8 := ![1,2,3,4,5]
def copySlots : Fin 4→Fin 8 := ![0,6,4,7]
theorem power_injective : Function.Injective powerSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide

def input (source : List Bool) (total : Nat) : Fin 8→List Bool :=
  ![source,UnaryTemplate.tape total,[],[],[],[],[],[]]
noncomputable def powerMachine := RecoveryFocus.machine powerSlots (DimensionPower.machine 1 2)
noncomputable def copyMachine := RecoveryFocus.machine copySlots RecoveryBoundedWordCopy.machine
noncomputable def machine := Composition.machine powerMachine copyMachine
def budget (total : Nat) := DimensionPower.cost 2 total 1+1+(4*total+8)

theorem output_ready (xs : List Bool) (cap : Nat) : ∃ out,
    ClockJoin.ReadyRun machine (budget xs.length)
      (input (ZeroPadding.pad cap (frame (xs++[false,true]))) xs.length) out ∧
    out 0=ZeroPadding.pad cap (frame (xs++[false,true])) ∧
    out 1=UnaryTemplate.tape xs.length ∧ out 6=frame xs := by
  classical
  let source := ZeroPadding.pad cap (frame (xs++[false,true]))
  obtain ⟨powerOut,hpower,hdriver,hcount⟩ := DimensionPower.power_run 1 2 xs.length
  have hp := hpower.focus powerSlots power_injective (input source xs.length) (by
    intro i
    fin_cases i <;> rfl)
  let middle := install powerSlots (input source xs.length) powerOut
  have hsource : middle 0=source := by
    dsimp only [middle]
    rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
    rfl
  have htotal : middle 1=UnaryTemplate.tape xs.length := by
    change install powerSlots _ _ (powerSlots ⟨0,by decide⟩)=_
    rw [install_slot _ power_injective]
    exact hdriver
  have hcount' : middle 4=List.replicate (2*xs.length) true := by
    change install powerSlots _ _ (powerSlots (DimensionPower.valueSlot 1 1 (by omega)))=_
    rw [install_slot _ power_injective]
    simpa only [pow_one] using hcount
  have hblank (i : Fin 8) (hi : 6 ≤ i.val) : middle i=[] := by
    dsimp only [middle]
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg (fun k : Fin 8=>k.val) he
      have hj : (powerSlots j).val<6 := by fin_cases j <;> decide
      omega)]
    fin_cases i <;> simp_all [input]
  have hc := (copy_ready xs cap 0).focus copySlots copy_injective middle (by
    intro i
    fin_cases i
    · exact hsource
    · exact hblank 6 (by decide)
    · exact hcount'
    · exact hblank 7 (by decide))
  have whole := ClockJoin.join _ _ _ _ _ _ _ hp hc
  refine ⟨_,whole,?_,?_,?_⟩
  · change install copySlots middle _ (copySlots 0)=_
    rw [install_slot _ copy_injective]
    rfl
  · rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
    exact htotal
  · change install copySlots middle _ (copySlots 1)=_
    rw [install_slot _ copy_injective]
    rfl

end NearCubicWires.RepairSource.RecoveryPrefixOutput
