import Proof.Amplification.RecoveryTseitinStream
import Proof.PCP.PCPSerializerCapacityPower
import Proof.PCP.ProjectionNormalizationDriverAtoms

/-! From the actual raw unary clause count, execute the existing polynomial
capacity producer and sentinel counter. The count, capacity and all scratch
are physical tapes; only the fixed polynomial coefficient enters control. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverCapacity (count : Nat) := 33554432*(count+1)^2
theorem driver_capacity (count : Nat) : uniformCapacity count≤driverCapacity count := by
  have hw : natBitLength count+1≤2*(count+1) := by
    unfold natBitLength
    have := Nat.log_le_self 2 count
    omega
  have hs := Nat.pow_le_pow_left hw 2
  have he : (2*(count+1))^2=4*(count+1)^2 := by ring
  rw [he] at hs
  unfold uniformCapacity driverCapacity
  omega

def powerSlots (i : Fin 18) : Fin 262 :=
  if i=0 then 242 else if i=7 then 3 else ⟨i.val+242,by have hi:=i.isLt; omega⟩
def countSlots : Fin 4→Fin 262 := ![242,260,241,261]
theorem power_injective : Function.Injective powerSlots := by
  intro i j he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> simp_all
theorem count_injective : Function.Injective countSlots := by decide
noncomputable def powerMachine := RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 2 33554432)
noncomputable def countMachine := RecoveryFocus.machine countSlots Counter.machine
noncomputable def driversMachine := Composition.machine powerMachine countMachine
def driversInput (count : Nat) : Fin 262→List Bool := fun i=>if i=242 then List.replicate count true else []
def driversBudget (count : Nat) := PCPSerializerCapacity.Power.budget 2 33554432 count+1+Counter.budget count

theorem drivers_run (count : Nat) : ∃ out,
    ClockJoin.ReadyRun driversMachine (driversBudget count) (driversInput count) out ∧
      out 3=List.replicate (driverCapacity count) true ∧
      out 241=CompareMachine.word count ∧ out 242=List.replicate count true ∧
      (∀ i : Fin 242,i≠3 → i≠241 → out (i.castAdd 20)=[]) := by
  obtain ⟨power,hp,p0,pc⟩ := PCPSerializerCapacity.Power.capacity_run 2 33554432 count
  let middle := install powerSlots (driversInput count) power
  have hfirst := hp.focus powerSlots power_injective (driversInput count) (by
    intro i
    fin_cases i <;> rfl)
  have m0 : middle 242=List.replicate count true :=
    (install_slot powerSlots power_injective _ power 0).trans p0
  have mc : middle 3=List.replicate (driverCapacity count) true :=
    (install_slot powerSlots power_injective _ power 7).trans pc
  have mother (i : Fin 262) (hi : i=241 ∨ i=260 ∨ i=261) : middle i=[] := by
    dsimp only [middle]
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      have hj:=j.isLt
      dsimp only [powerSlots] at hv
      rcases hi with hi|hi|hi <;> subst i <;> split_ifs at hv <;> dsimp at hv <;> omega)]
    rcases hi with hi|hi|hi <;> subst i <;> rfl
  obtain ⟨counter,hc,c0,cc⟩ := DriverAtoms.counter_run count
  have hlast := hc.focus countSlots count_injective middle (by
    intro i
    fin_cases i
    · exact m0
    · exact mother 260 (by simp)
    · exact mother 241 (by simp)
    · exact mother 261 (by simp))
  let out := install countSlots middle counter
  have hwhole := ClockJoin.join powerMachine countMachine _ _ _ _ _ hfirst hlast
  refine ⟨out,hwhole,?_,?_,?_,?_⟩
  · exact (install_other countSlots middle counter 3 (by decide)).trans mc
  · exact (install_slot countSlots count_injective middle counter 2).trans cc
  · exact (install_slot countSlots count_injective middle counter 0).trans c0
  · intro i h3 h241
    have hi:=i.isLt
    have hn3 : i.val≠3 := by intro he; exact h3 (Fin.ext he)
    have hn241 : i.val≠241 := by intro he; exact h241 (Fin.ext he)
    dsimp only [out]
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      fin_cases j <;> dsimp [countSlots] at hv <;> omega)]
    dsimp only [middle]
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      dsimp only [powerSlots,Fin.val_castAdd] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    simp only [driversInput]
    rw [if_neg (by intro he; have hv:=congrArg Fin.val he; change i.val=242 at hv; omega)]

end NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
