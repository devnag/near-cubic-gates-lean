import Proof.PCP.ProjectionDimensionPolynomial
import Proof.PCP.ProjectionDimensionPowerBounds

/-! Raw polynomial workspace production from a measured unary byte mass.
Only template production and the fixed unary power loop are executed; the
binary conversion of the dimension producer is unnecessary here. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerCapacity.Power
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization DimensionPolynomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (D C : ℕ) := Composition.machine (templateProgram D) (powerProgram D C)
def budget (D C n : ℕ) := 2*n+9+DimensionPower.cost C (n+1) D
def outputSlot (D : ℕ) : Fin (tapes D) := binarySlots D 0

theorem capacity_run (D C n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine D C) (budget D C n) (input D n) out ∧
      out ⟨0,by simp [tapes]⟩=List.replicate n true ∧
      out (outputSlot D)=List.replicate (C*(n+1)^D) true := by
  let middle := install (templateSlots D) (input D n) (DimensionTemplate.output true n)
  have ht := (DimensionTemplate.ready true n).focus (templateSlots D) (template_injective D) (input D n)
    (by intro i; fin_cases i <;> rfl)
  change ClockJoin.ReadyRun (templateProgram D) (2*n+8) (input D n) middle at ht
  have middle_source : middle ⟨0,by simp [tapes]⟩=List.replicate n true := by
    change install (templateSlots D) _ _ (templateSlots D 0)=_
    rw [install_slot _ (template_injective D)]
    rfl
  have middle_template : middle (powerSlots D ⟨0,by simp [DimensionPower.tapes]⟩)=UnaryTemplate.tape (n+1) := by
    change install (templateSlots D) _ _ (templateSlots D 1)=_
    rw [install_slot _ (template_injective D)]
    rfl
  have middle_blank (i : Fin (tapes D)) (hi : 3 ≤ i.val) : middle i=[] := by
    dsimp only [middle]
    rw [install_other _ _ _ _ (by
      intro j he; have hv := congrArg Fin.val he; dsimp [templateSlots] at hv; omega)]
    simp [input,show i.val≠0 by omega]
  obtain ⟨powerOut,hp,hpt,hpv⟩ := DimensionPower.power_run D C (n+1)
  have hpower := hp.focus (powerSlots D) (power_injective D) middle (by
    intro i
    by_cases hi : i.val=0
    · have he : i=⟨0,by simp [DimensionPower.tapes]⟩ := Fin.ext hi
      subst i
      exact middle_template
    · rw [DimensionPower.input,if_neg hi]
      exact middle_blank _ (by simp [powerSlots,hi]; omega))
  let afterPower := install (powerSlots D) middle powerOut
  change ClockJoin.ReadyRun (powerProgram D C) (DimensionPower.cost C (n+1) D) middle afterPower at hpower
  have power_source : afterPower ⟨0,by simp [tapes]⟩=List.replicate n true := by
    dsimp only [afterPower]
    rw [install_other _ _ _ _ (by
      intro i he; have hv := congrArg Fin.val he
      dsimp [powerSlots] at hv; split_ifs at hv; dsimp at hv; omega)]
    exact middle_source
  have power_value : afterPower (binarySlots D 0)=List.replicate (value D C n) true := by
    have he : binarySlots D 0=powerSlots D (DimensionPower.valueSlot D D le_rfl) := by
      apply Fin.ext
      simp [binarySlots,powerSlots,DimensionPower.valueSlot]
      omega
    rw [he]
    change install (powerSlots D) middle powerOut _=_
    rw [install_slot _ (power_injective D)]
    exact hpv
  exact ⟨afterPower,ClockJoin.join _ _ _ _ _ _ _ ht hpower,power_source,power_value⟩

end NearCubicWires.RepairOrdinary.PCPSerializerCapacity.Power
