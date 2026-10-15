import Proof.PCP.ProjectionDimensionPolynomial

/-! The existing unary polynomial prefix stops before binary conversion.
This is essential for a driver containing a table-sized factor: producing
the raw value is linear in that value and never squares it for a header. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPower
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
open DimensionPolynomial (tapes templateSlots powerSlots template_injective power_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (D C : ℕ):=Composition.machine
  (DimensionPolynomial.templateProgram D) (DimensionPolynomial.powerProgram D C)
def budget (D C n : ℕ):=2*n+8+1+DimensionPower.cost C (n+1) D
def valueSlot (D : ℕ) : Fin (tapes D):=powerSlots D (DimensionPower.valueSlot D D le_rfl)

theorem ready (D C n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine D C) (budget D C n) (DimensionPolynomial.input D n) out ∧
      out ⟨0,by simp [tapes]⟩=List.replicate n true ∧
      out (valueSlot D)=List.replicate (C*(n+1)^D) true := by
  let middle:=install (templateSlots D) (DimensionPolynomial.input D n) (DimensionTemplate.output true n)
  have ht:=(DimensionTemplate.ready true n).focus (templateSlots D) (template_injective D)
    (DimensionPolynomial.input D n) (by intro i;fin_cases i <;>rfl)
  change ClockJoin.ReadyRun (DimensionPolynomial.templateProgram D) (2*n+8)
    (DimensionPolynomial.input D n) middle at ht
  have hsource : middle ⟨0,by simp [tapes]⟩=List.replicate n true := by
    change install (templateSlots D) _ _ (templateSlots D 0)=_
    rw [install_slot _ (template_injective D)]
    rfl
  have htemplate : middle (powerSlots D ⟨0,by simp [DimensionPower.tapes]⟩)=UnaryTemplate.tape (n+1) := by
    change install (templateSlots D) _ _ (templateSlots D 1)=_
    rw [install_slot _ (template_injective D)]
    rfl
  have hblank (i : Fin (tapes D)) (hi : 3 ≤ i.val) : middle i=[] := by
    dsimp only [middle]
    rw [install_other _ _ _ _ (by
      intro j he;have hv:=congrArg Fin.val he;dsimp [templateSlots] at hv;omega)]
    simp [DimensionPolynomial.input,show i.val≠0 by omega]
  obtain ⟨powerOut,hp,_hpt,hpv⟩:=DimensionPower.power_run D C (n+1)
  have hpower:=hp.focus (powerSlots D) (power_injective D) middle (by
    intro i
    by_cases hi : i.val=0
    · have he : i=⟨0,by simp [DimensionPower.tapes]⟩:=Fin.ext hi
      subst i
      exact htemplate
    · rw [DimensionPower.input,if_neg hi]
      exact hblank _ (by simp [powerSlots,hi];omega))
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ ht hpower,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro i he;have hv:=congrArg Fin.val he
      dsimp [powerSlots] at hv;split_ifs at hv;dsimp at hv;omega)]
    exact hsource
  · rw [valueSlot,install_slot _ (power_injective D)]
    exact hpv

theorem cost_linear (D C n j : ℕ) (hj : j≤D) (hn : 1≤n) :
    DimensionPower.cost C n j ≤ 2*C+2+j*(10*C*n^D+7) := by
  induction j with
  | zero => simp [DimensionPower.cost]
  | succ j ih =>
    have hprev:=ih (by omega)
    have hp : n^j≤n^D:=Nat.pow_le_pow_right (by omega) (by omega)
    have hnext : n^(j+1)≤n^D:=Nat.pow_le_pow_right (by omega) hj
    have hpC:=Nat.mul_le_mul_left C hp
    have hnC:=Nat.mul_le_mul_left C hnext
    rw [pow_succ] at hnC
    simp only [DimensionPower.cost,WilliamsUnaryProduct.budget]
    nlinarith

theorem budget_linear (D C n : ℕ) (hD : 1≤D) (hC : 1≤C) :
    budget D C n ≤ (10*D+20)*(C*(n+1)^D+1) := by
  have hc:=cost_linear D C (n+1) D le_rfl (by omega)
  have hp : n+1≤(n+1)^D:=Nat.le_self_pow (by omega) _
  have hpos : 1≤(n+1)^D:=Nat.one_le_pow _ _ (by omega)
  have hCn : n+1≤C*(n+1)^D := hp.trans (by nlinarith)
  have hCout : C≤C*(n+1)^D := by nlinarith
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverPower
