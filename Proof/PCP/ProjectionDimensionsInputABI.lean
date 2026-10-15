import Proof.Hierarchy.HierarchyFramedInput

namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionsFromInput
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clock_input_eq (bits : List Bool) : ClockFromInput.input bits=
    (fun i : Fin 34 => if i.val=12 then frame bits else []) := by
  funext i
  fin_cases i <;> rfl

theorem input_eq (p q : ℕ) (bits : List Bool) : input p q bits=
    (fun i : Fin (tapes p q) => if i.val=12 then frame bits else []) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [input,Fin.addCases_left,Fin.val_castAdd]
    rw [clock_input_eq]
    rfl
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem rawR_val (p q : ℕ) : (rawR p q).val=51+2*p := by
  simp [rawR,dimensionSlots,DimensionProducer.rawR,DimensionProducer.old,DimensionWidth.rawSlot,
    DimensionWidth.binarySlots,DimensionWidth.fresh,DimensionWidth.base,DimensionPolynomial.tapes]
  omega
theorem bitsR_val (p q : ℕ) : (bitsR p q).val=55+2*p := by
  simp [bitsR,dimensionSlots,DimensionProducer.bitsR,DimensionProducer.old,DimensionWidth.bitsSlot,
    DimensionWidth.binarySlots,DimensionWidth.fresh,DimensionWidth.base,DimensionPolynomial.tapes]
  omega
theorem rawQ_val (p q : ℕ) : (rawQ p q).val=64+2*p+2*q := by
  simp [rawQ,dimensionSlots,DimensionProducer.rawQ,DimensionProducer.querySlots,
    DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots,DimensionWidth.tapes,DimensionWidth.base,DimensionPolynomial.tapes]
  omega
theorem bitsQ_val (p q : ℕ) : (bitsQ p q).val=68+2*p+2*q := by
  simp [bitsQ,dimensionSlots,DimensionProducer.bitsQ,DimensionProducer.querySlots,
    DimensionPolynomial.bitsSlot,DimensionPolynomial.binarySlots,DimensionWidth.tapes,DimensionWidth.base,DimensionPolynomial.tapes]
  omega

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionsFromInput
