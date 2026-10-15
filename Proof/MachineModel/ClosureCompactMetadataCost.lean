import Proof.MachineModel.ClosureCompactMetadata
import Proof.CaseAnalysis.RowsCapacityBudget

/-! Cost of the executed metadata composition. The digit-enumeration
factor occurs once; there is no residual-table factor in preparation. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactMetadata
open RepairOrdinary ExtIncidence

theorem setup_bound (B n N b D Q w X : Nat)
    (hB : B≤X) (hn : n≤X) (hN : N≤X) (hb : b≤X) (hD : D≤X) (hQ : Q≤X) (_hw : w≤X) :
    budget6 B n N b D Q w ≤ 2^25*(X+1)^4 := by
  calc
    _ ≤ budget6 X X X X X X X := by
      simp only [budget6,budget5,budget4,budget3,budget2,budget1,
        CompactSize.budget,CompactSize.firstCost,CompactSize.value,
        RowCommonResources.budget,RowCommonTupleDimensions.budget,NativeFieldWidth.budget,
        RowCommonAllocation.budget,RowCommonAllocation.value,WilliamsUnaryProduct.budget,outer,p]
      gcongr
    _ ≤ 2^25*(X+1)^4 := by
      simp only [budget6,budget5,budget4,budget3,budget2,budget1,
        CompactSize.budget,CompactSize.firstCost,CompactSize.value,
        RowCommonResources.budget,RowCommonTupleDimensions.budget,NativeFieldWidth.budget,
        RowCommonAllocation.budget,RowCommonAllocation.value,WilliamsUnaryProduct.budget,outer,p]
      nlinarith [sq_nonneg (X : Int)]

theorem scale_bound (B n N b D Q w X : Nat)
    (hB : B≤X) (hn : n≤X) (hN : N≤X) (hb : b≤X) (hD : D≤X) (hQ : Q≤X) (hw : w≤X) :
    CloseoutRowsPreparationBounds.scale n (p b D Q) (F B n N b D Q) w N Q+1 ≤
      2^19*(X+1)^4 := by
  unfold CloseoutRowsPreparationBounds.scale F p outer CompactSize.value RowCommonAllocation.value
  calc
    _ ≤ X+(X*(X*X)+X)+(((X*X+1)*((X+(X+1)*(X+1)+X+1)*256))*64+
      (X*(X*X)+X)*16+64)+X+X+X+1+1 := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg (X : Int)]

theorem parameter_bound (n p F w N Q X : Nat)
    (hn : n≤X) (hp : p≤X) (hF : F≤X) (hw : w≤X) (hN : N≤X) (hQ : Q≤X) :
    NativeCapacityParameters.budget n p F w N Q ≤ 256*(X+1)^2 := by
  unfold NativeCapacityParameters.budget WilliamsUnaryProduct.budget
  calc
    _ ≤ NativeCapacityParameters.budget X X X X X X := by
      unfold NativeCapacityParameters.budget WilliamsUnaryProduct.budget
      gcongr
    _ ≤ _ := by unfold NativeCapacityParameters.budget WilliamsUnaryProduct.budget; nlinarith

theorem budget_bound (B n N b D Q w X : Nat)
    (hB : B≤X) (hn : n≤X) (hN : N≤X) (hb : b≤X) (hD : D≤X) (hQ : Q≤X) (hw : w≤X) :
    budget B n N b D Q w ≤ 2^118*(X+1)^22*2^(w*(Q+1)) := by
  let S := CloseoutRowsPreparationBounds.scale n (p b D Q) (F B n N b D Q) w N Q
  let E := 2^(w*(Q+1))
  let Z := (X+1)^22
  have hE : 1 ≤ E := Nat.one_le_two_pow
  have hZ : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have hXZ : X+1 ≤ Z := Nat.le_self_pow (by decide) _
  have h4 : (X+1)^4 ≤ Z := Nat.pow_le_pow_right (by omega) (by decide)
  have h8 : (X+1)^8 ≤ Z := Nat.pow_le_pow_right (by omega) (by decide)
  have hscale : S+1 ≤ 2^19*(X+1)^4 := scale_bound B n N b D Q w X hB hn hN hb hD hQ hw
  have hp := parameter_bound n (p b D Q) (F B n N b D Q) w N Q S
    (by unfold S CloseoutRowsPreparationBounds.scale; omega)
    (by unfold S CloseoutRowsPreparationBounds.scale; omega)
    (by unfold S CloseoutRowsPreparationBounds.scale; omega)
    (by unfold S CloseoutRowsPreparationBounds.scale; omega)
    (by unfold S CloseoutRowsPreparationBounds.scale; omega)
    (by unfold S CloseoutRowsPreparationBounds.scale; omega)
  have hparams : NativeCapacityParameters.budget n (p b D Q) (F B n N b D Q) w N Q ≤ 2^46*E*Z := by
    calc
      _ ≤ 256*(2^19*(X+1)^4)^2 := hp.trans (by gcongr)
      _ = 2^46*(X+1)^8 := by ring
      _ ≤ 2^46*E*Z := by nlinarith [Nat.mul_le_mul_left (2^46*Z) hE]
  have hR : w*(Q+1)+1 ≤ (X+1)^2 := by nlinarith [Nat.mul_le_mul hw (Nat.add_le_add_right hQ 1)]
  have hdrv : CloseoutRowsCapacityDriver.budget S (w*(Q+1)) ≤ 2^115*E*Z := by
    calc
      _ ≤ 1000000*E*(S+1)^5*(w*(Q+1)+1) := CloseoutRowsCapacityBudget.driver_bound S _
      _ ≤ 2^20*E*(2^19*(X+1)^4)^5*(X+1)^2 := by gcongr; norm_num
      _ = 2^115*E*Z := by dsimp [Z]; ring
  have hsetup : budget6 B n N b D Q w ≤ 2^25*E*Z := by
    have h := setup_bound B n N b D Q w X hB hn hN hb hD hQ hw
    nlinarith [Nat.mul_le_mul_left (2^25*Z) hE]
  have hshort : NativeShort.budget n w Q ≤ 128*E*Z := by
    unfold NativeShort.budget
    nlinarith [Nat.mul_le_mul_left Z hE]
  change budget6 B n N b D Q w+1+
    (NativeCapacityParameters.budget n (p b D Q) (F B n N b D Q) w N Q+1+
      CloseoutRowsCapacityDriver.budget S (w*(Q+1)))+1+NativeShort.budget n w Q ≤ _
  change _ ≤ 2^118*Z*E
  nlinarith

end NearCubicWires.P1Closure.CompactMetadata
