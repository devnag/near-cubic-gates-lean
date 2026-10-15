import Proof.CaseAnalysis.CaseOneAmplifierBound
import Proof.PCP.PCPSerializerCapacityBounds
import Proof.Amplification.RecoveryPrefixColdBudget

/-! The whole original Case1 formula constructor and canonical proof search
have a sufficient C.12 envelope in their actual serialized input/output sizes.
This includes scalar production, every original row, balanced serialization,
request copies, resets and the existing cold oracle search. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem dimension_budget (n M : Nat) (hn : n+1 ≤ M) :
    RecoveryProjectionDimension.budget n.bits ≤ 64*M^2 := by
  have hb : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hM : 1 ≤ M := by omega
  have hMM : M ≤ M^2 := Nat.le_self_pow (by decide) _
  have h1 : 1 ≤ M^2 := Nat.one_le_pow _ _ hM
  simp only [RecoveryProjectionDimension.budget,Unary.budget,
    CanonicalPositiveOutput.nat_bits_value]
  have hprod : (n+1)*(n.bits.length+1) ≤ M^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hn (by omega : n.bits.length+1 ≤ M)
  nlinarith

private theorem scalar_budget (R Q M : Nat) (hRQ : R+Q+1 ≤ M)
    (ht : 2^R+1 ≤ M) :
    RecoveryPCPFormulaResumeColdScalars.budget R.bits Q.bits ≤ 1000000000000*M^5 := by
  have hM : 1 ≤ M := by omega
  have hR : R+1 ≤ M := by omega
  have hQ : Q+1 ≤ M := by omega
  have dR := dimension_budget R M hR
  have dQ := dimension_budget Q M hQ
  have p4 := (PCPSerializerCapacity.budget_bound 4 1048576 R).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR 5))
  have p2 := (PCPSerializerCapacity.budget_bound 2 536870912 (R+Q)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hRQ 3))
  norm_num [PCPSerializerCapacity.coefficient] at p4 p2
  unfold PCPSerializerCapacity.budget at p4 p2
  have h1 : 1 ≤ M^5 := Nat.one_le_pow _ _ hM
  have hm : M ≤ M^5 := Nat.le_self_pow (by decide) _
  have h2 : M^2 ≤ M^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : M^3 ≤ M^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hprod : 2^R*(R+1) ≤ M^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : 2^R ≤ M) hR
  unfold RecoveryPCPFormulaResumeColdScalars.budget
    RecoveryPCPFormulaResumeCapacity.budget RecoveryProjectionCapacity.budget
    RecoveryPCPFormulaResumeCountPair.budget RecoveryPCPFormulaResumeCountCold.budget
    RecoveryPCPFormulaResumeCount.budget
  simp only [CanonicalPositiveOutput.nat_bits_value]
  nlinarith [Nat.sub_le (2^R) 1]

theorem prefix_budget_bound (R Q count M : Nat) (hRQ : R+Q+1 ≤ M)
    (ht : 2^R+1 ≤ M) (hc : count ≤ M) :
    RecoveryPCPFormulaResumePrefix.budget (RecoverySourceClauseLoad.uniformBudget Q R)
      R Q count ≤ 30000000000*M^7 := by
  have hM : 1 ≤ M := by omega
  have hR : R+1 ≤ M := by omega
  have hQ : Q ≤ M := by omega
  have power_le (a b : Nat) (hab : a ≤ b) : M^a ≤ M^b :=
    Nat.pow_le_pow_right (by omega) hab
  have hm6 : M ≤ M^6 := Nat.le_self_pow (by decide) _
  have h16 : 1 ≤ M^6 := Nat.one_le_pow _ _ hM
  have hrewind : RecoveryProjectionRowsRewind.budget R Q ≤ 10000000*M^6 := by
    unfold RecoveryProjectionRowsRewind.budget RecoveryProjectionRowsRewind.batchBudget
      RecoveryProjectionRows.capacity
    calc
      _ ≤ 2*(M*(M*(4*(1048576*M^4)+11)+8)+3+2)+2 := by gcongr; omega
      _ ≤ _ := by nlinarith [power_le 2 6 (by decide)]
  have hcap : RecoverySourceClauseLoad.uniformBudget Q R ≤ 536870912*M^2 := by
    unfold RecoverySourceClauseLoad.uniformBudget
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : Q+R+1 ≤ M) 2)
  have hrow : RecoveryPCPFormulaResumeRow.budget
      (RecoverySourceClauseLoad.uniformBudget Q R) R Q count ≤ 3000000000*M^6 := by
    unfold RecoveryPCPFormulaResumeRow.budget
    calc
      _ ≤ 10000000*M^6+1+(M*(5*(536870912*M^2)+12)+3) := by gcongr
      _ ≤ _ := by nlinarith [power_le 3 6 (by decide)]
  have hreusable : RecoveryPCPFormulaResumeRowReusable.rowBudget
      (RecoverySourceClauseLoad.uniformBudget Q R) R Q count ≤ 8000000000*M^6 := by
    unfold RecoveryPCPFormulaResumeRowReusable.rowBudget
    nlinarith [power_le 2 6 (by decide)]
  have htaut := (RecoveryTseitinTautology.Cold.budget_bound (2^R)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht 3))
  unfold RecoveryPCPFormulaResumePrefix.budget RecoveryPCPFormulaResumeRows.budget
    RecoveryPCPFormulaResumeRows.bodyBudget
  have hloop := Nat.mul_le_mul (by omega : 2^R-1 ≤ M)
    (by omega : RecoveryPCPFormulaResumeRowReusable.rowBudget
      (RecoverySourceClauseLoad.uniformBudget Q R) R Q count+4*R+3+3 ≤
        8000000000*M^6+4*M+3+3)
  calc
    _ ≤ 4294967296*M^3+1+M*(8000000000*M^6+4*M+3+3)+4+8000000000*M^6 := by
      omega
    _ ≤ _ := by
      nlinarith [power_le 3 7 (by decide),power_le 6 7 (by decide),
        power_le 2 7 (by decide),power_le 1 7 (by decide),power_le 0 7 (by decide)]

theorem formula_search_budget (R Q count : Nat) (words : List (List Bool)) (payload : Nat) :
    RecoveryPCPFormulaResumeProof.budget R Q count words payload ≤
      10000000000000000 *
        (R+Q+2^R+count+(FieldList.stream words).length+payload.bits.length+2)^12 := by
  let M := R+Q+2^R+count+(FieldList.stream words).length+payload.bits.length+2
  have hpow : 0 < 2^R := Nat.two_pow_pos R
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hR : R+1 ≤ M := by dsimp [M]; omega
  have hQ : Q ≤ M := by dsimp [M]; omega
  have hRQ : R+Q+1 ≤ M := by dsimp [M]; omega
  have ht : 2^R+1 ≤ M := by dsimp [M]; omega
  have hc : count ≤ M := by dsimp [M]; omega
  have hw : (FieldList.stream words).length+1 ≤ M := by dsimp [M]; omega
  have hp : payload.bits.length ≤ M := by dsimp [M]; omega
  have power_le (a b : Nat) (hab : a ≤ b) : M^a ≤ M^b :=
    Nat.pow_le_pow_right (by omega) hab
  have hprefix := prefix_budget_bound R Q count M hRQ ht hc
  have hserial := RecoveryFormulaFrame.budget_bound words
  have hserialM : RecoveryFormulaFrame.rawBudget words ≤ 1000000000064*M^12 :=
    hserial.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 12))
  have hscalars := scalar_budget R Q M hRQ ht
  have hsearch := RecoveryPrefixCold.fixed_budget_bound payload (2^R)
  have hradius : RecoveryPrefixCold.radius payload (2^R) ≤ 8*M := by
    unfold RecoveryPrefixCold.radius
    omega
  have hsearchM := hsearch.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hradius 3))
  change RecoveryPCPFormulaResumeProof.budget R Q count words payload ≤ 10000000000000000*M^12
  unfold RecoveryPCPFormulaResumeProof.budget RecoveryPCPFormulaResumeSearchRequest.budget
    RecoveryPCPFormulaResumeSearch.readyBudget RecoveryPCPFormulaResumeSearch.budget
    RecoveryPCPFormulaResumeSearchCount.budget RecoveryPCPFormulaResumeSerialize.budget
    RecoveryPCPFormulaResumePrefix.framedBudget RecoveryPCPFormulaResumePrefix.rawBudget
    RecoveryPCPFormulaResumeSearchPair.framedBudget RecoveryPCPFormulaResumeSearchPair.budget
  simp only [List.length_append,frame_length,List.length_replicate]
  nlinarith [power_le 0 12 (by decide),power_le 1 12 (by decide),
    power_le 3 12 (by decide),power_le 5 12 (by decide),power_le 7 12 (by decide),
    Nat.sub_le (2^R) 1]

end NearCubicWires.RepairSource.CloseoutCaseOne
