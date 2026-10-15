import Proof.CaseAnalysis.CaseOneFormulaBound
import Proof.MachineModel.OrdinarySelectiveWorkspace

/-! The actual original printer supplies its own serialized-width bound:
its output cursor starts at zero and finishes at the emitted stream length.
No separate clause-encoding size proof or alternative formula is required. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open RepairOrdinary LocalBitMultitape ProjectionNormalization SourceInterfaces
open CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem formula_stream_budget (p : RawProjectionPCP) (R Q : Nat)
    (hr : p.width ≤ R) (hq : p.queries ≤ Q) {n : Nat} (x : BitInput n) :
    (FieldList.stream (RecoveryPCPFormulaResume.words
      (compactProjectionPCP (p.normalized R Q hr hq)) x)).length ≤
        RecoveryPCPFormulaResumePrefix.rawBudget (RecoverySourceClauseLoad.uniformBudget Q R)
          R Q (Codec.clauses p).length := by
  obtain ⟨r,hrun,_ht,hh,hs⟩ := RecoveryPCPFormulaResumePrefix.raw_run p R Q hr hq x
    (RecoverySourceClauseLoad.uniformBudget Q R) (RecoveryProjectionRowsRewind.batchBudget R Q+2)
    (RecoveryPCPFormulaResumeRow.budget (RecoverySourceClauseLoad.uniformBudget Q R)
      R Q (Codec.clauses p).length) le_rfl le_rfl le_rfl
  have hhead := SelectiveReset.prefix_head (prefix_of_run _ _ _ r hrun).1 (276 : Fin 580)
  rw [hh] at hhead
  simp only [initialConfiguration,Nat.zero_add] at hhead
  exact hhead.trans hs

theorem formula_stream_bound (p : RawProjectionPCP) (R Q : Nat)
    (hr : p.width ≤ R) (hq : p.queries ≤ Q) {n : Nat} (x : BitInput n) :
    (FieldList.stream (RecoveryPCPFormulaResume.words
      (compactProjectionPCP (p.normalized R Q hr hq)) x)).length ≤
        30000000002*(R+Q+2^R+(Codec.clauses p).length+2)^7 := by
  let U := R+Q+2^R+(Codec.clauses p).length+2
  have ht : 0 < 2^R := Nat.two_pow_pos R
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hp := prefix_budget_bound R Q (Codec.clauses p).length U
    (by dsimp [U]; omega) (by dsimp [U]; omega) (by dsimp [U]; omega)
  have h1 : 1 ≤ U^7 := Nat.one_le_pow _ _ hU
  have h := formula_stream_budget p R Q hr hq x
  unfold RecoveryPCPFormulaResumePrefix.rawBudget at h
  change _ ≤ 30000000002*U^7
  omega

theorem formula_payload_bound {M : TimedDecisionMachine} {T : Nat→Nat}
    (pcp : ProjectionPCP M T) {n : Nat} (x : BitInput n) :
    (balancedCNFPayload (outerProofRecoveryFormula pcp x)).bits.length ≤
      3*((FieldList.stream (RecoveryPCPFormulaResume.words pcp x)).length+1)^5 := by
  have h := PCPSerializerMass.code_bits (RecoveryPCPFormulaResume.words pcp x)
  change (PCPTraversal.code (RecoveryPCPFormulaResume.words pcp x)).bits.length ≤ _ at h
  rw [RecoveryFormulaPayload.value_code _ _ (RecoveryPCPFormulaResume.values pcp x),
    ←PCPTraversal.stream_mass] at h
  exact h

def formulaCoefficient : Nat := 10000000000000000*(30000000003+3*30000000003^5)^12

theorem original_formula_search_bound (p : RawProjectionPCP) (R Q : Nat)
    (hr : p.width ≤ R) (hq : p.queries ≤ Q) {n : Nat} (x : BitInput n) :
    let pcp := compactProjectionPCP (p.normalized R Q hr hq)
    RecoveryPCPFormulaResumeProof.budget R Q (Codec.clauses p).length
      (RecoveryPCPFormulaResume.words pcp x) (balancedCNFPayload (outerProofRecoveryFormula pcp x)) ≤
        formulaCoefficient*((R+Q+2^R+(Codec.clauses p).length+2)^35)^12 := by
  let pcp := compactProjectionPCP (p.normalized R Q hr hq)
  let fields := RecoveryPCPFormulaResume.words pcp x
  let payload := balancedCNFPayload (outerProofRecoveryFormula pcp x)
  let U := R+Q+2^R+(Codec.clauses p).length+2
  let A : Nat := 30000000003
  have ht : 0 < 2^R := Nat.two_pow_pos R
  have hU : 1 ≤ U := by dsimp [U]; omega
  have h1 : 1 ≤ U^7 := Nat.one_le_pow _ _ hU
  have hs := formula_stream_bound p R Q hr hq x
  have hs1 : (FieldList.stream fields).length+1 ≤ A*U^7 := by
    change (FieldList.stream fields).length ≤ 30000000002*U^7 at hs
    dsimp only [A]
    omega
  have hp := (formula_payload_bound pcp x).trans
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs1 5))
  have hp' : payload.bits.length ≤ 3*A^5*U^35 := by
    simpa only [mul_pow,←pow_mul,Nat.mul_assoc] using hp
  have hu35 : U ≤ U^35 := Nat.le_self_pow (by decide) _
  have h735 : U^7 ≤ U^35 := Nat.pow_le_pow_right (by omega) (by decide)
  have hsize : R+Q+2^R+(Codec.clauses p).length+(FieldList.stream fields).length+
      payload.bits.length+2 ≤ (A+3*A^5)*U^35 := by
    have hs35 := hs1.trans (Nat.mul_le_mul_left A h735)
    have hUeq : R+Q+2^R+(Codec.clauses p).length+2=U := rfl
    have hs7 : (FieldList.stream fields).length ≤ (A-1)*U^7 := hs
    have hs35' := hs7.trans (Nat.mul_le_mul_left (A-1) h735)
    have hA : 1 ≤ A := by decide
    have hsub : (A-1)*U^35+U^35=A*U^35 := by
      rw [←Nat.succ_mul,Nat.succ_eq_add_one,Nat.sub_add_cancel hA]
    nlinarith
  have h := (formula_search_budget R Q (Codec.clauses p).length fields payload).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 12))
  rw [mul_pow,←Nat.mul_assoc] at h
  exact h

end NearCubicWires.RepairSource.CloseoutCaseOne
