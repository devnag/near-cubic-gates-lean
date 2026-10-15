import Proof.CaseAnalysis.CaseOneStreamBound

/-! Apply C.12 slack at the final address: normalized queries are a fixed
polynomial of the actual core arity, and the existing deduplicated clause
count is cubic in those queries. The original formula, proof search and
amplifier all retain their checked physical budgets. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open RepairOrdinary ProjectionNormalization SourceInterfaces
open CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def dataCoefficient (C : Nat) := C+8*C^3+4
def dataExponent (D : Nat) := max 1 (3*D)
def sourceFormulaCoefficient (C : Nat) := formulaCoefficient*((dataCoefficient C)^35)^12
def sourceFormulaExponent (D : Nat) := dataExponent D*35*12

private theorem scaled_power_identity (A B V E a b : Nat) :
    A*((B*V^E)^a)^b=(A*(B^a)^b)*V^(E*a*b) := by
  simp only [mul_pow,←pow_mul]
  ring

theorem formula_data_bound (R Q count C D target : Nat) (hr : R ≤ target)
    (hq : Q ≤ C*(R+1)^D) (hc : count ≤ (2*Q)^3) :
    R+Q+2^R+count+2 ≤ dataCoefficient C*(2^target+1)^dataExponent D := by
  let V : Nat := 2^target+1
  let E := dataExponent D
  have hv : 1 ≤ V := Nat.le_add_left 1 _
  have hE : 1 ≤ E := Nat.le_max_left _ _
  have hDE : D ≤ E := by have h:=Nat.le_max_right 1 (3*D); dsimp [E,dataExponent]; omega
  have h3DE : D*3 ≤ E := by dsimp [E,dataExponent]; omega
  have hr1 : R+1 ≤ V := by
    have h := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=target))
    dsimp [V]
    omega
  have ht : 2^R ≤ V := (Nat.pow_le_pow_right (by decide) hr).trans (Nat.le_add_right _ 1)
  have hVE : V ≤ V^E := Nat.le_self_pow (by omega) _
  have h1 : 1 ≤ V^E := Nat.one_le_pow _ _ hv
  have hQD : Q ≤ C*V^D := hq.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hr1 D))
  have hQE := hQD.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) hDE))
  have hcD : count ≤ 8*C^3*V^(D*3) := by
    calc
      count ≤ (2*Q)^3 := hc
      _ ≤ (2*(C*V^D))^3 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hQD) 3
      _ = _ := by rw [mul_pow,mul_pow,←pow_mul]; ring
  have hcE := hcD.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h3DE))
  change _ ≤ dataCoefficient C*V^E
  unfold dataCoefficient
  nlinarith

theorem original_formula_final_bound (p : RawProjectionPCP) (R Q : Nat)
    (hr : p.width ≤ R) (hq : p.queries ≤ Q) {n : Nat} (x : BitInput n)
    (C D target : Nat) (hR : R ≤ target) (hQ : Q ≤ C*(R+1)^D) :
    let pcp := compactProjectionPCP (p.normalized R Q hr hq)
    RecoveryPCPFormulaResumeProof.budget R Q (Codec.clauses p).length
      (RecoveryPCPFormulaResume.words pcp x) (balancedCNFPayload (outerProofRecoveryFormula pcp x)) ≤
        sourceFormulaCoefficient C*(2^target+1)^sourceFormulaExponent D := by
  have hd := formula_data_bound R Q (Codec.clauses p).length C D target hR hQ
    (Streams.clause_count p Q hq)
  have hb := (original_formula_search_bound p R Q hr hq x).trans
    (Nat.mul_le_mul_left formulaCoefficient (Nat.pow_le_pow_left (Nat.pow_le_pow_left hd 35) 12))
  exact hb.trans_eq (scaled_power_identity formulaCoefficient (dataCoefficient C)
    (2^target+1) (dataExponent D) 35 12)

def constructorCoefficient (C : Nat) := sourceFormulaCoefficient C+65636
def constructorExponent (D amplifierExponent : Nat) :=
  sourceFormulaExponent D+2*max 1 amplifierExponent

theorem original_constructor_bound {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (p : RawProjectionPCP) (R Q : Nat) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : Nat} (x : BitInput n) (C D target : Nat) (hpos : 1 ≤ target)
    (hR : R ≤ target) (hQ : Q ≤ C*(R+1)^D)
    (hout : (amplifier.output R
      (RecoveryCaseOneRequest.request (compactProjectionPCP (p.normalized R Q hr hq)) x).function).arity ≤ target) :
    RecoveryCaseOneConstruct.budget amplifier p R Q hr hq x ≤
      constructorCoefficient C*(2^target+1)^(constructorExponent D amplifier.constructionExponent) := by
  let pcp := compactProjectionPCP (p.normalized R Q hr hq)
  let V : Nat := 2^target+1
  let E := constructorExponent D amplifier.constructionExponent
  have hv : 1 ≤ V := Nat.le_add_left 1 _
  have hE : 1 ≤ E := by dsimp [E,constructorExponent]; omega
  have hVE : V ≤ V^E := Nat.le_self_pow (by omega) _
  have h1 : 1 ≤ V^E := Nat.one_le_pow _ _ hv
  have hr1 : R+1 ≤ V := by
    have h := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=target))
    dsimp [V]
    omega
  have ht : 2^R ≤ V := (Nat.pow_le_pow_right (by decide) hR).trans (Nat.le_add_right _ 1)
  have hrbits : R.bits.length ≤ R := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hb := original_formula_final_bound p R Q hr hq x C D target hR hQ
  have hFE : sourceFormulaExponent D ≤ E := by dsimp [E,constructorExponent]; omega
  have hbE := hb.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega : 0 < V) hFE))
  have ha := amplifier_budget_bound amplifier (RecoveryCaseOneRequest.request pcp x) target hpos hR hout
  have hAE : 2*max 1 amplifier.constructionExponent ≤ E := by dsimp [E,constructorExponent]; omega
  have haE := ha.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega : 0 < V) hAE))
  have htable : (RecoveryCaseOneRequest.table pcp x).length=2^R := RecoveryCaseOneRequest.table_length pcp x
  change _ ≤ constructorCoefficient C*V^E
  unfold RecoveryCaseOneConstruct.budget RecoveryCaseOneInput.budget
    RecoveryCaseOneArchive.budget RecoveryCaseOnePayload.framedBudget RecoveryCaseOnePayload.budget
    constructorCoefficient
  simp only [List.length_append,frame_length]
  change (RecoveryCaseOneRequest.table pcp x).length=2^R at htable
  nlinarith

end
end NearCubicWires.RepairSource.CloseoutCaseOne
