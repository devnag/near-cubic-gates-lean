import Proof.Amplification.RecoveryCaseOneAmplifierReady

/-! The same physically searched table determines the amplifier request
on every input, and equals the paper's canonical proof whenever complete. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneRequest
open RepairOrdinary SourceInterfaces CanonicalRecoveryLanguage BalancedCNFSATEncoding
open ExecutableInterfaces OuterPCPRecovery RecoveryChoice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T)

def table {n : Nat} (x : BitInput n) := RecoveryPrefixBody.search true
  (balancedCNFPayload (outerProofRecoveryFormula pcp x)) (2^pcp.nativeWidth n) []
theorem table_length {n : Nat} (x : BitInput n) : (table pcp x).length=2^pcp.nativeWidth n := by
  simp [table]
def proof {n : Nat} (x : BitInput n) : BitInput (2^pcp.nativeWidth n) :=
  fun i=>(table pcp x)[i.val]'(by rw [table_length]; exact i.isLt)
theorem proof_table {n : Nat} (x : BitInput n) : List.ofFn (proof pcp x)=table pcp x := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,table_length]
  · intro i hi hj
    simp only [List.getElem_ofFn,proof]

def request {n : Nat} (x : BitInput n) : AmplifierRequest :=
  ⟨pcp.nativeWidth n,proofFunction pcp (proof pcp x)⟩
theorem request_input {n : Nat} (x : BitInput n) :
    amplifierInput (request pcp x)=frame (pcp.nativeWidth n).bits++table pcp x := by
  simp only [amplifierInput,request,boolFunctionTable_proofFunction,proof_table]

theorem proof_canonical {n : Nat} (x : BitInput n)
    (complete : ∃ pi,∀ randomness,pcp.accepts x pi randomness) :
    proof pcp x=(proofSelector pcp x complete).proof := by
  apply List.ofFn_injective
  rw [proof_table]
  exact RecoveryPCPFormulaResumeProof.search_proof pcp x complete

theorem request_canonical {n : Nat} (x : BitInput n)
    (complete : ∃ pi,∀ randomness,pcp.accepts x pi randomness) :
    request pcp x=⟨pcp.nativeWidth n,proofFunction pcp (proofSelector pcp x complete).proof⟩ := by
  unfold request
  rw [proof_canonical pcp x complete]

end
end NearCubicWires.RepairSource.RecoveryCaseOneRequest
