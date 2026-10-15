import Proof.CaseAnalysis.RecoveryRowReusableBudget
import Proof.Amplification.RecoveryPCPFormulaResumeRowRandomness
import Proof.PCP.PCPPairReusable

/-! The original normalized address producer uses one retained padded
output cell and its existing exact randomness successor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowProjection
open LocalBitMultitape RepairSource SourceInterfaces RepairSource.ProjectionNormalization
open RecoveryRootRound CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (B : ℕ) (i : Fin 37):=if i=31 then B else 0
def padded (B : ℕ) (A : Fin 37→List Bool) (i : Fin 37):=ZeroPadding.pad (caps B i) (A i)
noncomputable def bank (p : RawProjectionPCP) (R Q : ℕ) (randomness : BitInput R) (B : ℕ):=
  padded B (RecoveryPCPFormulaResumeRow.batchInput p R Q randomness B)

theorem padded_update (B : ℕ) (A : Fin 37→List Bool) (j : Fin 37) (word : List Bool) :
    padded B (Function.update A j word)=Function.update (padded B A) j (ZeroPadding.pad (caps B j) word) := by
  funext i
  by_cases h : i=j
  · subst i; simp only [padded,Function.update_self]
  · simp only [padded,Function.update_of_ne h]

theorem batch_ready (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (randomness : BitInput R) (B : ℕ)
    (hB : RecoveryProjectionRowsRewind.batchBudget R Q+2≤B) :
    ClockJoin.ReadyRun RecoveryProjectionRowsRewind.machine (RecoveryProjectionRowsRewind.budget R Q)
      (bank p R Q randomness B)
      (Function.update (bank p R Q randomness B) 31
        (ZeroPadding.pad B (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)))) := by
  have h:=RecoveryProjectionRowsRewind.batch_ready p R Q hr hq x randomness B hB
  change ClockJoin.ReadyRun _ _ (RecoveryPCPFormulaResumeRow.batchInput p R Q randomness B)
    (RecoveryPCPFormulaResumeRow.batchOutput p R Q randomness B _) at h
  rw [RecoveryPCPFormulaResumeRow.batch_output] at h
  have hp:=PCPPairReusable.padded_ready _ _ _ h (caps B)
  change ClockJoin.ReadyRun _ _ (bank p R Q randomness B) (padded B _) at hp
  rw [padded_update] at hp
  exact hp

theorem bank_output (p : RawProjectionPCP) (R Q : ℕ) (r : BitInput R) (B : ℕ) :
    bank p R Q r B 31=List.replicate B false := by
  change ZeroPadding.pad B []=_
  simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]

theorem bank_random (p : RawProjectionPCP) (R Q : ℕ) (r s : BitInput R) (B : ℕ) :
    Function.update (bank p R Q r B) 29 (frame (List.ofFn s))=bank p R Q s B := by
  have h:=congrArg (padded B) (RecoveryPCPFormulaResumeRowRandomness.batch_random p R Q r s B)
  rw [padded_update] at h
  change Function.update (bank p R Q r B) 29 (ZeroPadding.pad 0 (frame (List.ofFn s)))=_ at h
  simpa only [ZeroPadding.pad_zero,bank] using h

theorem increment_ready (p : RawProjectionPCP) (R Q k B : ℕ) (hk : k+1<2^R) :
    ClockJoin.ReadyRun RecoveryPCPFormulaResumeRandomness.machine (4*R+2)
      (bank p R Q (bitInputOfCode R k) B) (bank p R Q (bitInputOfCode R (k+1)) B) := by
  have h:=RecoveryPCPFormulaResumeRandomness.increment_ready R k (RecoveryProjectionRows.capacity R+1)
    hk (by have h:=RecoveryProjectionColdRows.capacity_initialization R; omega)
    (bank p R Q (bitInputOfCode R k) B)
    (by change ZeroPadding.pad 0 (frame (List.ofFn (bitInputOfCode R k))++[])=_
        rw [ZeroPadding.pad_zero,List.append_nil])
    (by change ZeroPadding.pad 0 (List.replicate (RecoveryProjectionRows.capacity R+1) false)=_
        exact ZeroPadding.pad_zero _)
  rw [bank_random] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowProjection
