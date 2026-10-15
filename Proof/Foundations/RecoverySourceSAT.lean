import Proof.Foundations.RecoveryOracleSemantics
import StatementSupport

/-! The source refuter uses conventional explicit 3SAT, represented by a
canonical balanced list of fixed-length clause codes.  Recursive `Encodable`
is used only inside a three-literal clause, never around the whole formula.
The source predicate has no committed-prefix or legacy size-guard convention.
Its polynomial representation conversion and the lift to the corrected
recovery predicate are local theorems, not imported premises. -/
namespace NearCubicWires.RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open CanonicalBinary BalancedCNFSATEncoding
open private legacyDecodeCNF natBitLength_succ_le pairSuccBits_le from StatementSupport

def sourceSATCode (formula : EncodedCNF) : Nat := balancedCNFPayload formula

@[simp] theorem decodeSourceSAT_encode (formula : EncodedCNF) :
    decodeSourceSAT (sourceSATCode formula) = some formula := by
  simp [decodeSourceSAT, sourceSATCode, balancedCNFPayload,
    Encodable.encodek, Function.comp_def]

theorem sourceSAT_encode (formula : EncodedCNF) :
    sourceSAT (sourceSATCode formula) =
      ((formula.all fun clause => clause.length = 3) && mathSat formula) := by
  simp [sourceSAT]

theorem sourceSAT_encode_iff (formula : EncodedCNF)
    (hthree : ∀ clause ∈ formula, clause.length = 3) :
    sourceSAT (sourceSATCode formula) = true ↔
      ∃ assignment : Nat → Bool, TseitinCNF.formulaEval assignment formula = true := by
  classical
  have hthree' : formula.all (fun clause => clause.length = 3) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hthree
  simp [sourceSAT_encode, hthree', mathSat]

theorem liftSourceSAT_encode (formula : EncodedCNF) :
    liftSourceSAT (sourceSATCode formula) = encodeBalancedCNF formula := rfl

/-- A fixed three-literal clause uses only constant-depth pairing. -/
private theorem clauseCode_bits (clause : List (Bool × Nat)) (width : Nat)
    (hw : 1 ≤ width) (hwidth : ∀ literal ∈ clause, natBitLength literal.2 ≤ width) :
    natBitLength (Encodable.encode clause) + 1 ≤
      2 ^ (clause.length + 1) * (width + 1) := by
  induction clause with
  | nil => change 1 + 1 ≤ 2 * (width + 1); omega
  | cons literal tail ih =>
    have hlw := hwidth literal (by simp)
    have htw := ih (by intro x hx; exact hwidth x (by simp [hx]))
    have hliteral : natBitLength (Encodable.encode literal) ≤ 2 * width := by
      have hb : natBitLength (Encodable.encode literal.1) ≤ width := by
        cases literal.1 <;> simpa [natBitLength] using hw
      change natBitLength (Nat.pair (Encodable.encode literal.1) literal.2) ≤ _
      exact
        (pairCodeBits_le (Encodable.encode literal.1) literal.2).trans
          (Nat.mul_le_mul_left 2 (max_le hb hlw))
    have hexp : 2 ≤ 2 ^ (tail.length + 1) := by
      have := Nat.one_le_two_pow (n := tail.length)
      rw [pow_succ]
      omega
    have hmax : max (natBitLength (Encodable.encode literal))
        (natBitLength (Encodable.encode tail)) + 1 ≤
          2 ^ (tail.length + 1) * (width + 1) := by
      rw [← max_add_add_right]
      apply max_le _ htw
      nlinarith
    have hp := pairSuccBits_le (Encodable.encode literal) (Encodable.encode tail)
    change natBitLength (Nat.pair (Encodable.encode literal) (Encodable.encode tail) + 1) + 1 ≤
      2 ^ (tail.length + 1 + 1) * (width + 1)
    rw [pow_succ]
    nlinarith

/-- Polynomial in clause count and the conventional maximum label width.
The fixed factor 16 comes from the three recursive list cells, not from the
number of clauses. -/
theorem sourceSATCode_bits (formula : EncodedCNF) (width : Nat)
    (hw : 1 ≤ width) (hthree : ∀ clause ∈ formula, clause.length = 3)
    (hwidth : ∀ clause ∈ formula, ∀ literal ∈ clause,
      natBitLength literal.2 ≤ width) :
    natBitLength (sourceSATCode formula) ≤
      1 + 2 * formula.length ^ 4 * (formula.length * (16 * (width + 1)) + 1) := by
  have hclauses : ∀ clause ∈ formula,
      natBitLength (Encodable.encode clause) ≤ 16 * (width + 1) := by
    intro clause hc
    have h := clauseCode_bits clause width hw (hwidth clause hc)
    rw [hthree clause hc] at h
    norm_num at h
    omega
  have hsum : ((formula.map Encodable.encode).map natBitLength).sum ≤
      formula.length * (16 * (width + 1)) := by
    apply (List.sum_le_card_nsmul _ (16 * (width + 1)) ?_).trans_eq
    · simp
    · intro value hv
      simp only [List.mem_map] at hv
      obtain ⟨code, ⟨clause, hc, rfl⟩, rfl⟩ := hv
      exact hclauses clause hc
  have h := balancedListCodeBits_le (formula.map Encodable.encode)
  simp only [List.length_map] at h
  apply h.trans
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right hsum 1)) 1

end NearCubicWires.RepairSource.RecoveryOracle
