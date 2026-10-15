import Proof.Foundations.BalancedCNFSATEncoding

/-!
# Conservative extension facts for compact balanced CNF queries

The compact marker occupies only queries rejected by the historical
well-sizedness predicate.  The extended SAT semantics therefore preserves
every old accepted query and sends a balanced marker to the exact historical
decision on its decoded formula.
-/

namespace NearCubicWires.BalancedCNFSATEncodingConservativeExtension

open NearCubicWires
open NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.CanonicalBinary

/-- No compact query was accepted by the historical
well-sizedness gate. -/
theorem wellSizedCNFEncoding_false_of_decodeBalancedCNF
    {code : ℕ} {formula : EncodedCNF}
    (hdecode : decodeBalancedCNF code = some formula) :
    wellSizedCNFEncoding code (decodeCNF code) = false := by
  unfold decodeBalancedCNF at hdecode
  change
    (match decodeCNF code with
      | [[], [(true, payload)]] =>
          match decodeBalancedList payload with
          | some clauses =>
              some (clauses.map fun clauseCode =>
                (Encodable.decode (α := List (Bool × ℕ)) clauseCode).getD [])
          | none => none
      | [[], [(true, payload)],
          [(false, assignment), (true, count)]] =>
          match decodeBalancedList payload with
          | some clauses =>
              some (balancedPrefixClauses count assignment ++
                clauses.map fun clauseCode =>
                  (Encodable.decode (α := List (Bool × ℕ))
                    clauseCode).getD [])
          | none => none
      | _ => none) = some formula at hdecode
  generalize hlegacy : decodeCNF code = legacy at hdecode
  split at hdecode <;> simp_all [wellSizedCNFEncoding]

/-- Every historically accepted query lies outside the new marker region. -/
theorem decodeBalancedCNF_eq_none_of_wellSized
    {code : ℕ}
    (hwell : wellSizedCNFEncoding code (decodeCNF code) = true) :
    decodeBalancedCNF code = none := by
  cases hdecode : decodeBalancedCNF code with
  | none => rfl
  | some formula =>
      have hfalse :=
        wellSizedCNFEncoding_false_of_decodeBalancedCNF hdecode
      rw [hwell] at hfalse
      contradiction

/-- All old well-sized queries have exactly their historical answer. -/
theorem encodedSat_eq_legacyEncodedSat_of_wellSized
    {code : ℕ}
    (hwell : wellSizedCNFEncoding code (decodeCNF code) = true) :
    encodedSat code = legacyEncodedSat code := by
  simp [encodedSat, hwell]

/-- Every recognized compact query has exactly the historical answer on the
ordinary canonical code of its decoded formula. -/
theorem encodedSat_eq_legacyEncodedSat_of_decodeBalancedCNF
    {code : ℕ} {formula : EncodedCNF}
    (hdecode : decodeBalancedCNF code = some formula) :
    encodedSat code = legacyEncodedSat (Encodable.encode formula) := by
  have hfalse :=
    wellSizedCNFEncoding_false_of_decodeBalancedCNF hdecode
  simp [encodedSat, hfalse, hdecode]

/-- A base compact query has exactly the historical answer on the ordinary
canonical code of the same decoded formula. -/
@[simp] theorem encodedSat_encodeBalancedCNF
    (formula : EncodedCNF) :
    encodedSat (encodeBalancedCNF formula) =
      legacyEncodedSat (Encodable.encode formula) := by
  exact encodedSat_eq_legacyEncodedSat_of_decodeBalancedCNF
    (decodeBalancedCNF_encode formula)

/-- A prefix compact query has exactly the historical answer on the ordinary
canonical code of the formula with its committed prefix clauses. -/
@[simp] theorem encodedSat_encodeBalancedPrefixCNF
    (formula : EncodedCNF) (assignment count : ℕ) :
    encodedSat (encodeBalancedPrefixCNF formula assignment count) =
      legacyEncodedSat
        (Encodable.encode
          (balancedPrefixClauses count assignment ++ formula)) := by
  exact encodedSat_eq_legacyEncodedSat_of_decodeBalancedCNF
    (decodeBalancedCNF_encodePrefix formula assignment count)

end NearCubicWires.BalancedCNFSATEncodingConservativeExtension
