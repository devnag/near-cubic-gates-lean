import Proof.Foundations.BalancedCNFCodec
import Proof.Foundations.TseitinCNF

/-!
# Semantic facts for the compact, disjoint CNF code

The historical SAT ABI consumes `Encodable.encode formula`.  Its linked list
has exponential bit width in the number of clauses.  This file defines the
compact additive alternative used by the repaired recovery path.

The outer cell deliberately has the ordinary-list head code `0`.  Under the
old decoder that is an empty first clause, hence is rejected by the existing
three-literal well-sizedness guard.  The payload is the canonical balanced
list of the ordinary encodings of the individual clauses.  Consequently the
new convention occupies only an old-rejected portion of the SAT query space;
all formerly well-sized canonical queries remain disjoint.
-/

namespace NearCubicWires.BalancedCNFSATEncoding

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.TseitinCNF

/-- The old canonical decoder sees the marker as an empty first clause. -/
theorem decodeCNF_encodeBalancedCNF (formula : EncodedCNF) :
    decodeCNF (encodeBalancedCNF formula) =
      balancedCNFMarker formula := by
  exact decodeCNF_encode _

/-- Therefore the marker was rejected by the historical SAT semantics. -/
@[simp] theorem wellSizedCNFEncoding_encodeBalancedCNF (formula : EncodedCNF) :
    wellSizedCNFEncoding (encodeBalancedCNF formula)
        (decodeCNF (encodeBalancedCNF formula)) = false := by
  rw [decodeCNF_encodeBalancedCNF]
  simp [wellSizedCNFEncoding, balancedCNFMarker]

end NearCubicWires.BalancedCNFSATEncoding
