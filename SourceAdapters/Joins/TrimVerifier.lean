import SourceAdapters.Proximity.Trimming

/-!
`app:sources`, "Uniform three-query PCPP and code interfaces": enumerate queried proof addresses, sort and
relabel the distinct addresses, print the target clauses, and apply the same
restriction to the honest proof. Both interfaces below are ordinary machines
with clocks polynomial in the ACTUAL flat input word, including address bits.
No source algorithm, free sorting, or free encoding conversion is assumed.

-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicGates.Published.CW19Proximity
open NearCubicGates.Adapters.Proximity

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the original input arity and the complete three-query table. -/
abbrev TrimRequest := (n : ℕ) × ThreeQueryVerifier n

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": input/proof tag, binary address, and negation bit. -/
def trimQueryFields {n : ℕ} (q : SignedQuery n) : List ℕ :=
  match q.address with
  | .inl i => [0, i.val, q.negated.toNat]
  | .inr address => [1, address, q.negated.toNat]

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": coin-major, then query-major, with exactly three queries
per coin. `natWord` has a unary bit-length prefix and binary payload. -/
def trimRequestFields (r : TrimRequest) : List ℕ :=
  [r.1, r.2.randomBits] ++
    (List.ofFn fun coins : Fin (2 ^ r.2.randomBits) =>
      (List.ofFn fun j : Fin 3 => trimQueryFields (r.2.clause coins j)).flatten).flatten

def trimRequestWord (r : TrimRequest) : List Bool :=
  (trimRequestFields r).flatMap natWord

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": this order is exactly the semantic `restrictProof` order. -/
def trimSortedAddresses (r : TrimRequest) : List ℕ :=
  (usedProofAddresses r.2).sort (· ≤ ·)

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the honest-proof constructor consumes all retained proof
addresses, including original and auxiliary addresses, excluding input bits. -/
def trimAddressWord (r : TrimRequest) : List Bool :=
  natWord (usedProofAddresses r.2).card ++ (trimSortedAddresses r).flatMap natWord

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": actual serializers, with separately paid output words.
The verifier output is EXACTLY the target word, with no extra outer frame.
The second output provides sorted distinct source addresses for honest proof
restriction. The common constants are independent of arity and address size. -/
def TrimVerifier : Prop :=
  ∃ K e : ℕ, 1 ≤ K ∧
    Nonempty (WordFunction TrimRequest trimRequestWord
      (fun r => (trimVerifier r.2).word)
      (fun r => K * ((trimRequestWord r).length + 1) ^ e)) ∧
    Nonempty (WordFunction TrimRequest trimRequestWord trimAddressWord
      (fun r => K * ((trimRequestWord r).length + 1) ^ e))

end NearCubicGates.Adapters.Joins
