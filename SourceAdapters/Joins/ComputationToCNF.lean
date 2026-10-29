import Proof.Foundations.RecoverySourceSAT
import Proof.Foundations.VerifierEncoding

/-!
Bounded actual framed computation to native balanced exact-three-CNF.
Stated for the refuter's half-open witness prefix [0, high).
proof of `lem:multitape-refuter`; proof of `cor:framed-refuter` require a single compiler whose polynomial degree
is independent of M. Thus the verifier code is input to one WordFunction;
the quantifier order is not a separate compiler for each verifier.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.TseitinCNF

set_option autoImplicit false

/-- proof of `lem:multitape-refuter`: lexicographic witness rank, first bit most
significant. The consuming search uses the strict half-open prefix [0, high).
-/
def witnessRank {k : ℕ} (witness : BitInput k) : ℕ :=
  (List.ofFn witness).foldl (fun acc bit => 2 * acc + if bit then 1 else 0) 0

/-- proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`: bounded acceptance with the exact witness length
and a half-open lexicographic prefix [0, high). `high = 0` is empty;
`high = 2^witnessLength` includes every witness. -/
structure CNFCompilationRequest where
  verifier : OrdinaryVerifier
  input : List Bool
  witnessLength : ℕ
  fuel : ℕ
  high : ℕ

/-- proof of `lem:multitape-refuter`: finite control, actual input, and unary resource data.
The native verifier code records its finite transition table, not the
arbitrary descriptionBits annotation. No runtime function is an input. -/
def CNFCompilationRequest.word (r : CNFCompilationRequest) : List Bool :=
  RepairOrdinary.frame (VerifierEncoding.code r.verifier) ++
    RepairOrdinary.frame r.input ++
    RepairOrdinary.frame (List.replicate r.witnessLength true) ++
    RepairOrdinary.frame (List.replicate r.fuel true) ++
    RepairOrdinary.frame r.high.bits

/-- proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`: code length is paid and the degree stays fixed. -/
def CNFCompilationRequest.measure (r : CNFCompilationRequest) : ℕ :=
  (VerifierEncoding.code r.verifier).length + r.input.length +
    r.witnessLength + r.fuel + natBitLength r.high + 1

/-- proof of `lem:multitape-refuter`; `cor:framed-refuter`; proof of `cor:framed-refuter`: actual framed tapes and fixed terminators.
`acceptsAt` uses the verifier's native initial tapes, including blank suffixes. -/
def CNFCompilationRequest.accepts (r : CNFCompilationRequest) : Prop :=
  ∃ witness : BitInput r.witnessLength,
    witnessRank witness < r.high ∧
      r.verifier.acceptsAt r.fuel r.input (List.ofFn witness)

/-- X5(b), F05. One code-input compiler; coefficient and degree are chosen
before all verifiers. Membership uses high = 2^witnessLength; the binary search
uses the half-open prefix [0, high), so it needs no verifier-code transformer.
The consumer still pays the O(N) queries and final N-bit output.
Empty witness intervals and inconsistent computations are included by the
universal quantification; neither is excluded by a satisfiability premise. -/
def ComputationToCNF : Prop :=
  ∃ K d : ℕ, ∃ formula : CNFCompilationRequest → EncodedCNF,
    -- proof of `lem:multitape-refuter`: global coefficient and polynomial degree.
    1 ≤ K ∧
    -- proof of `lem:multitape-refuter`: exactly three literals, with padding/contradiction allowed.
    (∀ r, ∀ clause ∈ formula r, clause.length = 3) ∧
    -- proof of `lem:multitape-refuter`: satisfiability iff the bounded queried condition.
    (∀ r, (∃ assignment : ℕ → Bool, formulaEval assignment (formula r) = true) ↔
      r.accepts) ∧
    -- proof of `lem:multitape-refuter`: native literal-list coding and balanced outer coding.
    (∀ r, RecoveryOracle.decodeSourceSAT (RecoveryOracle.sourceSATCode (formula r)) =
      some (formula r)) ∧
    -- proof of `lem:multitape-refuter`: the source oracle answers exactly the bounded question.
    (∀ r, RecoveryOracle.sourceSAT (RecoveryOracle.sourceSATCode (formula r)) = true ↔
      r.accepts) ∧
    -- proof of `lem:multitape-refuter`: polynomial formula size, uniformly in finite-control code.
    (∀ r, (formula r).length ≤ K * r.measure ^ d) ∧
    -- proof of `lem:multitape-refuter`: polynomial native encoded bit length.
    (∀ r, natBitLength (RecoveryOracle.sourceSATCode (formula r)) ≤
      K * r.measure ^ d) ∧
    -- proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`: the complete framed SAT query is actually written.
    Nonempty (WordFunction CNFCompilationRequest CNFCompilationRequest.word
      (fun r => RepairOrdinary.frame (RecoveryOracle.sourceSATCode (formula r)).bits)
      (fun r => K * r.measure ^ d))

end NearCubicGates.Adapters.Compile
