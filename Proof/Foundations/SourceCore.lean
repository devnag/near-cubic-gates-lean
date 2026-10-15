import Proof.Foundations.OrdinaryMachine
import Proof.Foundations.PolynomialClock
import StatementSupport

/-! Shared source/consumer boundary for the correspondence repair. These
aliases use the already implemented ordinary carrier. A hierarchy's semantic
Boolean view is not a deterministic decision algorithm. No source theorem or
uniform factory is asserted by the structures in this file. -/
namespace NearCubicWires.RepairSource
open SourceInterfaces LocalBitMultitape ExecutableInterfaces CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure OrdinaryClock (T : ℕ → ℕ) where
  atLeastInput : ∀ n, n ≤ T n
  polynomial : PolynomiallyBounded T
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  computer : OrdinaryWordFunction ℕ (fun n => List.replicate n true)
    (fun n => (T n).bits) (fun n => coefficient*(T n+1))

noncomputable def OrdinaryHierarchy.timedView {T : ℕ → ℕ}
    (H : OrdinaryHierarchy T) : TimedDecisionMachine := by
  classical
  exact { accepts := fun n x => decide (H.verifier.language H.time n x)
          steps := fun n _ => H.time n }

theorem hierarchy_language_exact {T : ℕ → ℕ} (H : OrdinaryHierarchy T)
    (n : ℕ) (x : BitInput n) :
    H.timedView.accepts n x = true ↔ H.verifier.language H.time n x := by
  classical
  simp [OrdinaryHierarchy.timedView]

structure PCPDegrees where
  construction : ℕ
  queries : ℕ
  proofLog : ℕ

def pcpWord {M : TimedDecisionMachine} {T : ℕ → ℕ}
    (P : ProjectionPCP M T) {n : ℕ} (x : BitInput n) : List Bool :=
  (encodeBalancedList [P.nativeWidth n, P.queryCount n,
    encodeBalancedList ((List.ofFn fun j : Fin (P.queryCount n) =>
      List.ofFn fun i : Fin (P.nativeWidth n) =>
        projectionCode (P.queryAddressBits x j i)).flatten),
    encodeBalancedList ((P.decision x (fun _ => false)).clauses.map fun clause =>
      encodeBalancedList (List.ofFn fun j : Fin 3 => literalCode (clause j)))]).bits

/-- Local result for exactly the hierarchy the enclosing consumer selects.
The source theorem is applied to fixed U; its paid reduction realizes this
record. There is deliberately no factory over arbitrary later hierarchies. -/
structure OrdinaryPCPResult {T : ℕ → ℕ} (H : OrdinaryHierarchy T)
    (degrees : PCPDegrees) where
  pcp : ProjectionPCP H.timedView H.time
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  proofBound : ∀ n, 1 ≤ n →
    2^pcp.nativeWidth n ≤ coefficient*H.time n*logScale (H.time n)^degrees.proofLog
  queryBound : ∀ n, pcp.queryCount n ≤ coefficient*(pcp.nativeWidth n+1)^degrees.queries
  decisionIndependent : ∀ n (x : BitInput n) r s, pcp.decision x r = pcp.decision x s
  constructor : OrdinaryWordFunction InputRequest
    (fun r => frame (List.ofFn r.2) ++ frame (H.time r.1).bits)
    (fun r => pcpWord pcp r.2)
    (fun r => coefficient*(r.1+natBitLength (H.time r.1)+1)^degrees.construction)
  complete : ∀ n (x : BitInput n), H.timedView.accepts n x = true →
    ∃ proof, ∀ randomness, pcp.accepts x proof randomness = true
  sound : ∀ n, 1 ≤ n → ∀ (x : BitInput n), H.timedView.accepts n x = false →
    ∀ proof, pcp.acceptanceFraction x proof ≤ 1/(n : ℝ)^10

structure SeparatedPCPResult {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (inputExponent : ℕ) where
  degrees : PCPDegrees
  data : OrdinaryPCPResult H degrees
  coefficient : ℕ
  logTimeExponent : ℕ
  coefficientPositive : 0 < coefficient
  fineConstructor : OrdinaryWordFunction InputRequest
    (fun r => frame (List.ofFn r.2) ++ frame (H.time r.1).bits)
    (fun r => pcpWord data.pcp r.2)
    (fun r => coefficient*(r.1+1)^inputExponent*(natBitLength (H.time r.1)+1)^logTimeExponent)

/-- Semantic projection of the refuter source's full algorithmic witness.
The source-facing refuter contract must additionally retain its actual oracle
algorithm and resource guarantee; this projection alone is not that contract. -/
structure RefuterConclusion {T : ℕ → ℕ} (H : OrdinaryHierarchy T) where
  output : OrdinaryWeakMachine → (n : ℕ) → BitInput n
  separates : ∀ M, OrdinaryLittleO M T → ∃ onset, ∀ n, onset ≤ n →
    (M.accepts n (output M n) ↔ H.timedView.accepts n (output M n) = false)
structure JointOrdinarySource (T : ℕ → ℕ) where
  hierarchy : OrdinaryHierarchy T
  refuter : RefuterConclusion hierarchy
structure ChangedHierarchyOuterPCP {T : ℕ → ℕ}
    (source : JointOrdinarySource T) (degrees : PCPDegrees) where
  result : OrdinaryPCPResult source.hierarchy degrees

/-- Actual hierarchy/refuter/PCP semantic join, without the legacy refuter's
quantification over register-time weak machines. -/
theorem actualRefuterPCPRecoveryJoin {T : ℕ → ℕ}
    (source : JointOrdinarySource T) (degrees : PCPDegrees)
    (outer : ChangedHierarchyOuterPCP source degrees)
    (M : OrdinaryWeakMachine) (littleO : OrdinaryLittleO M T)
    (oneSided : ∀ n x, M.accepts n x → source.hierarchy.timedView.accepts n x = true) :
    ∃ onset, ∀ n, onset ≤ n →
      ¬M.accepts n (source.refuter.output M n) ∧
      ∃ proof, ∀ randomness,
        outer.result.pcp.accepts (source.refuter.output M n) proof randomness = true := by
  obtain ⟨onset, conflict⟩ := source.refuter.separates M littleO
  refine ⟨onset, ?_⟩
  intro n hn
  have hconflict := conflict n hn
  have reject : ¬M.accepts n (source.refuter.output M n) := by
    intro accept
    have htrue := oneSided n _ accept
    have hfalse := hconflict.mp accept
    simp [htrue] at hfalse
  have htrue : source.hierarchy.timedView.accepts n (source.refuter.output M n) = true := by
    cases h : source.hierarchy.timedView.accepts n (source.refuter.output M n)
    · exact False.elim (reject (hconflict.mpr h))
    · rfl
  exact ⟨reject, outer.result.complete n _ htrue⟩

theorem actualWitnessBound (n : ℕ) : n/16 ≤ n/10 :=
  Nat.div_le_div_left (by omega) (by omega)

end NearCubicWires.RepairSource
