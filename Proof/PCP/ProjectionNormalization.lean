import Proof.Foundations.ProjectionSourceContract
import Proof.Foundations.ProjectionPCPPadding

/-! Local normalization of one RAW source witness to length-only dimensions.
Unused queries do not enter the decision. Added randomness is ignored and
proof addresses are embedded in the zero-suffix face. Execution, compaction
and serialization costs are separate local obligations. -/
namespace NearCubicWires.RepairSource
open SourceInterfaces ProjectionPCPPadding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def liftQueryLiteral {q Q : ℕ} (h : q ≤ Q) : Literal q → Literal Q
  | .positive i => .positive (Fin.castLE h i)
  | .negative i => .negative (Fin.castLE h i)

@[simp] theorem liftQueryLiteral_eval {q Q : ℕ} (h : q ≤ Q)
    (literal : Literal q) (assignment : BitInput Q) :
    (liftQueryLiteral h literal).eval assignment =
      literal.eval (fun i => assignment (Fin.castLE h i)) := by
  cases literal <;> rfl

def RawProjectionPCP.raiseQueries (p : RawProjectionPCP) (Q : ℕ)
    (hq : p.queries ≤ Q) : RawProjectionPCP where
  width := p.width
  queries := Q
  queryBits := fun j i => if hj : j.val < p.queries
    then p.queryBits ⟨j.val, hj⟩ i else .constant false
  decision := ⟨p.decision.clauses.map (fun c j => liftQueryLiteral hq (c j))⟩

theorem RawProjectionPCP.raiseQueries_accepts (p : RawProjectionPCP) (Q : ℕ)
    (hq : p.queries ≤ Q) (proof : BitInput (2 ^ p.width))
    (randomness : BitInput p.width) :
    (p.raiseQueries Q hq).accepts proof randomness = p.accepts proof randomness := by
  simp only [RawProjectionPCP.accepts, RawProjectionPCP.raiseQueries, ThreeCNF.eval,
    List.all_map, Function.comp_def, liftQueryLiteral_eval, Fin.val_castLE,
    Fin.is_lt, dite_true]

theorem RawProjectionPCP.raiseQueries_fraction (p : RawProjectionPCP) (Q : ℕ)
    (hq : p.queries ≤ Q) (proof : BitInput (2 ^ p.width)) :
    (p.raiseQueries Q hq).acceptanceFraction proof = p.acceptanceFraction proof := by
  simp only [RawProjectionPCP.acceptanceFraction, RawProjectionPCP.raiseQueries_accepts]
  rfl

/-- Constant-input semantic view used to reuse the existing exact padding
proof. Its constructionSteps field is not an execution claim. -/
def RawProjectionPCP.constant (p : RawProjectionPCP) :
    ProjectionPCP ⟨fun _ _ => false, fun _ _ => 0⟩ (fun _ => 0) where
  nativeWidth := fun _ => p.width
  queryCount := fun _ => p.queries
  queryAddressBits := fun _ => p.queryBits
  decision := fun _ _ => p.decision
  constructionSteps := fun _ => 0

def RawProjectionPCP.normalized (p : RawProjectionPCP) (R Q : ℕ)
    (hr : p.width ≤ R) (hq : p.queries ≤ Q) :=
  padProjectionPCP (p.raiseQueries Q hq).constant (fun _ => R) (fun _ => hr)

def normalizeProjectionPCP {machine : TimedDecisionMachine} {T : ℕ → ℕ}
    (raw : InputRequest → RawProjectionPCP) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (raw r).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (raw r).queries ≤ Q r.1) : ProjectionPCP machine T where
  nativeWidth := R
  queryCount := Q
  queryAddressBits := fun {n} x =>
    ((raw ⟨n,x⟩).normalized (R n) (Q n) (hr ⟨n,x⟩) (hq ⟨n,x⟩)).queryAddressBits x
  decision := fun {n} x =>
    ((raw ⟨n,x⟩).normalized (R n) (Q n) (hr ⟨n,x⟩) (hq ⟨n,x⟩)).decision x
  constructionSteps := fun _ => 0

theorem normalizeProjectionPCP_accepts {machine : TimedDecisionMachine} {T : ℕ → ℕ}
    (raw : InputRequest → RawProjectionPCP) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (raw r).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (raw r).queries ≤ Q r.1)
    (r : InputRequest) (proof : BitInput (2 ^ R r.1)) (randomness : BitInput (R r.1)) :
    (normalizeProjectionPCP (machine := machine) (T := T) raw R Q hr hq).accepts r.2 proof randomness =
      (raw r).accepts (restrictPaddedProof (hr r) proof) (prefixBits (hr r) randomness) := by
  change ((raw r).normalized (R r.1) (Q r.1) (hr r) (hq r)).accepts r.2 proof randomness = _
  unfold RawProjectionPCP.normalized
  rw [padProjectionPCP_accepts]
  exact (raw r).raiseQueries_accepts _ _ _ _

theorem normalizeProjectionPCP_fraction {machine : TimedDecisionMachine} {T : ℕ → ℕ}
    (raw : InputRequest → RawProjectionPCP) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (raw r).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (raw r).queries ≤ Q r.1)
    (r : InputRequest) (proof : BitInput (2 ^ R r.1)) :
    (normalizeProjectionPCP (machine := machine) (T := T) raw R Q hr hq).acceptanceFraction r.2 proof =
      (raw r).acceptanceFraction (restrictPaddedProof (hr r) proof) := by
  change ((raw r).normalized (R r.1) (Q r.1) (hr r) (hq r)).acceptanceFraction r.2 proof = _
  unfold RawProjectionPCP.normalized
  rw [padProjectionPCP_acceptanceFraction]
  exact (raw r).raiseQueries_fraction _ _ _

theorem normalizeProjectionPCP_independent {machine : TimedDecisionMachine} {T : ℕ → ℕ}
    (raw : InputRequest → RawProjectionPCP) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (raw r).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (raw r).queries ≤ Q r.1)
    (r : InputRequest) (x y : BitInput (R r.1)) :
    (normalizeProjectionPCP (machine := machine) (T := T) raw R Q hr hq).decision r.2 x =
      (normalizeProjectionPCP (machine := machine) (T := T) raw R Q hr hq).decision r.2 y := rfl

/-- Immediate full source-to-normalized semantic consumer, preserving the
same source output at the selected padded input. -/
theorem normalized_source_complete {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest → InputRequest) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (source.output (encode r)).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (source.output (encode r)).queries ≤ Q r.1)
    (positive : ∀ r, 1 ≤ (encode r).1)
    (language : ∀ r, H.verifier.language H.time r.1 r.2 ↔
      v.language U (encode r).1 (encode r).2)
    (r : InputRequest) (yes : H.timedView.accepts r.1 r.2 = true) :
    ∃ proof, ∀ randomness,
      (normalizeProjectionPCP (machine := H.timedView) (T := H.time)
        (source.output ∘ encode) R Q hr hq).accepts r.2 proof randomness = true := by
  obtain ⟨proof, complete⟩ := projection_padded_complete source H encode positive language r yes
  refine ⟨extendNativeProof (hr r) proof, ?_⟩
  intro randomness
  rw [normalizeProjectionPCP_accepts]
  change (source.output (encode r)).accepts
    (restrictPaddedProof (hr r) (extendNativeProof (hr r) proof))
    (prefixBits (hr r) randomness) = true
  rw [restrictPaddedProof_extendNativeProof]
  exact complete _

theorem normalized_source_sound {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest → InputRequest) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (source.output (encode r)).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (source.output (encode r)).queries ≤ Q r.1)
    (length : ∀ r, r.1+1 ≤ (encode r).1)
    (language : ∀ r, H.verifier.language H.time r.1 r.2 ↔
      v.language U (encode r).1 (encode r).2)
    (r : InputRequest) (no : H.timedView.accepts r.1 r.2 = false)
    (proof : BitInput (2 ^ R r.1)) :
    (normalizeProjectionPCP (machine := H.timedView) (T := H.time)
      (source.output ∘ encode) R Q hr hq).acceptanceFraction r.2 proof ≤
        1 / ((r.1+1 : ℕ) : ℝ)^10 := by
  rw [normalizeProjectionPCP_fraction]
  exact projection_padded_sound source H encode length language r no _

end NearCubicWires.RepairSource
