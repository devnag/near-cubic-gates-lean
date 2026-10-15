import Proof.PCP.ProjectionNormalization

/-! Local duplicate deletion from the same selected PCP decision. Its actual
serializer is included in NormalizedPCPRun. This proof fixes the decision
size needed by the PCPP consumer, independently of the source output length. -/
namespace NearCubicWires.RepairSource
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

deriving instance DecidableEq for Literal

private def literalEquiv (q : ℕ) : Literal q ≃ Bool × Fin q where
  toFun := fun l => match l with | .positive i => (false,i) | .negative i => (true,i)
  invFun := fun p => if p.1 then .negative p.2 else .positive p.2
  left_inv := by intro l; cases l <;> rfl
  right_inv := by intro p; rcases p with ⟨b,i⟩; cases b <;> rfl

private instance literalFintype (q : ℕ) : Fintype (Literal q) :=
  Fintype.ofEquiv (Bool × Fin q) (literalEquiv q).symm

private theorem literal_card (q : ℕ) : Fintype.card (Literal q) = 2*q := by
  rw [Fintype.card_congr (literalEquiv q)]
  simp

def compactThreeCNF {q : ℕ} (formula : ThreeCNF q) : ThreeCNF q :=
  ⟨formula.clauses.dedup⟩

@[simp] theorem compactThreeCNF_eval {q : ℕ} (formula : ThreeCNF q)
    (assignment : BitInput q) :
    (compactThreeCNF formula).eval assignment = formula.eval assignment := by
  apply Bool.eq_iff_iff.mpr
  simp [compactThreeCNF, ThreeCNF.eval, List.all_eq_true]

theorem compactThreeCNF_clauses {q : ℕ} (formula : ThreeCNF q) :
    (compactThreeCNF formula).clauses.length ≤ (2*q)^3 := by
  have h := (List.nodup_dedup formula.clauses).length_le_card
  simpa only [compactThreeCNF, Fintype.card_fun, Fintype.card_fin, literal_card] using h

def compactProjectionPCP {M : TimedDecisionMachine} {T : ℕ → ℕ}
    (p : ProjectionPCP M T) : ProjectionPCP M T :=
  { p with decision := fun x r => compactThreeCNF (p.decision x r) }

@[simp] theorem compactProjectionPCP_accepts {M : TimedDecisionMachine} {T : ℕ → ℕ}
    (p : ProjectionPCP M T) {n : ℕ} (x : BitInput n)
    (proof : BitInput (2^p.nativeWidth n)) (randomness : BitInput (p.nativeWidth n)) :
    (compactProjectionPCP p).accepts x proof randomness = p.accepts x proof randomness := by
  exact compactThreeCNF_eval _ _

@[simp] theorem compactProjectionPCP_fraction {M : TimedDecisionMachine} {T : ℕ → ℕ}
    (p : ProjectionPCP M T) {n : ℕ} (x : BitInput n)
    (proof : BitInput (2^p.nativeWidth n)) :
    (compactProjectionPCP p).acceptanceFraction x proof = p.acceptanceFraction x proof := by
  simp only [ProjectionPCP.acceptanceFraction, compactProjectionPCP_accepts]
  rfl

theorem compactProjectionPCP_clauses {M : TimedDecisionMachine} {T : ℕ → ℕ}
    (p : ProjectionPCP M T) {n : ℕ} (x : BitInput n)
    (randomness : BitInput (p.nativeWidth n)) :
    ((compactProjectionPCP p).decision x randomness).clauses.length ≤ (2*p.queryCount n)^3 :=
  compactThreeCNF_clauses _

end NearCubicWires.RepairSource
