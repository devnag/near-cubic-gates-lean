import SourceAdapters.Proximity.HonestPreparedRun
import SourceAdapters.Proximity.HonestPreparationSizes
import SourceAdapters.Proximity.HonestAllocation

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": polynomial width, request and clock demands for
the actual prepared-input initializer, measured in its physical input word. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins Growth
open HonestPreparationSizes (measure)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (K e : ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest)
      (fun r => K * ((proofCallInput V r).length + 1) ^ e))

def initialDemand (p : AcceptedSourceInput) : ℕ :=
  measure V p + 3 + q + 2 ^ q + blockVariableBound q + proofSize p.1 +
    (2 + (sourceCircuitWord p.1).length + p.1.arity) +
    K * ((proofCallInput V (HonestSource.request V p)).length + 1) ^ e + 1

include P in
theorem initial_demand_bounded : Bounded (measure V) (initialDemand V proofSize K e) := by
  have hs : Bounded (measure V) (fun p => (sourceCircuitWord p.1).length) :=
    bounded_size.mono (HonestPreparationSizes.source_length V)
  have hn := HonestPreparationSizes.arity_bounded V
  have hp := HonestPreparationSizes.proof_size_bounded V proofSize honest K e P
  have hc := HonestPreparationSizes.honest_budget_bounded V K e
  exact ((((((((bounded_size.add (bounded_const 3)).add (bounded_const q)).add
    (bounded_const (2 ^ q))).add (bounded_const (blockVariableBound q))).add hp).add
    (((bounded_const 2).add hs).add hn)).add hc).add (bounded_const 1))

theorem initial_bounds (p : AcceptedSourceInput) (Wd Lk Bk : ℕ)
    (hw : initialDemand V proofSize K e p ≤ Wd)
    (hl : initialDemand V proofSize K e p ≤ Lk)
    (hb : initialDemand V proofSize K e p ≤ Bk) :
    (preparedHonestInput V p).length + 3 ≤ Wd ∧ q < 2 ^ Wd ∧ 2 ^ q < 2 ^ Wd ∧
    blockVariableBound q < 2 ^ Wd ∧ proofSize p.1 < 2 ^ Wd ∧
    2 + (sourceCircuitWord p.1).length + p.1.arity ≤ Lk ∧
    K * ((proofCallInput V (HonestSource.request V p)).length + 1) ^ e ≤ Bk := by
  have he := Nat.lt_two_pow_self (n := Wd)
  have ht := Nat.one_le_two_pow (n := q)
  simp only [initialDemand, HonestPreparationSizes.measure] at hw hl hb
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

include P in
theorem initial_cost_bounded (Lk Bk : AcceptedSourceInput → ℕ)
    (hL : Bounded (measure V) Lk) (hB : Bounded (measure V) Bk) :
    Bounded (measure V) (fun p => initialCost V proofSize p (Lk p) (Bk p)) := by
  have hs : Bounded (measure V) (fun p => (sourceCircuitWord p.1).length) :=
    bounded_size.mono (HonestPreparationSizes.source_length V)
  have hn := HonestPreparationSizes.arity_bounded V
  have hp := HonestPreparationSizes.proof_size_bounded V proofSize honest K e P
  have hsetup : Bounded (measure V) (fun _ => 2 * q + 2 * 2 ^ q + 2 * blockVariableBound q + 17) := bounded_const _
  have hload : Bounded (measure V) (fun p => 1100 * (measure V p + 1) ^ 2) :=
    (bounded_const 1100).mul ((bounded_size.add (bounded_const 1)).pow 2)
  have hsource := ((((((bounded_const 15).mul hs).add ((bounded_const 9).mul hn)).add hL).add hB).add
    ((bounded_const 9).mul hp)).add (bounded_const 33)
  exact ((hsetup.add hload).add hsource).add (bounded_const 2)

include P in
theorem initial_allocation : ∃ A D : ℕ, 1 ≤ A ∧ ∀ p,
    initialDemand V proofSize K e p ≤ HonestAllocation.allocation (preparedHonestInput V) A D p :=
  HonestAllocation.sufficient (preparedHonestInput V) (initialDemand V proofSize K e)
    (initial_demand_bounded V proofSize honest K e P)

end NearCubicGates.Adapters.Proximity.HonestPrepared
