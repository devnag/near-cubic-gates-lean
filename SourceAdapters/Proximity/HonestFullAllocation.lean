import SourceAdapters.Proximity.HonestFullAllocationData

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": one physically computed polynomial allocation
satisfies every initializer, source-call, row, auxiliary and restriction bound. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestFullAllocation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins Growth
open HonestPreparationSizes (measure)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)) (K e a : ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest)
      (fun r => K * ((proofCallInput V r).length + 1) ^ e))
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))

include P hr

theorem bounds_of_demand (p : AcceptedSourceInput) (Wd Lk Bk : ℕ)
    (hw : demand V proofSize K e a p ≤ Wd)
    (hl : demand V proofSize K e a p ≤ Lk) (hb : demand V proofSize K e a p ≤ Bk) :
    AllBounds V proofSize honest K e a p Wd Lk Bk := by
  have hR := Nat.zero_le (2 ^ (V p.1).randomBits)
  have hi : HonestPrepared.initialDemand V proofSize K e p ≤ demand V proofSize K e a p := by
    unfold demand
    omega
  have hc : HonestCoinSetup.demand V K e p ≤ demand V proofSize K e a p := by
    unfold demand
    omega
  have hrw : HonestRowTable.demand V K e a p ≤ demand V proofSize K e a p := by
    unfold demand
    omega
  have ib := HonestPrepared.initial_bounds V proofSize K e p Wd Lk Bk (hi.trans hw) (hi.trans hl) (hi.trans hb)
  have cb := HonestCoinSetup.bounds V K e p Wd Lk Bk (hc.trans hw) (hc.trans hl) (hc.trans hb)
  have he := Nat.lt_two_pow_self (n := Wd)
  have hextra := hw
  unfold demand at hextra
  refine ⟨ib, cb, ?_, by omega, by omega, by omega, by omega, ?_, by omega, ?_⟩
  · intro coins
    exact HonestRowTable.bounds_of_demand V proofSize honest K e P a hr p coins Wd Lk Bk
      (hrw.trans hw) (hrw.trans hl) (hrw.trans hb)
  · intro row hrow i hi
    have hk := odd_key_le (q := q) (V p.1).randomBits row i hrow hi
    omega
  · intro x hx
    exact schedule_value_width V p Wd (by omega) x hx

theorem demand_bounded : Bounded (measure V) (demand V proofSize K e a) := by
  have hi := HonestPrepared.initial_demand_bounded V proofSize honest K e P
  have hc := HonestCoinSetup.demand_bounded V a K e hr
  have hrow := HonestRowTable.demand_bounded V K e a hr
  have hR := HonestPreparationSizes.coins_bounded V a hr
  have hk := HonestPreparationSizes.auxiliary_cap_bounded V a hr
  have hn := HonestPreparationSizes.arity_bounded V
  have hs := HonestPreparationSizes.schedule_bounded V
  exact ((((((((hi.add hc).add hrow).add hR).add (bounded_const (q + blockVariableBound q))).add
    (hR.mul (bounded_const (blockVariableBound q)))).add hk).add hn).add hs).add (bounded_const 1)

theorem sufficient_allocation : ∃ A D : ℕ, 1 ≤ A ∧ ∀ p,
    AllBounds V proofSize honest K e a p
      (HonestAllocation.allocation (preparedHonestInput V) A D p)
      (HonestAllocation.allocation (preparedHonestInput V) A D p)
      (HonestAllocation.allocation (preparedHonestInput V) A D p) := by
  obtain ⟨A, D, hA, hD⟩ := HonestAllocation.sufficient (preparedHonestInput V)
    (demand V proofSize K e a) (demand_bounded V proofSize honest K e a P hr)
  exact ⟨A, D, hA, fun p => bounds_of_demand V proofSize honest K e a P hr p _ _ _ (hD p) (hD p) (hD p)⟩

end NearCubicGates.Adapters.Proximity.HonestFullAllocation
