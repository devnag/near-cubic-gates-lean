import SourceAdapters.Proximity.HonestRowTableRun
import SourceAdapters.Proximity.HonestPreparationSizes
import SourceAdapters.Proximity.HonestAllocation

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": source polynomial bounds and logarithmic coins
supply all row resources, measured in the actual prepared honest input. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestRowTable

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins Growth
open HonestPreparationSizes (measure)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)

theorem table_request_length (predicate : BitInput q → Bool) (answers : BitInput q) :
    (proofCallInput V (HonestTableCall.request V predicate answers)).length = 2 + 2 ^ q + q := by
  rw [HonestTableCall.request_input]
  simp only [List.length_append, List.length_ofFn, HonestTableCall.tag, List.length_cons, List.length_nil]

theorem table_request_cap (a L : ℕ) (predicate : BitInput q → Bool) (answers : BitInput q) :
    (proofCallInput V (HonestTableCall.request V predicate answers)).length ≤ SourceCallee.requestCap q a L := by
  rw [table_request_length]
  unfold SourceCallee.requestCap
  have hp := Nat.zero_le (2 ^ q)
  nlinarith [Nat.zero_le (a * L), Nat.zero_le (q * L), Nat.zero_le (2 ^ q * L)]

variable (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)) (K e : ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest)
      (fun r => K * ((proofCallInput V r).length + 1) ^ e))

def rowWidth (a : ℕ) (p : AcceptedSourceInput) : ℕ :=
  SourceCallee.widthMeasure q (V p.1).randomBits
    (SourceCallee.callBudgetCap q a K e (sourceCircuitWord p.1).length)

def demand (a : ℕ) (p : AcceptedSourceInput) : ℕ :=
  SourceCallee.widthDemand q (sourceCircuitWord p.1).length (V p.1).randomBits
    (SourceCallee.callBudgetCap q a K e (sourceCircuitWord p.1).length) +
  SourceCallee.requestCap q a (sourceCircuitWord p.1).length +
  SourceCallee.callBudgetCap q a K e (sourceCircuitWord p.1).length + 1

include P in
 theorem bounds_of_demand (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (p : AcceptedSourceInput) (coins : Fin (2 ^ (V p.1).randomBits)) (Wd Lk Bk : ℕ)
    (hw : demand V K e a p ≤ Wd) (hl : demand V K e a p ≤ Lk) (hb : demand V K e a p ≤ Bk) :
    Bounds V (fun r => K * ((proofCallInput V r).length + 1) ^ e)
      p.1 coins p.2.val (honest p) Wd Lk Bk (rowWidth V K e a p) := by
  let R := SourceCallee.requestCap q a (sourceCircuitWord p.1).length
  let B := SourceCallee.callBudgetCap q a K e (sourceCircuitWord p.1).length
  have hroom : R ≤ Lk := by dsimp only [demand] at hl; exact le_trans (by dsimp only [R]; omega) hl
  have hclock : B ≤ Bk := by dsimp only [demand] at hb; exact le_trans (by dsimp only [B]; omega) hb
  have hwidth : SourceCallee.widthDemand q (sourceCircuitWord p.1).length (V p.1).randomBits B ≤ Wd := by
    dsimp only [demand] at hw
    dsimp only [B]
    omega
  have hbud : ∀ request, (proofCallInput V request).length ≤ R →
      K * ((proofCallInput V request).length + 1) ^ e ≤ B := fun request h =>
    SourceCallee.budget_below_cap V a K e _ request h
  have h := SourceCallee.numerical_rows V proofSize honest _ P p.1 coins R B Wd Lk Bk
    (SourceCallee.request_lengths V a p.1 coins (SourceCallee.random_linear V a hr p.1))
    hbud hroom hclock hwidth
  have htable := table_request_cap V a (sourceCircuitWord p.1).length
    (rowPredicate (V p.1) coins) (TrimHonest.rowAnswers (V p.1) coins p.2.val (honest p))
  have hrow : blockVariableBound q < 2 ^ Wd := by
    have hp := Nat.zero_le (2 ^ q)
    have he := Nat.lt_two_pow_self (n := Wd)
    simp only [SourceCallee.widthDemand, SourceCallee.widthMeasure] at hwidth
    omega
  exact ⟨h.width_four, h.width_bits, h.query_width, h.truth_width, hrow,
    h.row_bits, h.count_bits, h.query_bits, h.address_bits, h.count_room, h.count_budget,
    h.query_room, h.query_budget, h.decision_room, h.decision_budget,
    (by rw [table_request_length] at htable; exact htable.trans hroom), (hbud _ htable).trans hclock⟩

theorem demand_bounded (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) :
    Bounded (measure V) (demand V K e a) := by
  have hw := HonestPreparationSizes.transfer V _ (SourceCallee.widthDemand_bounded V a hr K e)
  have hrq := HonestPreparationSizes.request_cap_bounded V a
  have hb := HonestPreparationSizes.call_budget_bounded V a K e
  exact ((hw.add hrq).add hb).add (bounded_const 1)

theorem row_width_bounded (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) :
    Bounded (measure V) (rowWidth V K e a) :=
  HonestPreparationSizes.transfer V _ (SourceCallee.widthMeasure_bounded V a hr K e)

include P in
 theorem cost_bounded (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (Lk Bk : AcceptedSourceInput → ℕ) (hL : Bounded (measure V) Lk) (hB : Bounded (measure V) Bk) :
    Bounded (measure V) (fun p => cost q p.1.arity (proofSize p.1) (sourceCircuitWord p.1).length
      (Lk p) (Bk p) (rowWidth V K e a p)) := by
  have hs : Bounded (measure V) (fun p => (sourceCircuitWord p.1).length) :=
    bounded_size.mono (HonestPreparationSizes.source_length V)
  have hn := HonestPreparationSizes.arity_bounded V
  have hp := HonestPreparationSizes.proof_size_bounded V proofSize honest K e P
  have hΛ := row_width_bounded V K e a hr
  have h15 := (bounded_const 15).mul hs
  have hpass := (((h15.add hL).add hB).add ((bounded_const 30).mul hΛ)).add (bounded_const 64)
  have hquery := ((((((bounded_const q).mul hpass).add h15).add hL).add hB).add
    ((bounded_const 20).mul hΛ)).add (bounded_const (2 * q))
  have hanswers := ((bounded_const (3 * q)).add
    ((((bounded_const 6).mul (hn.add hp)).add (bounded_const 21)).mul (bounded_const q))).add (bounded_const 8)
  have hdecision := ((((h15.add ((bounded_const 10).mul hΛ)).add (bounded_const (6 * q))).add hL).add hB).add
    (bounded_const 45)
  have htable := ((bounded_const (2 ^ q)).mul hdecision).add (bounded_const 3)
  have hcall := ((((bounded_const (9 * 2 ^ q + 9 * q)).add hL).add hB).add
    (bounded_const (8 * blockVariableBound q))).add (bounded_const 28)
  exact ((((hquery.add (bounded_const 50)).add hanswers).add htable).add hcall).add (bounded_const 3)

include P in
 theorem allocated_cost_bounded (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) (A D : ℕ) :
    Bounded (measure V) (fun p => cost q p.1.arity (proofSize p.1) (sourceCircuitWord p.1).length
      (HonestAllocation.allocation (preparedHonestInput V) A D p)
      (HonestAllocation.allocation (preparedHonestInput V) A D p) (rowWidth V K e a p)) :=
  cost_bounded V proofSize honest K e P a hr _ _
    (HonestAllocation.bounded _ A D) (HonestAllocation.bounded _ A D)

include P in
 theorem sufficient_allocation (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) :
    ∃ A D : ℕ, 1 ≤ A ∧ ∀ p (coins : Fin (2 ^ (V p.1).randomBits)),
      Bounds V (fun r => K * ((proofCallInput V r).length + 1) ^ e) p.1 coins p.2.val (honest p)
        (HonestAllocation.allocation (preparedHonestInput V) A D p)
        (HonestAllocation.allocation (preparedHonestInput V) A D p)
        (HonestAllocation.allocation (preparedHonestInput V) A D p) (rowWidth V K e a p) := by
  obtain ⟨A, D, hA, hD⟩ := HonestAllocation.sufficient (preparedHonestInput V) (demand V K e a)
    (demand_bounded V K e a hr)
  exact ⟨A, D, hA, fun p coins => bounds_of_demand V proofSize honest K e P a hr p coins _ _ _ (hD p) (hD p) (hD p)⟩

end NearCubicGates.Adapters.Proximity.HonestRowTable
