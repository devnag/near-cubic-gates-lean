import SourceAdapters.Proximity.HonestFullAllocation
import SourceAdapters.Proximity.TrimHonestLoopData

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the sum of actual initializer, coin, row-loop and
restriction clocks is polynomial under the single paid-prefix allocation. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestFullAllocation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins Growth
open HonestPreparationSizes (measure)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)) (K e a : ℕ)

def outputCost (p : AcceptedSourceInput) : ℕ :=
  (trimSortedAddresses (clauseTrimRequest V p.1)).length +
    (6 * proofSize p.1 + 16 * (TrimHonest.auxKeys (2 ^ (V p.1).randomBits) (blockVariableBound q)).length + 38) *
      (trimSortedAddresses (clauseTrimRequest V p.1)).length + 6

def cost (p : AcceptedSourceInput) (Lk Bk : ℕ) : ℕ :=
  HonestPrepared.initialCost V proofSize p Lk Bk +
  HonestCoinSetup.cost q (V p.1).randomBits (sourceCircuitWord p.1).length Lk Bk +
  (2 ^ (V p.1).randomBits * (TrimHonest.rowCost q p.1.arity (proofSize p.1)
    (sourceCircuitWord p.1).length Lk Bk (HonestRowTable.rowWidth V K e a p) + 4) + 4) +
  outputCost V proofSize p + 3

variable
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest)
      (fun r => K * ((proofCallInput V r).length + 1) ^ e))
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))

include P hr

theorem output_cost_bounded : Bounded (measure V) (outputCost V proofSize) := by
  have hR := HonestPreparationSizes.coins_bounded V a hr
  have hp := HonestPreparationSizes.proof_size_bounded V proofSize honest K e P
  have hs := HonestPreparationSizes.schedule_bounded V
  have haux : Bounded (measure V) (fun p =>
      (TrimHonest.auxKeys (2 ^ (V p.1).randomBits) (blockVariableBound q)).length) := by
    simpa only [TrimHonest.auxKeys_length] using hR.mul (bounded_const (blockVariableBound q))
  have hlookup := (((bounded_const 6).mul hp).add ((bounded_const 16).mul haux)).add (bounded_const 38)
  exact (hs.add (hlookup.mul hs)).add (bounded_const 6)

theorem cost_bounded (Lk Bk : AcceptedSourceInput → ℕ)
    (hL : Bounded (measure V) Lk) (hB : Bounded (measure V) Bk) :
    Bounded (measure V) (fun p => cost V proofSize K e a p (Lk p) (Bk p)) := by
  have hi := HonestPrepared.initial_cost_bounded V proofSize honest K e P Lk Bk hL hB
  have hc := HonestCoinSetup.cost_bounded V a hr Lk Bk hL hB
  have hrow := HonestRowTable.cost_bounded V proofSize honest K e P a hr Lk Bk hL hB
  have hrowFull : Bounded (measure V) (fun p => TrimHonest.rowCost q p.1.arity (proofSize p.1)
      (sourceCircuitWord p.1).length (Lk p) (Bk p) (HonestRowTable.rowWidth V K e a p)) :=
    (hrow.add (bounded_const (6 * (blockVariableBound q) ^ 2 + 40 * blockVariableBound q + 11))).add (bounded_const 1)
  have hR := HonestPreparationSizes.coins_bounded V a hr
  have hloop := (hR.mul (hrowFull.add (bounded_const 4))).add (bounded_const 4)
  have ho := output_cost_bounded V proofSize honest K e a P hr
  exact (((hi.add hc).add hloop).add ho).add (bounded_const 3)

theorem allocated_cost_bounded (A D : ℕ) :
    Bounded (measure V) (fun p => cost V proofSize K e a p
      (HonestAllocation.allocation (preparedHonestInput V) A D p)
      (HonestAllocation.allocation (preparedHonestInput V) A D p)) :=
  cost_bounded V proofSize honest K e a P hr _ _
    (HonestAllocation.bounded _ A D) (HonestAllocation.bounded _ A D)

end NearCubicGates.Adapters.Proximity.HonestFullAllocation
