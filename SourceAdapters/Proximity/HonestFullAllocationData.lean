import SourceAdapters.Proximity.HonestPreparedGrowth
import SourceAdapters.Proximity.HonestCoinSetupGrowth
import SourceAdapters.Proximity.HonestRowTableGrowth
import Proof.Gates.Worker.Format

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": all numerical conditions for the complete honest
producer. Arbitrary source proof addresses are bounded by their serialized bit
width; auxiliary paired keys and the number of retained addresses are polynomial. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestFullAllocation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins Growth
open HonestPreparationSizes (measure)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)) (K e a : ℕ)

def demand (p : AcceptedSourceInput) : ℕ :=
  HonestPrepared.initialDemand V proofSize K e p + HonestCoinSetup.demand V K e p +
    HonestRowTable.demand V K e a p + 2 ^ (V p.1).randomBits + (q + blockVariableBound q) +
    2 ^ (V p.1).randomBits * blockVariableBound q + SourceCallee.auxiliaryCap q (V p.1).randomBits +
    p.1.arity + (trimSortedAddresses (clauseTrimRequest V p.1)).length + 1

structure AllBounds (p : AcceptedSourceInput) (Wd Lk Bk : ℕ) : Prop where
  initial : (preparedHonestInput V p).length + 3 ≤ Wd ∧ q < 2 ^ Wd ∧ 2 ^ q < 2 ^ Wd ∧
    blockVariableBound q < 2 ^ Wd ∧ proofSize p.1 < 2 ^ Wd ∧
    2 + (sourceCircuitWord p.1).length + p.1.arity ≤ Lk ∧
    K * ((proofCallInput V (HonestSource.request V p)).length + 1) ^ e ≤ Bk
  coin : 4 ≤ 2 ^ Wd ∧ (proofCallInput V (SourceCallee.randomRequest V p.1)).length ≤ Lk ∧
    K * ((proofCallInput V (SourceCallee.randomRequest V p.1)).length + 1) ^ e ≤ Bk ∧
    (V p.1).randomBits.bits.length + 1 ≤ Wd ∧ (V p.1).randomBits < Wd ∧
    (V p.1).randomBits + predicateBlockBits q < 2 ^ Wd
  rows : ∀ coins : Fin (2 ^ (V p.1).randomBits),
    HonestRowTable.Bounds V (fun r => K * ((proofCallInput V r).length + 1) ^ e)
      p.1 coins p.2.val (honest p) Wd Lk Bk (HonestRowTable.rowWidth V K e a p)
  input_width : p.1.arity < 2 ^ Wd
  coin_width : 2 ^ (V p.1).randomBits < 2 ^ Wd
  local_sum_width : q + blockVariableBound q < 2 ^ Wd
  auxiliary_count_width : 2 ^ (V p.1).randomBits * blockVariableBound q < 2 ^ Wd
  key_width : ∀ row < 2 ^ (V p.1).randomBits, ∀ i < blockVariableBound q,
    2 * Nat.pair row i + 1 < 2 ^ Wd
  schedule_count_width : (trimSortedAddresses (clauseTrimRequest V p.1)).length < 2 ^ Wd
  schedule_value_width : ∀ x ∈ trimSortedAddresses (clauseTrimRequest V p.1), x < 2 ^ Wd

theorem schedule_value_width (p : AcceptedSourceInput) (Wd : ℕ)
    (hw : (preparedHonestInput V p).length ≤ Wd)
    (x : ℕ) (hx : x ∈ trimSortedAddresses (clauseTrimRequest V p.1)) : x < 2 ^ Wd := by
  have h := (HonestPrepared.word_bounds (sourceCircuitWord p.1) (List.ofFn p.2.val)
    (trimSortedAddresses (clauseTrimRequest V p.1))).2.2.2.2.2 x hx
  rw [HonestPrepared.word_prepared V p] at h
  exact (NearCubicGates.Close.Worker.Format.lt_two_pow_natBitLength x).trans_le
    (Nat.pow_le_pow_right (by decide) (h.trans hw))

theorem odd_key_le (r row i : ℕ) (hrow : row < 2 ^ r) (hi : i < blockVariableBound q) :
    2 * Nat.pair row i + 1 ≤ SourceCallee.auxiliaryCap q r := by
  have hp := Nat.pair_lt_max_add_one_sq row i
  have hm : max row i + 1 ≤ 2 ^ r + blockVariableBound q + 1 := by omega
  have hs := Nat.pow_le_pow_left hm 2
  unfold SourceCallee.auxiliaryCap
  omega

end NearCubicGates.Adapters.Proximity.HonestFullAllocation
