import Proof.Gates.Recovery.AfterParts2
import Proof.Gates.Recovery.AfterStageCost

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.ENP

/-- **Stage workspace and cost from the final address** (paper §11.6, formulas of size `2^{O(q)}`, `q ≤ n`). -/
theorem stageBudget (d : ℕ) : StageBudget d := by
  obtain ⟨Kn, en, hn⟩ := uNeedPoly d
  obtain ⟨Kc, ec, hc⟩ := uCostPoly d
  refine ⟨en, en + Kn, Kc * 2 ^ ((en + Kn + 1) * ec), en * ec, fun n w R vals hw m x hRn hlen => ?_⟩
  have hneed := hn w R vals hw hlen
  have hcapge : Kn * (2 ^ R + 1) ^ en ≤ CloseoutCapacity.capacity en (en + Kn) n := by
    unfold CloseoutCapacity.capacity
    have h1 : Kn ≤ 2 ^ Kn := Nat.lt_two_pow_self.le
    have h2 : (2 ^ R + 1) ^ en ≤ (2 ^ (R + 1)) ^ en :=
      Nat.pow_le_pow_left (by rw [pow_succ]; have := Nat.one_le_two_pow (n := R); omega) _
    calc Kn * (2 ^ R + 1) ^ en ≤ 2 ^ Kn * (2 ^ (R + 1)) ^ en := Nat.mul_le_mul h1 h2
      _ = 2 ^ (Kn + (R + 1) * en) := by rw [← pow_mul, ← pow_add, Nat.mul_comm (R + 1) en]
      _ ≤ 2 ^ (en * n + (en + Kn)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hall := hneed.trans hcapge
  have h1 : originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤
      CloseoutCapacity.capacity en (en + Kn) n :=
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hall)
  have h2 : (DedupBytes.fields (unitPCP w vals)).length ≤ CloseoutCapacity.capacity en (en + Kn) n :=
    (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans hall)
  have h3 : 2 ^ R ≤ CloseoutCapacity.capacity en (en + Kn) n := (Nat.le_add_left _ _).trans hall
  refine ⟨h1, h2, h3, fun hb => ?_⟩
  refine (hc w R (CloseoutCapacity.capacity en (en + Kn) n) vals hw x hlen hb h1 h2 h3).trans ?_
  have hW : CloseoutCapacity.capacity en (en + Kn) n + 1 ≤ (2 ^ n) ^ en * 2 ^ (en + Kn + 1) := by
    unfold CloseoutCapacity.capacity
    have : (2 ^ n) ^ en * 2 ^ (en + Kn + 1) = 2 * 2 ^ (en * n + (en + Kn)) := by
      rw [← pow_mul, ← pow_add, ← pow_succ']; congr 1; ring
    rw [this]
    have := Nat.one_le_two_pow (n := en * n + (en + Kn))
    omega
  have hpow : (CloseoutCapacity.capacity en (en + Kn) n + 1) ^ ec ≤
      2 ^ ((en + Kn + 1) * ec) * (2 ^ n + 1) ^ (en * ec) := by
    calc (CloseoutCapacity.capacity en (en + Kn) n + 1) ^ ec ≤ ((2 ^ n) ^ en * 2 ^ (en + Kn + 1)) ^ ec :=
          Nat.pow_le_pow_left hW _
      _ = 2 ^ ((en + Kn + 1) * ec) * (2 ^ n) ^ (en * ec) := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring
      _ ≤ 2 ^ ((en + Kn + 1) * ec) * (2 ^ n + 1) ^ (en * ec) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  calc Kc * (CloseoutCapacity.capacity en (en + Kn) n + 1) ^ ec ≤
        Kc * (2 ^ ((en + Kn + 1) * ec) * (2 ^ n + 1) ^ (en * ec)) := Nat.mul_le_mul_left _ hpow
    _ = Kc * 2 ^ ((en + Kn + 1) * ec) * (2 ^ n + 1) ^ (en * ec) := by ring

end NearCubicGates.Close.Recovery.After
