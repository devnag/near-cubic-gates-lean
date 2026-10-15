import Proof.Packets.PacketsGlueMetaMul

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
noncomputable section

/-- The upper bound: `smallSize` with each variable power `x^e` replaced by `2^(e·⌈log₂ x⌉)`. -/
def bigOf (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  r.q + (Request.input a r).length + twoK a r +
    2 ^ ((degree a r + 1) * Nat.clog 2 (pop a r + 2)) +
    2 ^ ((degree a r + 1) * Nat.clog 2 (alphabet a r)) +
    tupleWork a r + 2 ^ walkLength a r +
    2 ^ ((depth a r + 1) * Nat.clog 2 (pop a r + 2)) + 1

/-- The census exponent: `12·⌈log₂(U+1)⌉`. -/
def wOf (a : DecompositionAlgorithm) (r : Request) : ℕ := Nat.clog 2 (bigOf a r + 1) * 12

theorem pow_le_two_pow (x e : ℕ) : x ^ e ≤ 2 ^ (e * Nat.clog 2 x) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) x) e

theorem two_pow_le_sq (x e : ℕ) (hx : 2 ≤ x) : 2 ^ (e * Nat.clog 2 x) ≤ (x ^ e) ^ 2 := by
  rw [Nat.mul_comm, pow_mul]
  calc (2 ^ Nat.clog 2 x) ^ e ≤ (2 * x) ^ e :=
        Nat.pow_le_pow_left (SupplierWalkBridge.two_pow_clog_two_le_two_mul x (by omega)) e
    _ = 2 ^ e * x ^ e := mul_pow _ _ _
    _ ≤ x ^ e * x ^ e := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hx e)
    _ = (x ^ e) ^ 2 := by ring

theorem small_le_big (a : DecompositionAlgorithm) (r : Request) : r.smallSize a ≤ bigOf a r := by
  have h1 := pow_le_two_pow (pop a r + 2) (degree a r + 1)
  have h2 := pow_le_two_pow (alphabet a r) (degree a r + 1)
  have h3 := pow_le_two_pow (pop a r + 2) (depth a r + 1)
  have key : ∀ q n k x1 x2 x3 y1 y2 y3 t w : ℕ, x1 ≤ y1 → x2 ≤ y2 → x3 ≤ y3 →
      q + n + k + x1 + x2 + t + w + x3 + 1 ≤ q + n + k + y1 + y2 + t + w + y3 + 1 := by
    intros; omega
  unfold Request.smallSize bigOf
  exact key _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3

theorem occ_pow_le (a : DecompositionAlgorithm) (r : Request) : (pop a r + 2) ^ (degree a r + 1) ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, x2 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem alpha_pow_le (a : DecompositionAlgorithm) (r : Request) : (alphabet a r) ^ (degree a r + 1) ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, x3 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem depth_pow_le (a : DecompositionAlgorithm) (r : Request) : (pop a r + 2) ^ (depth a r + 1) ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, x6 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem walk_pow_le (a : DecompositionAlgorithm) (r : Request) : 2 ^ walkLength a r ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, x5 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem rest_le (a : DecompositionAlgorithm) (r : Request) :
    r.q + (Request.input a r).length + twoK a r + tupleWork a r + 2 ^ walkLength a r + 1 ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, q + n + x1 + x4 + x5 + 1 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by
    intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

theorem sq_le_small_sq {x s : ℕ} (h : x ≤ s) : x ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left h 2

theorem big_le (a : DecompositionAlgorithm) (r : Request) : bigOf a r ≤ 4 * (r.smallSize a) ^ 2 := by
  have hs := one_le_small a r
  have ha : 2 ≤ alphabet a r := by rw [alphabet_eq]; omega
  have p1 := (two_pow_le_sq (pop a r + 2) (degree a r + 1) (by omega)).trans (sq_le_small_sq (occ_pow_le a r))
  have p2 := (two_pow_le_sq (alphabet a r) (degree a r + 1) ha).trans (sq_le_small_sq (alpha_pow_le a r))
  have p3 := (two_pow_le_sq (pop a r + 2) (depth a r + 1) (by omega)).trans (sq_le_small_sq (depth_pow_le a r))
  have hr := rest_le a r
  have hss : r.smallSize a ≤ (r.smallSize a) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold bigOf
  omega

theorem one_le_big (a : DecompositionAlgorithm) (r : Request) : 1 ≤ bigOf a r := by
  unfold bigOf; exact Nat.le_add_left 1 _

/-- `census`: `smallSize^12 ≤ 2^w`. -/
theorem census (a : DecompositionAlgorithm) (r : Request) : (r.smallSize a) ^ 12 ≤ 2 ^ wOf a r := by
  unfold wOf
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  have h1 := small_le_big a r
  have h2 := Nat.le_pow_clog (b := 2) (by norm_num) (bigOf a r + 1)
  omega

theorem w_pos (a : DecompositionAlgorithm) (r : Request) : 1 ≤ wOf a r := by
  unfold wOf
  have h := one_le_big a r
  have : 1 ≤ Nat.clog 2 (bigOf a r + 1) := Nat.clog_pos (by norm_num) (by omega)
  omega

/-- `w_le`: `2^w ≤ 10^12·smallSize^24`. -/
theorem w_le (a : DecompositionAlgorithm) (r : Request) : 2 ^ wOf a r ≤ 10 ^ 12 * (r.smallSize a) ^ 24 := by
  unfold wOf
  rw [pow_mul]
  have h1 := big_le a r
  have hs := one_le_small a r
  have hss : 1 ≤ (r.smallSize a) ^ 2 := Nat.one_le_pow _ _ hs
  have h2 := SupplierWalkBridge.two_pow_clog_two_le_two_mul (bigOf a r + 1) (by omega)
  have h3 : 2 ^ Nat.clog 2 (bigOf a r + 1) ≤ 10 * (r.smallSize a) ^ 2 := by omega
  calc (2 ^ Nat.clog 2 (bigOf a r + 1)) ^ 12 ≤ (10 * (r.smallSize a) ^ 2) ^ 12 := Nat.pow_le_pow_left h3 12
    _ = 10 ^ 12 * (r.smallSize a) ^ 24 := by ring

/-! ## The stages -/

theorem pow_cost_sq (y s : ℕ) (hy : 2 ^ y ≤ s ^ 2) (hs : 1 ≤ s) :
    RepairSource.CloseoutCapacity.Power.budget y ≤ 800 * s ^ 4 := by
  have h := power_budget_le y
  have hs2 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
  have h1 : 2 ^ y + 1 ≤ 2 * s ^ 2 := by omega
  have h2 : (2 ^ y + 1) ^ 2 ≤ (2 * s ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
  calc RepairSource.CloseoutCapacity.Power.budget y ≤ 200 * (2 ^ y + 1) ^ 2 := h
    _ ≤ 200 * (2 * s ^ 2) ^ 2 := Nat.mul_le_mul_left _ h2
    _ = 800 * s ^ 4 := by ring

/-- **The `U` stage**, from the typed inputs `q`, `degree`, `tupleWork`, `walkLength`. -/
def bigStage (a : DecompositionAlgorithm) (qS : UnaryStage a (fun r => r.q)) (degS : UnaryStage a (degree a))
    (tupS : UnaryStage a (tupleWork a)) (walkS : UnaryStage a (walkLength a)) : UnaryStage a (bigOf a) :=
  let e1 := degS.thenMapP (plusMap 1) 6 1 (plus_cost 1)
  let cP := ((popStage a).thenMapP (plusMap 2) 8 1 (plus_cost 2)).thenMapP clogMap 62 1 clog_cost
  let cA := (alphabetStage a).thenMapP clogMap 62 1 clog_cost
  let eD := (depthStage a).thenMapP (plusMap 1) 6 1 (plus_cost 1)
  let p1 := (e1.pairP cP mulMap2 8 2 mul_cost).thenMap powMap 800 4 (by
    intro r
    have hs := one_le_small a r
    change RepairSource.CloseoutCapacity.Power.budget ((degree a r + 1) * Nat.clog 2 (pop a r + 2)) ≤ _
    exact pow_cost_sq _ _ ((two_pow_le_sq (pop a r + 2) (degree a r + 1) (by omega)).trans
      (sq_le_small_sq (occ_pow_le a r))) hs)
  let p2 := (e1.pairP cA mulMap2 8 2 mul_cost).thenMap powMap 800 4 (by
    intro r
    have hs := one_le_small a r
    have ha : 2 ≤ alphabet a r := by rw [alphabet_eq]; omega
    change RepairSource.CloseoutCapacity.Power.budget ((degree a r + 1) * Nat.clog 2 (alphabet a r)) ≤ _
    exact pow_cost_sq _ _ ((two_pow_le_sq (alphabet a r) (degree a r + 1) ha).trans
      (sq_le_small_sq (alpha_pow_le a r))) hs)
  let p3 := (eD.pairP cP mulMap2 8 2 mul_cost).thenMap powMap 800 4 (by
    intro r
    have hs := one_le_small a r
    change RepairSource.CloseoutCapacity.Power.budget ((depth a r + 1) * Nat.clog 2 (pop a r + 2)) ≤ _
    exact pow_cost_sq _ _ ((two_pow_le_sq (pop a r + 2) (depth a r + 1) (by omega)).trans
      (sq_le_small_sq (depth_pow_le a r))) hs)
  let pw := walkS.thenMap powMap 800 4 (by
    intro r
    have hs := one_le_small a r
    have hw := walk_pow_le a r
    have hss : r.smallSize a ≤ (r.smallSize a) ^ 2 := Nat.le_self_pow (by norm_num) _
    change RepairSource.CloseoutCapacity.Power.budget (walkLength a r) ≤ _
    exact pow_cost_sq _ _ (hw.trans hss) hs)
  let s1 := qS.pairP (inputLenStage a) addMap2 6 1 add_cost
  let s2 := s1.pairP (twoKStage a) addMap2 6 1 add_cost
  let s3 := s2.pairP p1 addMap2 6 1 add_cost
  let s4 := s3.pairP p2 addMap2 6 1 add_cost
  let s5 := s4.pairP tupS addMap2 6 1 add_cost
  let s6 := s5.pairP pw addMap2 6 1 add_cost
  let s7 := s6.pairP p3 addMap2 6 1 add_cost
  s7.thenMapP (plusMap 1) 6 1 (plus_cost 1)

/-- **The census-exponent stage** `w = 12·⌈log₂(U+1)⌉`. -/
def wStage (a : DecompositionAlgorithm) (qS : UnaryStage a (fun r => r.q)) (degS : UnaryStage a (degree a))
    (tupS : UnaryStage a (tupleWork a)) (walkS : UnaryStage a (walkLength a)) : UnaryStage a (wOf a) :=
  (((bigStage a qS degS tupS walkS).thenMapP (plusMap 1) 6 1 (plus_cost 1)).thenMapP clogMap 62 1
    clog_cost).thenMapP (scaleMap 12) (4 * 12 + 12) 2 (scale_cost 12)

end
end NearCubicWires.PacketsGlue.RequestMeta

