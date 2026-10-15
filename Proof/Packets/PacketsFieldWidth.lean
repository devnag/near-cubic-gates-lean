import Proof.Packets.PacketsMetaWord
import Proof.Packets.PacketsPrimeService

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.BitAt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

/-- Read tape 0 at cell `p`; write one `true` on tape 1 iff the bit equals `b`. -/
def machine (p : ℕ) (b : Bool) : Machine 2 (p + 2) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == p + 1
  rule := fun q x =>
    if h : q.val < p then some ⟨⟨q.val + 1, by omega⟩, ![none, none], ![.right, .stay]⟩
    else if q.val = p then
      some (if x 0 = b then ⟨⟨p + 1, by omega⟩, ![none, some true], ![.stay, .stay]⟩
        else ⟨⟨p + 1, by omega⟩, ![none, none], ![.stay, .stay]⟩)
    else none

def cfg (p : ℕ) (q : Fin (p + 2)) (w : List Bool) (i : ℕ) (o : List Bool) : Configuration 2 (p + 2) :=
  ⟨q, ![i, 0], ![w, o]⟩

theorem s_move (p : ℕ) (b : Bool) (w : List Bool) (k : ℕ) (hk : k < p) :
    step (machine p b) (cfg p ⟨k, by omega⟩ w k []) = some (cfg p ⟨k + 1, by omega⟩ w (k + 1) []) := by
  simp [step, machine, cfg, hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s_hit (p : ℕ) (b : Bool) (w : List Bool) (h : readTapeBit w p = b) :
    step (machine p b) (cfg p ⟨p, by omega⟩ w p []) = some (cfg p ⟨p + 1, by omega⟩ w p [true]) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, writeTapeBit]

theorem s_miss (p : ℕ) (b : Bool) (w : List Bool) (h : readTapeBit w p ≠ b) :
    step (machine p b) (cfg p ⟨p, by omega⟩ w p []) = some (cfg p ⟨p + 1, by omega⟩ w p []) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem walk (p : ℕ) (b : Bool) (w : List Bool) : ∀ k (hk : k ≤ p),
    Timed (machine p b) k (cfg p ⟨0, by omega⟩ w 0 []) (cfg p ⟨k, by omega⟩ w k []) := by
  intro k
  induction k with
  | zero => intro _; exact Timed.refl _ _
  | succ k ih =>
    intro hk
    have t1 := ih (by omega)
    have t2 := Timed.single (p := machine p b) (by simp [machine, cfg]; omega) (s_move p b w k (by omega))
    exact t1.trans t2

/-- **The bit test**: tape 1 ends as `replicate (if w[p] = b then 1 else 0) true`. -/
theorem run (p : ℕ) (b : Bool) (w : List Bool) : ∃ H, Step (machine p b) (p + 1) ![0, 0] ![w, []] H
    ![w, List.replicate (if readTapeBit w p = b then 1 else 0) true] := by
  have t1 := walk p b w p (le_refl p)
  by_cases h : readTapeBit w p = b
  · have t2 := Timed.single (p := machine p b) (by simp [machine, cfg]) (s_hit p b w h)
    obtain ⟨r, hr, hf, hs⟩ := (t1.trans t2).run (by simp [machine, cfg])
    refine ⟨_, r, ?_, rfl, ?_, by omega⟩
    · have hc : (⟨(machine p b).start, ![0, 0], ![w, []]⟩ : Configuration 2 (p + 2)) =
          cfg p ⟨0, by omega⟩ w 0 [] := rfl
      rw [hc]; exact hr
    · rw [hf, if_pos h]; rfl
  · have t2 := Timed.single (p := machine p b) (by simp [machine, cfg]) (s_miss p b w h)
    obtain ⟨r, hr, hf, hs⟩ := (t1.trans t2).run (by simp [machine, cfg])
    refine ⟨_, r, ?_, rfl, ?_, by omega⟩
    · have hc : (⟨(machine p b).start, ![0, 0], ![w, []]⟩ : Configuration 2 (p + 2)) =
          cfg p ⟨0, by omega⟩ w 0 [] := rfl
      rw [hc]; exact hr
    · rw [hf, if_neg h]; rfl

end NearCubicWires.PacketsGlue.BitAt

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
noncomputable section

/-! ## The values -/

/-- `1` off the terminal sentinel. -/
def liveFlag : Request → ℕ
  | .terminal => 0
  | .sym _ _ _ _ => 1
  | .thr _ _ _ _ => 1

/-- `1` for a THR request. -/
def thrFlag : Request → ℕ
  | .terminal => 0
  | .sym _ _ _ _ => 0
  | .thr _ _ _ _ => 1

/-- The coordinate-level sum of `digitBound`: SYM `Σ (bottomCount + 1)`, THR `Σ |children|`. -/
def coordSum (a : DecompositionAlgorithm) : Request → ℕ
  | .terminal => 0
  | .sym r _ _ _ => ∑ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount + 1)
  | .thr r _ _ _ => ∑ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length

theorem digitBound_eq (a : DecompositionAlgorithm) (r : Request) :
    PacketsConstruction.digitBound a r =
      liveFlag r * seedCount a r + coordSum a r + PrimeCount.pc (cutoffOf a r) + cutoffOf a r + 2 := by
  cases r with
  | terminal => simp [PacketsConstruction.digitBound, liveFlag, coordSum, cutoffOf, PrimeCount.pc]
  | sym r four L target =>
    simp only [PacketsConstruction.digitBound, liveFlag, coordSum, cutoffOf, PrimeCount.pc, one_mul]
    rfl
  | thr r four L target =>
    simp only [PacketsConstruction.digitBound, liveFlag, coordSum, cutoffOf, one_mul, card_primeIndex]
    rfl

theorem log_succ_eq_clog (n : ℕ) (hn : 1 ≤ n) : Nat.log 2 n + 1 = Nat.clog 2 (n + 1) := by
  apply le_antisymm
  · by_contra hc
    have hle : Nat.clog 2 (n + 1) ≤ Nat.log 2 n := by omega
    rw [Nat.clog_le_iff_le_pow (by norm_num)] at hle
    have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    omega
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem fieldWidth_eq (a : DecompositionAlgorithm) (r : Request) :
    fieldWidth a r = Nat.clog 2 (PacketsConstruction.digitBound a r + 1) := by
  change Nat.log 2 (PacketsConstruction.digitBound a r) + 1 = _
  exact log_succ_eq_clog _ (by have := PacketsConstruction.two_le_bound a r; omega)

/-! ## The kind bits of `nativeWord` -/

theorem frame_odd (w : List Bool) : ∀ j, readTapeBit (RepairOrdinary.frame w) (2 * j + 1) = w.getD j false := by
  induction w with
  | nil => intro j; simp [RepairOrdinary.frame, readTapeBit]
  | cons b bs ih =>
    intro j
    cases j with
    | zero => simp [RepairOrdinary.frame, readTapeBit]
    | succ j =>
      have := ih j
      simp only [RepairOrdinary.frame, readTapeBit] at this ⊢
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega]
      simpa using this

theorem natWord_zero : natWord 0 = [true, false, false] := by
  simp [natWord, NearCubicWires.WilliamsPublishedForm.framedNatBits, natBitLength,
    NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits, List.ofFn_succ]

theorem natWord_one : natWord 1 = [true, false, true] := by
  simp [natWord, NearCubicWires.WilliamsPublishedForm.framedNatBits, natBitLength,
    NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits, List.ofFn_succ]

theorem natWord_two : natWord 2 = [true, true, false, false, true] := by
  have h : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h2 : Nat.testBit 2 1 = true := by decide
  simp [natWord, NearCubicWires.WilliamsPublishedForm.framedNatBits, natBitLength,
    NearCubicWires.WilliamsPublishedForm.fixedWidthNatBits, h, h2, List.ofFn_succ]

theorem getD_append_left (u v : List Bool) (j : ℕ) (h : j < u.length) : (u ++ v).getD j false = u.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem native_bit1 (r : Request) : readTapeBit (RepairOrdinary.frame r.nativeWord) 3 = decide (liveFlag r = 0) := by
  have e := frame_odd r.nativeWord 1
  simp only [show 2 * 1 + 1 = 3 by rfl] at e
  rw [e]
  cases r with
  | terminal => simp [Request.nativeWord, natWord_two, liveFlag]
  | sym r four L target =>
    simp only [Request.nativeWord, List.append_assoc]
    rw [getD_append_left _ _ _ (by rw [natWord_zero]; simp), natWord_zero]
    simp [liveFlag]
  | thr r four L target =>
    simp only [Request.nativeWord, List.append_assoc]
    rw [getD_append_left _ _ _ (by rw [natWord_one]; simp), natWord_one]
    simp [liveFlag]

theorem native_bit2 (r : Request) : readTapeBit (RepairOrdinary.frame r.nativeWord) 5 = decide (thrFlag r = 1) := by
  have e := frame_odd r.nativeWord 2
  simp only [show 2 * 2 + 1 = 5 by rfl] at e
  rw [e]
  cases r with
  | terminal => simp [Request.nativeWord, natWord_two, thrFlag]
  | sym r four L target =>
    simp only [Request.nativeWord, List.append_assoc]
    rw [getD_append_left _ _ _ (by rw [natWord_zero]; simp), natWord_zero]
    simp [thrFlag]
  | thr r four L target =>
    simp only [Request.nativeWord, List.append_assoc]
    rw [getD_append_left _ _ _ (by rw [natWord_one]; simp), natWord_one]
    simp [thrFlag]

theorem liveFlag_le (r : Request) : liveFlag r ≤ 1 := by cases r <;> simp [liveFlag]
theorem thrFlag_le (r : Request) : thrFlag r ≤ 1 := by cases r <;> simp [thrFlag]

theorem heads0_2 : (![0, 0] : Fin 2 → ℕ) = fun _ => 0 := by
  funext i; fin_cases i <;> rfl

/-- A kind-bit stage from the bit test on field 0. -/
def bitStage (a : DecompositionAlgorithm) (p : ℕ) (b : Bool) (v : Request → ℕ)
    (hv : ∀ r, (if readTapeBit (RepairOrdinary.frame (fields a r 0)) p = b then 1 else 0) = v r) :
    UnaryStage a v where
  extra := 13 + 0 + 1
  states := _
  machine := fieldMachineE (BitAt.machine p b) 0
  cost := fun r => 6 * (r.input a).length + 17 + 1 + (2 * (p + 1) + 2)
  coefficient := 2 * p + 40
  degree := 1
  cost_le := by
    intro r
    have h := input_le_small a r
    rw [pow_one]
    nlinarith
  run := by
    intro r
    obtain ⟨H, hs⟩ := BitAt.run p b (RepairOrdinary.frame (fields a r 0))
    have hs' : Step (BitAt.machine p b) (p + 1) (fun _ => 0) (scanIn 0 (frame (fields a r 0))) H
        ![RepairOrdinary.frame (fields a r 0), List.replicate (v r) true] := by
      have e : scanIn 0 (frame (fields a r 0)) = ![RepairOrdinary.frame (fields a r 0), []] := by
        funext i; fin_cases i <;> rfl
      rw [e, ← heads0_2, ← hv r]
      exact hs
    exact field_runE (e := 0) (BitAt.machine p b) 0 a r (v r) _ H _ hs' rfl

/-- **The not-terminal flag.** -/
def liveFlagStage (a : DecompositionAlgorithm) : UnaryStage a (fun r => liveFlag r) :=
  bitStage a 3 false (fun r => liveFlag r) (by
    intro r
    have e : fields a r 0 = r.nativeWord := rfl
    rw [e, native_bit1]
    have := liveFlag_le r
    rcases (show liveFlag r = 0 ∨ liveFlag r = 1 by omega) with h | h <;> simp [h])

/-- **The THR flag.** -/
def thrFlagStage (a : DecompositionAlgorithm) : UnaryStage a (fun r => thrFlag r) :=
  bitStage a 5 true (fun r => thrFlag r) (by
    intro r
    have e : fields a r 0 = r.nativeWord := rfl
    rw [e, native_bit2]
    have := thrFlag_le r
    rcases (show thrFlag r = 0 ∨ thrFlag r = 1 by omega) with h | h <;> simp [h])

/-! ## The field width -/

theorem pc_cost (x : ℕ) : primeCountMap.cost x ≤ 14 * (x + 3) ^ 3 := by
  change 2 * (6 * (x + 3) ^ 3 + 4) + 2 ≤ _
  have := cube_ge x
  omega

/-- **`fieldWidth` stage**, from the typed inputs `seedCount`, `coordSum`, `cutoffOf`. -/
def fieldWidthStage (a : DecompositionAlgorithm) (seedS : UnaryStage a (seedCount a))
    (coordS : UnaryStage a (coordSum a)) (cutS : UnaryStage a (cutoffOf a)) :
    UnaryStage a (fieldWidth a) := by
  have h : fieldWidth a = fun r => Nat.clog 2
      (liveFlag r * seedCount a r + coordSum a r + PrimeCount.pc (cutoffOf a r) + cutoffOf a r + 3) := by
    funext r
    rw [fieldWidth_eq, digitBound_eq]
  rw [h]
  exact (((((((liveFlagStage a).pairP seedS mulMap2 8 2 mul_cost).pairP coordS addMap2 6 1 add_cost).pairP
    (cutS.thenMapP primeCountMap 14 3 pc_cost) addMap2 6 1 add_cost).pairP cutS addMap2 6 1 add_cost).thenMapP
    (plusMap 3) 10 1 (plus_cost 3)).thenMapP clogMap 62 1 clog_cost)

end
end NearCubicWires.PacketsGlue.RequestMeta

