import Proof.Packets.PacketsMetaPair
import Proof.Packets.PacketsPrimeCount
import Proof.Amplification.RecoveryTapeSupport

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
open NearCubicWires.SupplierPrime
noncomputable section

/-! ## The value of a stage is bounded by its cost -/

theorem UnaryStage.value_le {a : DecompositionAlgorithm} {v : Request → ℕ} (s : UnaryStage a v) (r : Request) :
    v r ≤ 2 * (Request.input a r).length + s.cost r + 2 := by
  obtain ⟨H', A', ⟨res, hres, _, ht, hs⟩, _, _, h1, _⟩ := s.run r
  have hsup := RecoveryTapeSupport.run_support s.machine (s.cost r) _ res hres
    (RepairOrdinary.frame (Request.input a r)).length 0 (fun _ => le_refl 0)
    (by
      intro i
      change (inBank (2 + s.extra) (Request.input a r) i).length ≤ _
      rw [inBank_val]
      split_ifs
      · exact le_max_left _ _
      · simp)
    ⟨1, by omega⟩
  rw [ht, h1, List.length_replicate, frame_length] at hsup
  omega

/-- The value as a fixed power of `smallSize`: `v + 3 ≤ (k + 7)·s^(d+1)`. -/
theorem UnaryStage.value_bound {a : DecompositionAlgorithm} {v : Request → ℕ} (s : UnaryStage a v) (r : Request) :
    v r + 3 ≤ (s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1) := by
  have h1 := s.value_le r
  have h2 := s.cost_le r
  have h3 := input_le_small a r
  have hs := one_le_small a r
  have p1 : (r.smallSize a) ^ s.degree ≤ (r.smallSize a) ^ (s.degree + 1) :=
    Nat.pow_le_pow_right hs (by omega)
  have p2 : r.smallSize a ≤ (r.smallSize a) ^ (s.degree + 1) := by
    calc r.smallSize a = (r.smallSize a) ^ 1 := (pow_one _).symm
      _ ≤ (r.smallSize a) ^ (s.degree + 1) := Nat.pow_le_pow_right hs (by omega)
  have p0 : 1 ≤ (r.smallSize a) ^ (s.degree + 1) := Nat.one_le_pow _ _ hs
  have q1 := Nat.mul_le_mul_left s.coefficient p1
  have e : (s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1) =
      s.coefficient * (r.smallSize a) ^ (s.degree + 1) + 2 * (r.smallSize a) ^ (s.degree + 1) +
        5 * (r.smallSize a) ^ (s.degree + 1) := by ring
  rw [e]
  omega

/-! ## The prime-count map -/

/-- **`π x` in unary** (`PrimeCount.machine` under the masked reset). -/
def primeCountMap : UnaryMap (fun x => PrimeCount.pc x) where
  extra := 3
  states := 21 + 2
  machine := MaskedReset.machine PrimeCount.machine (fun _ => true)
  cost := fun x => 2 * (6 * (x + 3) ^ 3 + 4) + 2
  run := by
    intro x
    obtain ⟨T, H1, A1, hs, hv, hT⟩ := PrimeCount.run x
    obtain ⟨k, hm⟩ := step_mask0 (hs.enlarge hT) (fun _ => true) (by intro i _; rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]
    · have hc : (⟨1, by omega⟩ : Fin (2 + 3)) = Fin.castAdd 1 (1 : Fin 4) := rfl
      rw [hc, Fin.addCases_left, hv]
    · have hc : (⟨1, by omega⟩ : Fin (2 + 3)) = Fin.castAdd 1 (1 : Fin 4) := rfl
      rw [hc, Fin.addCases_left]
      rfl

theorem pc_le (x : ℕ) : PrimeCount.pc x ≤ x := by
  induction x with
  | zero => simp [PrimeCount.pc]
  | succ c ih =>
    simp only [PrimeCount.pc]
    split_ifs <;> omega

/-! ## `max 1 x` -/

namespace OneMax

/-- Tapes 0 the argument, 1 the output (both heads move together). -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q b =>
    if q.val = 0 then some (if b 0 then ⟨1, ![none, some true], ![.right, .right]⟩
      else ⟨2, ![none, some true], ![.stay, .stay]⟩)
    else if q.val = 1 then some (if b 0 then ⟨1, ![none, some true], ![.right, .right]⟩
      else ⟨2, ![none, none], ![.stay, .stay]⟩)
    else none

def cfg (q : Fin 3) (x i o : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, i], ![List.replicate x true, List.replicate o true]⟩

theorem s0t (x : ℕ) (hx : 0 < x) : step machine (cfg 0 x 0 0) = some (cfg 1 x 1 1) := by
  have hr : readTapeBit (List.replicate x true) 0 = true := read_replicate_true x 0 hx
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end_replicate, writeTapeBit]

theorem s0f : step machine (cfg 0 0 0 0) = some (cfg 2 0 0 1) := by
  simp [step, machine, cfg, Configuration.scanned, readTapeBit]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, writeTapeBit]

theorem s1t (x i : ℕ) (hi : i < x) : step machine (cfg 1 x i i) = some (cfg 1 x (i + 1) (i + 1)) := by
  have hr : readTapeBit (List.replicate x true) i = true := read_replicate_true x i hi
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, write_end_replicate]

theorem s1f (x : ℕ) : step machine (cfg 1 x x x) = some (cfg 2 x x x) := by
  have hr : readTapeBit (List.replicate x true) x = false := read_replicate_end x true
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem copy (x : ℕ) : ∀ i, 1 ≤ i → i ≤ x → Timed machine (x - i) (cfg 1 x i i) (cfg 1 x x x) := by
  intro i hi hix
  induction h : x - i generalizing i with
  | zero =>
    have : i = x := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s1t x i (by omega))
    have t2 := ih (i + 1) (by omega) (by omega) (by omega)
    have t := t1.trans t2
    rw [show 1 + k = k + 1 by omega] at t
    exact t

theorem run (x : ℕ) : ∃ H, Step machine (x + 1) ![0, 0] ![List.replicate x true, []] H
    ![List.replicate x true, List.replicate (max 1 x) true] := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    have t := Timed.single (p := machine) (by simp [machine, cfg]) s0f
    obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
    refine ⟨_, r, ?_, rfl, by rw [hf]; rfl, by omega⟩
    have hc : (⟨machine.start, ![0, 0], ![List.replicate 0 true, []]⟩ : Configuration 2 3) = cfg 0 0 0 0 := rfl
    rw [hc]
    simpa using hr
  · have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s0t x hx)
    have t2 := copy x 1 (le_refl 1) hx
    have t3 := Timed.single (p := machine) (by simp [machine, cfg]) (s1f x)
    have t := (t1.trans t2).trans t3
    obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
    have hm : max 1 x = x := by omega
    refine ⟨_, r, ?_, rfl, by rw [hf, hm]; rfl, by omega⟩
    have hc : (⟨machine.start, ![0, 0], ![List.replicate x true, []]⟩ : Configuration 2 3) = cfg 0 x 0 0 := rfl
    rw [hc]
    have e : 1 + (x - 1) + 1 = x + 1 := by omega
    rw [e] at hr
    exact hr

end OneMax

/-- **`max 1 x` in unary.** -/
def max1Map : UnaryMap (fun x => max 1 x) where
  extra := 1
  states := 3 + 2
  machine := MaskedReset.machine OneMax.machine (fun _ => true)
  cost := fun x => 2 * (x + 1) + 2
  run := by
    intro x
    obtain ⟨H, hs⟩ := OneMax.run x
    obtain ⟨k, hm⟩ := step_mask0 hs (fun _ => true) (by intro i _; fin_cases i <;> rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp only [Fin.addCases_right]
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]
    · rfl
    · rfl

/-! ## The THR cutoff and the prime count -/

/-- AD's `cutoffStage` value: the THR prime cutoff, `0` otherwise. -/
def cutoffOf (a : DecompositionAlgorithm) : Request → ℕ
  | .thr r _ _ target => CloseoutFinalC10ThresholdRows.primeCutoff a r target
  | _ => 0

/-- The prime-index bound: `card (PrimeIndex cutoff)` for THR, `1` otherwise. -/
def primeCountOf (a : DecompositionAlgorithm) : Request → ℕ
  | .thr r _ _ target => Fintype.card (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target))
  | _ => 1

theorem primeCountOf_eq (a : DecompositionAlgorithm) (r : Request) :
    primeCountOf a r = max 1 (PrimeCount.pc (cutoffOf a r)) := by
  cases r with
  | terminal => simp [primeCountOf, cutoffOf, PrimeCount.pc]
  | sym r four L target => simp [primeCountOf, cutoffOf, PrimeCount.pc]
  | thr r four L target =>
    simp only [primeCountOf, cutoffOf]
    rw [Fintype.card_coe, ← PrimeCount.pc_eq]
    have h563 : 563 ≤ CloseoutFinalC10ThresholdRows.primeCutoff a r target := by
      unfold CloseoutFinalC10ThresholdRows.primeCutoff
      exact canonicalPrimeCutoff_ge_563 _ _
    have hpos : 1 ≤ (primesUpTo (CloseoutFinalC10ThresholdRows.primeCutoff a r target)).card :=
      Finset.card_pos.mpr ⟨2, mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩⟩
    rw [PrimeCount.pc_eq]
    omega

/-- **`primeCount` stage**, from AD's cutoff stage. -/
def primeCountStage (a : DecompositionAlgorithm) (cs : UnaryStage a (cutoffOf a)) :
    UnaryStage a (primeCountOf a) := by
  have h : primeCountOf a = fun r => max 1 (PrimeCount.pc (cutoffOf a r)) := funext (primeCountOf_eq a)
  rw [h]
  set K := cs.coefficient + 7
  set D := cs.degree + 1
  exact (cs.thenMap primeCountMap (12 * K ^ 3 + 10) (3 * D) (by
      intro r
      have hb : cutoffOf a r + 3 ≤ K * (r.smallSize a) ^ D := cs.value_bound r
      have hs := one_le_small a r
      have p0 : 1 ≤ (r.smallSize a) ^ (3 * D) := Nat.one_le_pow _ _ hs
      have hp : (cutoffOf a r + 3) ^ 3 ≤ (K * (r.smallSize a) ^ D) ^ 3 := Nat.pow_le_pow_left hb 3
      have e : (K * (r.smallSize a) ^ D) ^ 3 = K ^ 3 * (r.smallSize a) ^ (3 * D) := by ring
      change 2 * (6 * (cutoffOf a r + 3) ^ 3 + 4) + 2 ≤ _
      rw [e] at hp
      have e2 : (12 * K ^ 3 + 10) * (r.smallSize a) ^ (3 * D) =
          12 * (K ^ 3 * (r.smallSize a) ^ (3 * D)) + 10 * (r.smallSize a) ^ (3 * D) := by ring
      rw [e2]
      omega)).thenMap max1Map (2 * K + 4) D (by
      intro r
      have hb : cutoffOf a r + 3 ≤ K * (r.smallSize a) ^ D := cs.value_bound r
      have hs := one_le_small a r
      have p0 : 1 ≤ (r.smallSize a) ^ D := Nat.one_le_pow _ _ hs
      have hpc := pc_le (cutoffOf a r)
      change 2 * (PrimeCount.pc (cutoffOf a r) + 1) + 2 ≤ _
      have e2 : (2 * K + 4) * (r.smallSize a) ^ D = 2 * (K * (r.smallSize a) ^ D) + 4 * (r.smallSize a) ^ D := by
        ring
      rw [e2]
      omega)

end
end NearCubicWires.PacketsGlue.RequestMeta

