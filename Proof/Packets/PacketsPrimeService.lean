import Proof.Packets.PacketsGlueMetaMul
import Proof.Packets.PacketsPrimeSum
import Proof.Packets.PacketsPrimeIdx

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
open NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
noncomputable section

/-! ## The prime index is the count of smaller primes -/

theorem card_primeIndex (c : ℕ) : Fintype.card (PrimeIndex c) = PrimeCount.pc c := by
  rw [Fintype.card_coe, PrimeCount.pc_eq]

/-- The increasing enumeration: the index of the prime `x ≤ c` is the number of primes below it. -/
theorem idx_eq_count (c : ℕ) (x : PrimeIndex c) :
    ((primeIndexFinEquiv c) x).val = PrimeCount.pc (x.val - 1) := by
  have he : (primeIndexFinEquiv c) x =
      (Fintype.orderIsoFinOfCardEq (PrimeIndex c) (rfl : Fintype.card (PrimeIndex c) = _)).symm x := rfl
  rw [he]
  set e := Fintype.orderIsoFinOfCardEq (PrimeIndex c) (rfl : Fintype.card (PrimeIndex c) = _)
  have h1 : (Finset.univ.filter (fun y : PrimeIndex c => y < x)) =
      (Finset.Iio (e.symm x)).map e.toEquiv.toEmbedding := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Iio]
    constructor
    · intro hy
      refine ⟨e.symm y, e.symm.lt_iff_lt.mpr hy, ?_⟩
      simp
    · rintro ⟨i, hi, rfl⟩
      have h := e.lt_iff_lt.mpr hi
      simpa using h
  have h2 : (Finset.univ.filter (fun y : PrimeIndex c => y < x)).card = (e.symm x).val := by
    rw [h1, Finset.card_map, Fin.card_Iio]
  have hx := mem_primesUpTo.mp x.property
  have hx2 := hx.1.two_le
  have hmap : (Finset.univ.filter (fun y : PrimeIndex c => y < x)).map (Function.Embedding.subtype _) =
      primesUpTo (x.val - 1) := by
    ext q
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' := mem_primesUpTo.mp y.property
      have hlt : y.val < x.val := hy
      exact mem_primesUpTo.mpr ⟨hy'.1, by omega⟩
    · intro hq
      have hq' := mem_primesUpTo.mp hq
      refine ⟨⟨q, mem_primesUpTo.mpr ⟨hq'.1, by omega⟩⟩, ?_, rfl⟩
      show q < x.val
      omega
  have h3 : (Finset.univ.filter (fun y : PrimeIndex c => y < x)).card = PrimeCount.pc (x.val - 1) := by
    rw [PrimeCount.pc_eq, ← hmap, Finset.card_map]
  omega

/-- A prime `v ≤ c` sits at index `π (v - 1)`. -/
theorem primeAt_of_count (c v : ℕ) (hv : v.Prime) (hvc : v ≤ c) :
    primeAt c (PrimeCount.pc (v - 1)) = v := by
  have hx := idx_eq_count c ⟨v, mem_primesUpTo.mpr ⟨hv, hvc⟩⟩
  have hlt : PrimeCount.pc (v - 1) < Fintype.card (PrimeIndex c) := by
    rw [← hx]; exact ((primeIndexFinEquiv c) ⟨v, mem_primesUpTo.mpr ⟨hv, hvc⟩⟩).isLt
  unfold primeAt
  rw [dif_pos hlt]
  have e : (⟨PrimeCount.pc (v - 1), hlt⟩ : Fin (Fintype.card (PrimeIndex c))) =
      (primeIndexFinEquiv c) ⟨v, mem_primesUpTo.mpr ⟨hv, hvc⟩⟩ := Fin.ext hx.symm
  rw [e, Equiv.symm_apply_apply]

/-- Off range, `primeAt` is `1`. -/
theorem primeAt_off (c u : ℕ) (h : PrimeCount.pc c ≤ u) : primeAt c u = 1 := by
  unfold primeAt
  rw [dif_neg (by rw [card_primeIndex]; omega)]

/-- In range, `primeAt c u` is a prime `≤ c` with exactly `u` primes below it. -/
theorem primeAt_spec (c u : ℕ) (hu : u < PrimeCount.pc c) :
    (primeAt c u).Prime ∧ primeAt c u ≤ c ∧ PrimeCount.pc (primeAt c u - 1) = u := by
  have hlt : u < Fintype.card (PrimeIndex c) := by rw [card_primeIndex]; exact hu
  have hx : primeAt c u = ((primeIndexFinEquiv c).symm ⟨u, hlt⟩).val := by
    unfold primeAt; rw [dif_pos hlt]
  have hmem := mem_primesUpTo.mp ((primeIndexFinEquiv c).symm ⟨u, hlt⟩).property
  have hi := idx_eq_count c ((primeIndexFinEquiv c).symm ⟨u, hlt⟩)
  rw [Equiv.apply_symm_apply] at hi
  rw [hx]
  exact ⟨hmem.1, hmem.2, hi.symm⟩

/-- The prime count at `primeAt c u` is `u + 1`. -/
theorem pc_primeAt (c u : ℕ) (hu : u < PrimeCount.pc c) : PrimeCount.pc (primeAt c u) = u + 1 := by
  obtain ⟨hp, _, hcount⟩ := primeAt_spec c u hu
  have h2 := hp.two_le
  have h := PrimeIdx.pc_succ (primeAt c u - 1)
  rw [show primeAt c u - 1 + 1 = primeAt c u by omega, if_pos hp] at h
  omega

/-- The first prime is `2`. -/
theorem primeAt_zero (c : ℕ) (hc : 2 ≤ c) : primeAt c 0 = 2 := by
  have h := primeAt_of_count c 2 Nat.prime_two hc
  rwa [show PrimeCount.pc (2 - 1) = 0 from PrimeCount.pc_one] at h

/-! ## `primeSum` -/

/-- The sum of the primes up to `x`. -/
def primeSumOf (x : ℕ) : ℕ := ∑ p ∈ primesUpTo x, p

/-- The THR row count's prime sum is `seeds · primeSumOf cutoff` (`RCFive.RowKeys.thr_count`'s form). -/
theorem thr_prime_sum (c s : ℕ) :
    ((List.ofFn (primeIndexFinEquiv c).symm).map (fun p => s * p.val)).sum = s * primeSumOf c := by
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [Equiv.sum_comp (primeIndexFinEquiv c).symm (fun p : PrimeIndex c => s * p.val), ← Finset.mul_sum]
  unfold primeSumOf
  congr 1
  exact Finset.sum_coe_sort (primesUpTo c) (fun p => p)

/-- **`primeSum` in unary** (`PrimeSum.machine` under the masked reset). -/
def primeSumMap : UnaryMap primeSumOf where
  extra := 3
  states := 22 + 2
  machine := MaskedReset.machine PrimeSum.machine (fun _ => true)
  cost := fun x => 2 * (6 * (x + 3) ^ 3 + 4) + 2
  run := by
    intro x
    obtain ⟨T, H1, A1, hs, hv, hT⟩ := PrimeSum.run x
    obtain ⟨k, hm⟩ := step_mask0 (hs.enlarge hT) (fun _ => true) (by intro i _; rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]
    · have hc : (⟨1, by omega⟩ : Fin (2 + 3)) = Fin.castAdd 1 (1 : Fin 4) := rfl
      rw [hc, Fin.addCases_left, hv]
      unfold primeSumOf
      rw [PrimeSum.ps_eq]
    · have hc : (⟨1, by omega⟩ : Fin (2 + 3)) = Fin.castAdd 1 (1 : Fin 4) := rfl
      rw [hc, Fin.addCases_left]
      rfl

theorem cube_ge (x : ℕ) : 27 ≤ (x + 3) ^ 3 := by
  have h := Nat.pow_le_pow_left (show 3 ≤ x + 3 by omega) 3
  norm_num at h
  exact h

theorem primeSum_cost (x : ℕ) : primeSumMap.cost x ≤ 14 * (x + 3) ^ 3 := by
  change 2 * (6 * (x + 3) ^ 3 + 4) + 2 ≤ _
  have := cube_ge x
  omega

/-- **The `primeSum` stage at a request**, from the cutoff stage (THR `primeCutoff`, else `0`). -/
def primeSumStage (a : DecompositionAlgorithm) (cs : UnaryStage a (cutoffOf a)) :
    UnaryStage a (fun r => primeSumOf (cutoffOf a r)) :=
  cs.thenMapP primeSumMap 14 3 primeSum_cost

/-! ## `primeOfIndex` -/

theorem idx_value (c u v : ℕ) (h : (PrimeCount.pc c ≤ u ∧ v = 1) ∨
    (u < PrimeCount.pc c ∧ v.Prime ∧ v ≤ c ∧ PrimeCount.pc (v - 1) = u)) : v = primeAt c u := by
  rcases h with ⟨hc, rfl⟩ | ⟨_, hp, hvc, hcount⟩
  · exact (primeAt_off c u hc).symm
  · rw [← hcount]; exact (primeAt_of_count c v hp hvc).symm

/-- **`primeAt` in unary**: cutoff `1^c` on tape 0, index `1^u` on tape 1, `1^(primeAt c u)` on tape 2
(`PrimeIdx.machine` under the masked reset). -/
def primeOfIndexMap : UnaryMap2 (fun c u => primeAt c u) where
  extra := 3
  states := 22 + 2
  machine := MaskedReset.machine PrimeIdx.machine (fun _ => true)
  cost := fun c _ => 2 * (6 * (c + 3) ^ 3 + 4) + 2
  run := by
    intro c u
    obtain ⟨T, H1, A1, v, hs, hv, hT, hspec⟩ := PrimeIdx.run c u
    obtain ⟨k, hm⟩ := step_mask0 (hs.enlarge hT) (fun _ => true) (by intro i _; rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn2]
    · have hc : (⟨2, by omega⟩ : Fin (3 + 3)) = Fin.castAdd 1 (2 : Fin 5) := rfl
      rw [hc, Fin.addCases_left, hv, idx_value c u v hspec]
    · have hc : (⟨2, by omega⟩ : Fin (3 + 3)) = Fin.castAdd 1 (2 : Fin 5) := rfl
      rw [hc, Fin.addCases_left]
      rfl

theorem primeIdx_cost (c u : ℕ) : primeOfIndexMap.cost c u ≤ 14 * (c + u + 3) ^ 3 := by
  change 2 * (6 * (c + 3) ^ 3 + 4) + 2 ≤ _
  have h1 := Nat.pow_le_pow_left (show c + 3 ≤ c + u + 3 by omega) 3
  have := cube_ge c
  omega

/-! ## `nextPrime` -/

/-- The prime after `p` below the cutoff `c`: `primeAt c (π p)`; the value `1` flags "past the cutoff". -/
def nextPrimeOf (c p : ℕ) : ℕ := primeAt c (PrimeCount.pc p)

/-- At a keyed prime, the next prime. -/
theorem nextPrime_succ (c u : ℕ) (hu : u + 1 < PrimeCount.pc c) :
    nextPrimeOf c (primeAt c u) = primeAt c (u + 1) := by
  unfold nextPrimeOf
  rw [pc_primeAt c u (by omega)]

/-- At the last prime, the flag `1`. -/
theorem nextPrime_last (c u : ℕ) (hu : u + 1 = PrimeCount.pc c) : nextPrimeOf c (primeAt c u) = 1 := by
  unfold nextPrimeOf
  rw [pc_primeAt c u (by omega)]
  exact primeAt_off c (u + 1) (by omega)

def slP : Fin 5 → Fin 10 := ![1, 3, 4, 5, 6]
def slI : Fin 6 → Fin 10 := ![0, 3, 2, 7, 8, 9]

theorem slP_inj : Function.Injective slP := by decide
theorem slI_inj : Function.Injective slI := by decide

/-- The composite: `π p` onto tape 3, then `primeAt c (π p)` onto tape 2. -/
def nextMachine :=
  Composition.machine (RecoveryFocus.machine slP primeCountMap.machine)
    (RecoveryFocus.machine slI primeOfIndexMap.machine)

/-- **`nextPrime` in unary**: cutoff `1^c` on tape 0, current prime `1^p` on tape 1, `1^(nextPrimeOf c p)` on
tape 2. -/
def nextPrimeMap : UnaryMap2 nextPrimeOf where
  extra := 7
  states := _
  machine := nextMachine
  cost := fun c p => primeCountMap.cost p + 1 + primeOfIndexMap.cost c (PrimeCount.pc p)
  run := by
    intro c p
    obtain ⟨H1, A1, h1, hv1, hh1⟩ := primeCountMap.run p
    have d1 := h1.dock slP slP_inj (fun _ => 0) (unIn2 10 c p) (fun _ => rfl) (by intro k; fin_cases k <;> rfl)
    obtain ⟨H2, A2, h2, hv2, hh2⟩ := primeOfIndexMap.run c (PrimeCount.pc p)
    have e13 : slI 1 = slP 1 := by decide
    have d2 := h2.dock slI slI_inj (dockH slP (fun _ => 0) H1) (install slP (unIn2 10 c p) A1)
      (by
        intro k
        fin_cases k
        · exact dockH_other _ _ _ _ (by decide)
        · show dockH slP (fun _ => 0) H1 (slI 1) = 0
          rw [e13, dockH_slot _ slP_inj]
          exact hh1
        · exact dockH_other _ _ _ _ (by decide)
        · exact dockH_other _ _ _ _ (by decide)
        · exact dockH_other _ _ _ _ (by decide)
        · exact dockH_other _ _ _ _ (by decide))
      (by
        intro k
        fin_cases k
        · exact install_other _ _ _ _ (by decide)
        · show install slP (unIn2 10 c p) A1 (slI 1) = List.replicate (PrimeCount.pc p) true
          rw [e13, install_slot _ slP_inj]
          exact hv1
        · exact install_other _ _ _ _ (by decide)
        · exact install_other _ _ _ _ (by decide)
        · exact install_other _ _ _ _ (by decide)
        · exact install_other _ _ _ _ (by decide))
    refine ⟨_, _, d1.seq d2, ?_, ?_⟩
    · exact (install_slot (t := 6) slI slI_inj (install slP (unIn2 10 c p) A1) A2 2).trans hv2
    · exact (dockH_slot (t := 6) slI slI_inj (dockH slP (fun _ => 0) H1) H2 2).trans hh2

theorem next_cost (c p : ℕ) : nextPrimeMap.cost c p ≤ 28 * (c + p + 3) ^ 3 := by
  change 2 * (6 * (p + 3) ^ 3 + 4) + 2 + 1 + (2 * (6 * (c + 3) ^ 3 + 4) + 2) ≤ _
  have h1 := Nat.pow_le_pow_left (show c + 3 ≤ c + p + 3 by omega) 3
  have h2 := Nat.pow_le_pow_left (show p + 3 ≤ c + p + 3 by omega) 3
  have := cube_ge (c + p)
  omega

end
end NearCubicWires.PacketsGlue.RequestMeta

