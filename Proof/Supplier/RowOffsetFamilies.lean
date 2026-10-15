import Proof.Supplier.SupplierEstimator

/-! Actual finite offset families of the A.13 symmetric and threshold rows.
These bounds justify a polynomial number of table scans at a bounded-wire
fourfold caller. They do not assume a runtime offset tape has been produced. -/
namespace NearCubicWires.RepairOrdinary.RowOffsets
open SupplierPipeline SupplierEstimator SupplierPrime
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bottom_le_wires {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) :
    c.bottomCount ≤ c.wireCount := by
  have h : (∑ _i : Fin c.bottomCount, (1 : ℕ)) ≤
      ∑ i : Fin c.bottomCount, ((c.bottom i).wireCount+1) := by
    exact Finset.sum_le_sum fun i _ => Nat.le_add_left 1 _
  simpa [NormalizedSymmetricThresholdCircuit.wireCount] using h

abbrev SymmetricOffsets (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :=
  (i : Fin r.circuits.length) → Fin ((r.circuits.get i).bottomCount+1)

/-- These are exactly the residual constants read by canonicalSymmetricCircuitRow. -/
def symmetricOffsets (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput r.q) : SymmetricOffsets r :=
  fun i => ⟨occurrenceResidualConstantCount (symmetricFourfoldOccurrences r)
    liveScale input (symmetricCircuitMask r i), by
    have h := symmetricCircuitResidualCount_reconstruction r liveScale input i
    have hb := ((r.circuits.get i).acceptedBottomCount input).isLt
    omega⟩

theorem symmetric_card_le (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (cap : ℕ) (hfour : r.circuits.length ≤ 4)
    (hcap : ∀ c ∈ r.circuits, c.wireCount ≤ cap) :
    Fintype.card (SymmetricOffsets r) ≤ (cap+1)^4 := by
  classical
  rw [Fintype.card_pi]
  calc
    (∏ i : Fin r.circuits.length, Fintype.card (Fin ((r.circuits.get i).bottomCount+1)))
        ≤ ∏ _i : Fin r.circuits.length, (cap+1) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      simp only [Fintype.card_fin]
      exact Nat.succ_le_succ ((bottom_le_wires _).trans (hcap _ (List.get_mem _ _)))
    _ = (cap+1)^r.circuits.length := by simp
    _ ≤ (cap+1)^4 := Nat.pow_le_pow_right (by omega) hfour

theorem symmetric_card_polynomial
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (degree : ℕ) (hfour : r.circuits.length ≤ 4)
    (hcap : ∀ c ∈ r.circuits, c.wireCount ≤ (r.q+1)^degree) :
    Fintype.card (SymmetricOffsets r) ≤ 16*(r.q+1)^(4*degree) := by
  have hp : 1 ≤ (r.q+1)^degree := Nat.one_le_pow _ _ (by omega)
  calc
    Fintype.card (SymmetricOffsets r) ≤ ((r.q+1)^degree+1)^4 :=
      symmetric_card_le r _ hfour hcap
    _ ≤ (2*(r.q+1)^degree)^4 := Nat.pow_le_pow_left (by omega) 4
    _ = 16*(r.q+1)^(4*degree) := by rw [mul_pow, ←pow_mul]; ring

/-- One actual modular residual offset, with its prime carried in the type. -/
def thresholdOffset {q cutoff : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) (liveScale : ℕ)
    (input : BitInput q) (equation : LabelledEquation (Fin occurrences.length))
    (prime : PrimeIndex cutoff) : Fin prime.val :=
  ⟨modularResidualOffset occurrences liveScale input equation prime.val, by
    have hp : (0 : ℤ) < prime.val := by
      exact_mod_cast (mem_primesUpTo.mp prime.property).1.pos
    have hn := Int.emod_nonneg
      (occurrenceWeightedResidualConstant occurrences liveScale input
        Finset.univ equation.weights-equation.target) (ne_of_gt hp)
    have hl := Int.emod_lt_of_pos
      (occurrenceWeightedResidualConstant occurrences liveScale input
        Finset.univ equation.weights-equation.target) hp
    exact_mod_cast (show
      ((occurrenceWeightedResidualConstant occurrences liveScale input
        Finset.univ equation.weights-equation.target) % (prime.val : ℤ)).toNat <
      prime.val from (Int.toNat_lt hn).2 hl)⟩

theorem threshold_card_le {cutoff : ℕ} (prime : PrimeIndex cutoff) :
    Fintype.card (Fin prime.val) ≤ cutoff := by
  simpa only [Fintype.card_fin] using (mem_primesUpTo.mp prime.property).2

/-- Enumerating every prime and every residue remains quadratic in the cutoff. -/
theorem threshold_all_card_le (cutoff : ℕ) :
    Fintype.card ((prime : PrimeIndex cutoff) × Fin prime.val) ≤ (cutoff+1)^2 := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ prime : PrimeIndex cutoff, Fintype.card (Fin prime.val)) ≤
        ∑ _prime : PrimeIndex cutoff, cutoff :=
      Finset.sum_le_sum fun prime _ => threshold_card_le prime
    _ = (primesUpTo cutoff).card * cutoff := by simp
    _ ≤ (cutoff+1)*cutoff := by
      apply Nat.mul_le_mul_right
      have h := Finset.card_le_card (Finset.filter_subset Nat.Prime (Finset.range (cutoff+1)))
      simpa only [primesUpTo, Finset.card_range] using h
    _ ≤ (cutoff+1)^2 := by nlinarith

end NearCubicWires.RepairOrdinary.RowOffsets
