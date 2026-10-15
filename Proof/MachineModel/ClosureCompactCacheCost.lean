import Proof.MachineModel.ClosureRadix

/-! Bytes in the replicated cache are bounded by its occurrence count and
the ORIGINAL per-equation bit bound. Replication is a preparation factor;
it is not used as the radix of a printed equation. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactCacheCost
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierPrime
open RepairSource.CloseoutFinal C10SupplierRowInput
open scoped BigOperators

theorem bit_bound (z : Int) (b : Nat) (hb : 0<b) (hz : z.natAbs < 2^b) :
    intBitLength z ≤ b := by
  have := Nat.log_lt_of_lt_pow' (by omega : b≠0) hz
  unfold intBitLength
  omega

theorem gate_bytes {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs]
    (i : Fin gs.length) :
    (exactWord gs[i.val]).length ≤ (n+1)*(2*P1Radix.bits gs+2) := by
  have safe := P1Radix.safe i
  have hw (j : Fin n) : intBitLength (gs[i.val].weight j) ≤ P1Radix.bits gs := by
    apply bit_bound _ _ (P1Radix.positive (gs:=gs))
    have h := Finset.single_le_sum (fun k _ => Nat.zero_le (gs[i.val].weight k).natAbs)
      (Finset.mem_univ j)
    exact h.trans_lt ((Nat.le_add_right _ _).trans_lt safe)
  have ht : intBitLength gs[i.val].target ≤ P1Radix.bits gs := by
    apply bit_bound _ _ (P1Radix.positive (gs:=gs))
    exact (Nat.le_add_left _ _).trans_lt safe
  simp only [exactWord,List.length_append,List.length_flatMap,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,DecompositionSource.intWord_length]
  have sum : (∑ j : Fin n, (2*intBitLength (gs[i.val].weight j)+2)) ≤
      n*(2*P1Radix.bits gs+2) := by
    calc
      _ ≤ ∑ _j : Fin n, (2*P1Radix.bits gs+2) := by gcongr with j; exact hw j
      _ = _ := by simp
  nlinarith

theorem cache_bytes {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs] :
    (exactListWord gs).length ≤ 4*(gs.length+1)*(n+1)*(P1Radix.bits gs+1) := by
  have body : (gs.flatMap exactWord).length ≤ gs.length*((n+1)*(2*P1Radix.bits gs+2)) := by
    rw [List.length_flatMap]
    simpa only [List.length_map,smul_eq_mul] using
      List.sum_le_card_nsmul (gs.map (fun g => (exactWord g).length)) ((n+1)*(2*P1Radix.bits gs+2)) (by
      intro v hv
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hv
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
      exact gate_bytes gs ⟨i,hi⟩)
  have head : natBitLength gs.length ≤ gs.length+1 := by
    unfold natBitLength
    have := Nat.log_le_self 2 gs.length
    omega
  rw [exactListWord,List.length_append,DecompositionSource.natWord_length]
  have hM : 1 ≤ (n+1)*(P1Radix.bits gs+1) := by
    have : 0 < (n+1)*(P1Radix.bits gs+1) := by positivity
    omega
  nlinarith [Nat.mul_le_mul_left gs.length hM]

theorem actual_cache_bytes {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2 = liveᶜ.card) (degree : Nat) :
    (exactListWord (pool a live occ s harity)).length ≤
      8*2^live.card*((s+1)/2+s/2+1)*(CompactBounds.radix a live occ+1)^2 := by
  letI := p1ActualRadix a live occ s harity degree
  have h := cache_bytes (pool a live occ s harity)
  have hc := DecompositionSource.children_le_output (childList a live occ)
  have hN : (pool a live occ s harity).length+1 ≤
      2*2^live.card*(CompactBounds.radix a live occ+1) := by
    rw [pool_length,liveList_length]
    unfold CompactBounds.radix
    have hpow : 1 ≤ 2^live.card := Nat.one_le_two_pow
    nlinarith
  change (exactListWord (pool a live occ s harity)).length ≤ _
  calc
    _ ≤ 4*((pool a live occ s harity).length+1)*((s+1)/2+s/2+1)*
        (CompactBounds.radix a live occ+1) := h
    _ ≤ 4*(2*2^live.card*(CompactBounds.radix a live occ+1))*((s+1)/2+s/2+1)*
        (CompactBounds.radix a live occ+1) := by gcongr
    _ = _ := by ring

end NearCubicWires.P1Closure.CompactCacheCost
