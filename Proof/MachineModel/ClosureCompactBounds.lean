import Proof.CaseAnalysis.FinalSupplierRowInput
import Proof.MachineModel.ClosureCompactRow

/-! A.12's compact bounds at the actual hardwired pool and incidence bank.
Hardwiring cannot increase the equation magnitude bound. Incidence conversion
can only delete repeated factors; it does not replace degree by cache length.
These feed the existing commonInput/table consumer, with no new source postulate. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactBounds
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierPrime SupplierEstimator
open ThresholdCompiler CanonicalFourfoldRowProgram RepairSource CloseoutFinal
open C10SupplierRowInput RowBinLift
open scoped BigOperators

theorem hardwire_magnitude {q : Nat} (live : Finset (Fin q))
    (g : ExactThresholdGate q) (y : BitInput live.card) :
    equationMagnitudeBound (RowCachedEquation.equation (hardwire live g y))  ≤ 
      equationMagnitudeBound (RowCachedEquation.equation g) := by
  have hsum : (∑ k : Fin q, (g.weight k).natAbs) =
      (∑ j : Fin live.card,
        (g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j))).natAbs) +
      (∑ j : Fin liveᶜ.card,
        (g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inr j))).natAbs) := by
    rw [← Equiv.sum_comp (normalizedLiveExternalCoordinateEquiv live)
      (fun k => (g.weight k).natAbs), Fintype.sum_sum_type]
  have hlive :
      (∑ j : Fin live.card,
        g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j)) *
          (if y j then 1 else 0)).natAbs  ≤ 
      ∑ j : Fin live.card,
        (g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j))).natAbs := by
    refine (Int.natAbs_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    split <;> simp
  have ht := Int.natAbs_sub_le g.target
    (∑ j : Fin live.card,
      g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j)) *
        (if y j then 1 else 0))
  simp only [equationMagnitudeBound,RowCachedEquation.equation,hardwire]
  omega

theorem cast_magnitude {m n : Nat} (h : m=n) (g : ExactThresholdGate n) :
    equationMagnitudeBound (RowCachedEquation.equation (castGate h g)) =
      equationMagnitudeBound (RowCachedEquation.equation g) := by
  subst n
  rfl

theorem positions_nodup (j : Nat) (bits : List Bool) :
    (RowMaskMeaning.positions j bits).Nodup := by
  induction bits generalizing j with
  | nil => simp [RowMaskMeaning.positions]
  | cons b bs ih =>
    cases b
    · simpa [RowMaskMeaning.positions] using ih (j+1)
    · simp only [RowMaskMeaning.positions,ite_true,List.singleton_append,List.nodup_cons]
      refine ⟨?_,ih (j+1)⟩
      intro hj
      have h := RowMaskMeaning.positions_bound (j+1) bs j hj
      omega

theorem mask_degree {B : Nat} (m : List (Fin B)) :
    (RowTupleCommonEquation.one B (List.ofFn (fun i : Fin B => decide (i∈m)))).length  ≤ 
      m.length := by
  let bits := List.ofFn (fun i : Fin B => decide (i∈m))
  have hlen : bits.length ≤ B := by simp [bits]
  have hn : (RowTupleCommonEquation.one B bits).Nodup := by
    rw [RowTupleCommonEquation.one,dif_pos hlen]
    apply List.Nodup.of_map (f:=Fin.val)
    rw [RowMaskMeaning.typed_values]
    exact positions_nodup 0 bits
  apply (hn.subperm ?_).length_le
  intro i hi
  exact of_decide_eq_true ((CloseoutRowsSourceMeaning.mask_one_mem _ i).mp hi)

theorem raw_family_degree {l r : Nat} (gs : List (ExactThresholdGate (l+r)))
    (ps : List (List (List (Fin gs.length)))) (degree : Nat)
    (hd : ∀ ms∈ps, ∀ m∈ms, m.length ≤ degree) :
    ∀ ms∈CloseoutRowsCacheInput.family gs (ExtIncidence.NativeRowInput.bank ps),
      ∀ m∈ms, m.length ≤ degree := by
  intro ms hms m hm
  obtain ⟨rows,hrows,rfl⟩ := List.mem_map.mp hms
  obtain ⟨mons,hmons,rfl⟩ := List.mem_map.mp hrows
  obtain ⟨bits,hbits,rfl⟩ := List.mem_map.mp hm
  obtain ⟨indices,hindices,rfl⟩ := List.mem_map.mp hbits
  simp only [CloseoutRowsCacheInput.monomial,RowCachedEquation.equations,List.length_map]
  exact (mask_degree indices).trans (hd mons hmons indices hindices)

theorem actual_family_degree {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) (degree : Nat)
    (hd : CloseoutRawRows.RawMonomialDegreeAtMost degree P) :
    ∀ ms∈CloseoutRowsCacheInput.family (pool a live occ s harity)
      (bank a live occ s harity P), ∀ m∈ms, m.length ≤ degree := by
  apply raw_family_degree
  intro ms hms m hm
  obtain ⟨yi,rfl⟩ := List.mem_ofFn.mp hms
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hm
  simpa only [List.length_map] using
    CloseoutRowsUniversal.lower_degree a live occ P degree hd old hold

/-- The source cache BEFORE live-assignment replication supplies the radix.
The full replicated pool is deliberately absent from this definition. -/
def radix {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) : Nat :=
  (exactListWord (childList a live occ)).length+1

theorem pool_magnitude {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card)
    (g : ExactThresholdGate ((s+1)/2+s/2)) (hg : g∈pool a live occ s harity) :
    equationMagnitudeBound (RowCachedEquation.equation g)<2^radix a live occ := by
  have hone : 1<2^radix a live occ := by
    apply Nat.one_lt_pow (by unfold radix; omega) (by decide)
  have hget (i : Nat) :
      equationMagnitudeBound (RowCachedEquation.equation
        ((childList a live occ).getD i falseChild))<2^radix a live occ := by
    by_cases hi : i<(childList a live occ).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact RowCachedEquation.cache_radix_safe (childList a live occ) ⟨i,hi⟩
    · rw [List.getD_eq_default _ _ (by omega : (childList a live occ).length ≤ i)]
      simpa [falseChild,falseGate,RowCachedEquation.equation,equationMagnitudeBound] using hone
  rcases List.mem_cons.mp hg with h | h
  · subst g
    simpa [falseGate,RowCachedEquation.equation,equationMagnitudeBound] using hone
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp h
    unfold poolFn
    rw [cast_magnitude]
    exact (hardwire_magnitude live _ _).trans_lt (hget _)

theorem actual_family_bits {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) :
    ∀ ms∈CloseoutRowsCacheInput.family (pool a live occ s harity)
      (bank a live occ s harity P), ∀ e∈ms.flatten,
        equationMagnitudeBound e<2^radix a live occ := by
  intro ms hms e he
  obtain ⟨rows,_,rfl⟩ := List.mem_map.mp hms
  obtain ⟨m,hm,he⟩ := List.mem_flatten.mp he
  obtain ⟨bits,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨native,hn,rfl⟩ := List.mem_map.mp he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hn
  rw [CloseoutRowsCacheInput.coordinates_magnitude]
  exact pool_magnitude a live occ s harity _ (List.getElem_mem i.isLt)

noncomputable def input {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) (w degree : Nat)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length<2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (hd : CloseoutRawRows.RawMonomialDegreeAtMost degree P) : EquationRow.Input :=
  CloseoutRows.commonInput s (radix a live occ) degree (live.card+1)
    (CloseoutRowsCacheInput.family (pool a live occ s harity) (bank a live occ s harity P))
    hs (gate a live occ s harity P w hmon hpos hload)
    (actual_family_degree a live occ s harity P degree hd)
    (actual_family_bits a live occ s harity P)

theorem input_width {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) (w degree : Nat)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length<2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (hd : CloseoutRawRows.RawMonomialDegreeAtMost degree P) :
    (input a live occ s harity P w degree hs hmon hpos hload hd).p =
      radix a live occ*(degree*(live.card+1))+(live.card+1) := rfl

end NearCubicWires.P1Closure.CompactBounds
