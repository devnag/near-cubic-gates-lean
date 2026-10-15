import Proof.CaseAnalysis.RowsUniversalLowering
import Proof.CaseAnalysis.RawRowsChildLog

/-! Coarse A.2 resource transport for the actual pooled source. The frozen
gate's integer description is polynomial in the original description; hence
the same source's child count remains polynomial and its logarithm is O(Lq).
No numerical magnitude is used as a machine runtime bound. -/
namespace NearCubicWires.RepairSource.CloseoutRowsUniversal
open SupplierPipeline RepairRepresentation CloseoutRawRows PolynomialSchedule SourceInterfaces
open RepairOrdinary ExtDecompositionBatch
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable {q : ℕ}

private theorem magnitude_le (z : ℤ) (e : ℕ) (h : intBitLength z≤e) :
    z.natAbs≤2^e:=by
  have hz:z.natAbs<2^intBitLength z:=by
    simpa only [intBitLength,natBitLength] using
      Nat.lt_pow_succ_log_self (b:=2) (by omega) z.natAbs
  exact hz.le.trans (Nat.pow_le_pow_right (by decide) h)

theorem minimum_magnitude (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    (minimumLiveScore g.gate live).natAbs≤q*2^g.gate.encodingBits:=by
  calc
    _≤∑ i∈live,(if g.gate.weight i<0 then g.gate.weight i else 0).natAbs:=
      Int.natAbs_sum_le live _
    _≤∑ _i∈live,2^g.gate.encodingBits:=by
      apply Finset.sum_le_sum
      intro i _
      split
      · apply magnitude_le
        have hs:=Finset.single_le_sum (fun j _=>Nat.zero_le (intBitLength (g.gate.weight j)))
          (Finset.mem_univ i)
        unfold NormalizedThresholdGate.encodingBits
        omega
      · simp
    _=live.card*2^g.gate.encodingBits:=by simp
    _≤q*2^g.gate.encodingBits:=by
      apply Nat.mul_le_mul_right
      simpa using Finset.card_le_univ live

theorem constant_parameters (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    (∀ i,((constantSupportedGate live g).gate.weight i).natAbs≤
      (q+1)*2^g.gate.encodingBits) ∧
    ((constantSupportedGate live g).gate.threshold).natAbs≤(q+1)*2^g.gate.encodingBits:=by
  constructor
  · intro i
    rw [constant_weight]
    split
    · simp
    · have hi:(g.gate.weight i).natAbs≤2^g.gate.encodingBits:=by
        apply magnitude_le
        have hs:=Finset.single_le_sum (fun j _=>Nat.zero_le (intBitLength (g.gate.weight j)))
          (Finset.mem_univ i)
        unfold NormalizedThresholdGate.encodingBits
        omega
      exact hi.trans (by
        calc
          _=1*2^g.gate.encodingBits:=by omega
          _≤(q+1)*2^g.gate.encodingBits:=Nat.mul_le_mul_right _ (by omega))
  · rw [constant_threshold]
    have hm:=minimum_magnitude live g
    have ht:g.gate.threshold.natAbs≤2^g.gate.encodingBits:=by
      apply magnitude_le
      unfold NormalizedThresholdGate.encodingBits
      omega
    exact (Int.natAbs_sub_le _ _).trans (by nlinarith)

theorem constant_description (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    (constantSupportedGate live g).descriptionBits≤(g.descriptionBits+3)^2:=by
  have hp:=constant_parameters live g
  have bitbound (z : ℤ) (hz:z.natAbs≤(q+1)*2^g.gate.encodingBits) :
      intBitLength z≤q+g.gate.encodingBits+3:=by
    have hb:=(PolynomialClock.natBitLength_mono hz).trans
      (ValidatorPolynomialDomination.natBitLength_mul_le (q+1) (2^g.gate.encodingBits))
    rw [bits_two_pow] at hb
    have hq:natBitLength (q+1)≤q+2:=by
      unfold natBitLength
      have h:=Nat.log_le_self 2 (q+1)
      omega
    change natBitLength z.natAbs≤_
    omega
  have ht:=bitbound _ hp.2
  have hw:(∑ i,intBitLength ((constantSupportedGate live g).gate.weight i))≤
      q*(q+g.gate.encodingBits+3):=by
    simpa using Finset.sum_le_card_nsmul Finset.univ
      (fun i=>intBitLength ((constantSupportedGate live g).gate.weight i))
      (q+g.gate.encodingBits+3) (fun i _=>bitbound _ (hp.1 i))
  have hb:(constantSupportedGate live g).gate.encodingBits≤
      (q+1)*(q+g.gate.encodingBits+3):=by
    change intBitLength (constantSupportedGate live g).gate.threshold+
      (∑ i,intBitLength ((constantSupportedGate live g).gate.weight i))≤_
    calc
      _≤(q+g.gate.encodingBits+3)+q*(q+g.gate.encodingBits+3):=Nat.add_le_add ht hw
      _=(q+1)*(q+g.gate.encodingBits+3):=by ring
  change (constantSupportedGate live g).gate.encodingBits+q≤_
  calc
    _≤(q+1)*(q+g.gate.encodingBits+3)+q:=Nat.add_le_add_right hb q
    _≤(q+1)*(q+g.gate.encodingBits+3)+(q+g.gate.encodingBits+3):=
      Nat.add_le_add_left (by omega) _
    _=(q+2)*(q+g.gate.encodingBits+3):=by ring
    _≤(q+g.gate.encodingBits+3)*(q+g.gate.encodingBits+3):=
      Nat.mul_le_mul_right _ (by omega)
    _=(g.descriptionBits+3)^2:=by unfold SupportedNormalizedGate.descriptionBits;ring

theorem pool_description (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (cap : ℕ) (hc:∀ i : Fin occ.length,(occ.get i).descriptionBits≤cap)
    (i : Fin (pool live occ).length) :
    ((pool live occ).get i).descriptionBits≤(cap+3)^2:=by
  have hm:=List.get_mem (pool live occ) i
  obtain ⟨g,hg,he⟩:=List.mem_flatMap.mp hm
  obtain ⟨j,hj,rfl⟩:=List.mem_iff_getElem.mp hg
  have hb:=hc ⟨j,hj⟩
  simp only [List.get_eq_getElem] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he|he
  · rw [he]
    nlinarith
  · rw [he]
    exact (constant_description live occ[j]).trans (Nat.pow_le_pow_left (by omega) 2)

theorem pooled_child_log (a : DecompositionAlgorithm) {cap : ℕ→ℕ}
    (hcap:PolynomiallyBounded cap) :
    ∃ c : ℕ,0<c ∧ ∀ q (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)),
      (∀ i : Fin occ.length,(occ.get i).descriptionBits≤cap q) →
      ∀ i : Fin (pool live occ).length,
        (children a ((pool live occ).get i)).length<2^(c*logScale q):=by
  have hpoly:PolynomiallyBounded (fun q=>(cap q+3)^2):=
    polynomiallyBounded_pow (polynomiallyBounded_add hcap (polynomiallyBounded_constant 3)) 2
  obtain ⟨c,hc,he⟩:=child_log_envelope a hpoly
  refine ⟨c,hc,?_⟩
  intro q live occ hd i
  exact he q (pool live occ) (pool_description live occ (cap q) hd) i

end
end NearCubicWires.RepairSource.CloseoutRowsUniversal
