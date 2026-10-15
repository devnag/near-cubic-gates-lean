import Proof.CaseAnalysis.RawRowsDescriptions
import Proof.Supplier.RowCachedEquationMeaning

/-! Coarse top-source bounds avoid an aggregate magnitude producer. They
refer to the same retained top children and original fourfold equation stack. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierPrime SourceInterfaces RepairRepresentation
open PolynomialSchedule CompilerSemantics ThresholdAlignedEnvelope
open RepairOrdinary
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem retained_top_bits {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    (retainedTopGate c).encodingBits ≤ c.top.gate.encodingBits := by
  let e := (retainedTopIndex c).toEmbedding
  have hs := Finset.sum_le_sum_of_subset (f := fun i : Fin c.bottomCount=>intBitLength (c.top.gate.weight i))
    (Finset.subset_univ (Finset.univ.map e))
  have he : (∑ i : Fin c.top.support.card,intBitLength (c.top.gate.weight (retainedTopIndex c i))) ≤
      ∑ i : Fin c.bottomCount,intBitLength (c.top.gate.weight i) := by
    rw [Finset.sum_map] at hs
    exact_mod_cast hs
  exact Nat.add_le_add le_rfl he

theorem top_source_parameter {q : ℕ} (c : NormalizedThresholdThresholdCircuit q)
    (desc : ℕ) (hd : c.descriptionBits ≤ desc) :
    c.top.support.card+(nonStrictAsStrict (retainedTopGate c)).encodingBits+1 ≤ desc+2 := by
  have hs : c.top.support.card ≤ c.bottomCount := (Finset.card_le_univ _).trans (by simp)
  have hg := retained_top_bits c
  have hb := strict_gate_bits (retainedTopGate c)
  unfold NormalizedThresholdThresholdCircuit.descriptionBits SupportedNormalizedGate.descriptionBits at hd
  omega

theorem top_output_bytes {q : ℕ} (a : DecompositionAlgorithm)
    (c : NormalizedThresholdThresholdCircuit q) (desc : ℕ) (hd : c.descriptionBits ≤ desc) :
    (exactListWord (ThresholdRows.children a c)).length ≤ sourceChildBound a desc := by
  exact (DecompositionSource.output_length a ⟨c.top.support.card,nonStrictAsStrict (retainedTopGate c)⟩).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (top_source_parameter c desc hd) a.degree))

theorem top_child_magnitude {q : ℕ} (a : DecompositionAlgorithm)
    (c : NormalizedThresholdThresholdCircuit q) (desc : ℕ) (hd : c.descriptionBits ≤ desc)
    (i : Fin (ThresholdRows.children a c).length) :
    childMagnitude ((ThresholdRows.children a c).get i) < 2^sourceChildBound a desc := by
  have hb := (RowCachedCoordinateBounds.child_bytes (ThresholdRows.children a c) i.val i.isLt).trans
    (top_output_bytes a c desc hd)
  exact (RowCachedEquation.equation_magnitude ((ThresholdRows.children a c).get i)).trans_le
    (Nat.pow_le_pow_right (by decide) hb)

theorem selection_count (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc : ℕ)
    (hfour : r.circuits.length ≤ 4) (hd : ∀ c∈r.circuits,c.descriptionBits ≤ desc) :
    Fintype.card (ThresholdRows.Selection a r) ≤ (sourceChildBound a desc+1)^4 := by
  classical
  have hchild (i : Fin r.circuits.length) :
      (ThresholdRows.children a (r.circuits.get i)).length ≤ sourceChildBound a desc+1 :=
    ((DecompositionSource.children_le_output _).trans
      (top_output_bytes a _ desc (hd _ (List.get_mem _ _)))).trans (Nat.le_succ _)
  calc
    _ = ∏ i : Fin r.circuits.length,(ThresholdRows.children a (r.circuits.get i)).length := by
      simp only [ThresholdRows.Selection,Fintype.card_pi,Fintype.card_fin]
    _ ≤ ∏ _i : Fin r.circuits.length,(sourceChildBound a desc+1) :=
      Finset.prod_le_prod' (fun i _=>hchild i)
    _ = (sourceChildBound a desc+1)^r.circuits.length := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hfour

theorem horner_lt_power (base : ℕ) (xs : List ℕ) (_hb : 0 < base)
    (hx : ∀ x∈xs,x < base) : natHornerFold base xs < base^xs.length := by
  induction xs with
  | nil => simp [natHornerFold]
  | cons x xs ih =>
    have hh := hx x (by simp)
    have ht := ih (fun y hy=>hx y (by simp [hy]))
    simp only [natHornerFold,List.length_cons,pow_succ]
    nlinarith

theorem canonical_stack_magnitude {Carrier : Type} [Fintype Carrier]
    (es : List (LabelledEquation Carrier)) (B : ℕ) (hfour : es.length ≤ 4)
    (he : ∀ e∈es,equationMagnitudeBound e < 2^B) :
    equationMagnitudeBound (canonicalEquationStack es) < 2^(4*(B+3)) := by
  let xs := es.map equationMagnitudeBound
  have hsum : xs.sum ≤ es.length*2^B := by
    change (es.map equationMagnitudeBound).sum ≤ es.length*2^B
    clear xs hfour
    induction es with
    | nil => simp
    | cons e es ih =>
      have hh := he e (by simp)
      have ht := ih (fun e he'=>he e (by simp [he']))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hbase : xs.sum+1 ≤ 2^(B+3) := by
    have hp : 1 ≤ 2^B := Nat.one_le_two_pow
    have hc := Nat.mul_le_mul_right (2^B) hfour
    rw [pow_add]
    norm_num
    omega
  have hentries : ∀ x∈xs,x < xs.sum+1 := by
    intro x hx
    exact (List.le_sum_of_mem hx).trans_lt (Nat.lt_succ_self _)
  have hh := horner_lt_power (xs.sum+1) xs (by omega) hentries
  have hmag := equationMagnitudeBound_stackEquations_le (equationListBase es) es
  simp only [equationListBase,Int.natAbs_natCast] at hmag
  calc
    _ ≤ natHornerFold (xs.sum+1) xs := hmag
    _ < (xs.sum+1)^es.length := by simpa only [xs,List.length_map] using hh
    _ ≤ (2^(B+3))^es.length := Nat.pow_le_pow_left hbase _
    _ ≤ (2^(B+3))^4 := Nat.pow_le_pow_right Nat.one_le_two_pow hfour
    _ = _ := by rw [←pow_mul,Nat.mul_comm]

def thresholdMagnitudeExponent (a : DecompositionAlgorithm) (desc : ℕ) :=
  4*(sourceChildBound a desc+3)

theorem actual_threshold_difference (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc : ℕ)
    (hfour : r.circuits.length ≤ 4) (hd : ∀ c∈r.circuits,c.descriptionBits ≤ desc)
    (sel : ThresholdRows.Selection a r) (x : Fin (thresholdFourfoldOccurrences r).length → Bool) :
    ((ThresholdRows.equation a r sel).difference x).natAbs < 2^thresholdMagnitudeExponent a desc := by
  apply (equation_difference_natAbs_le_magnitudeBound _ _).trans_lt
  apply canonical_stack_magnitude (ThresholdRows.equations a r sel) (sourceChildBound a desc)
  · simpa only [ThresholdRows.equations,List.length_ofFn] using hfour
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    rw [thresholdChildEquation_magnitudeBound]
    exact top_child_magnitude a _ desc (hd _ (List.get_mem _ _)) (sel i)

theorem thresholdMagnitudeExponent_polynomial (a : DecompositionAlgorithm) (degree : ℕ) :
    PolynomiallyBounded (fun q=>thresholdMagnitudeExponent a (descriptionEnvelope degree q)) :=
  polynomiallyBounded_mul (polynomiallyBounded_constant 4)
    (polynomiallyBounded_add (sourceChildBound_polynomial a (descriptionEnvelope_polynomial degree))
      (polynomiallyBounded_constant 3))

end
end NearCubicWires.RepairSource.CloseoutRawRows
