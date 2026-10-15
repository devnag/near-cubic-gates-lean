import Proof.CaseAnalysis.WitnessBoundedFamilySupportRun

/-! Exact cache bytes exported from the existing original-input bounded run.
The proof recovers its selected child by determinism; the machine and budget
are unchanged, and no second source call is executed. Rejected inputs still
have the same total run and flag. Cache facts require its actual admission.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdCacheAtAdmission

open NearCubicWires LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open ProjectionNormalization CloseoutWitness CanonicalWitnessCodec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine

def cacheSlot (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool) (j : Fin 19) :=
  BoundedFamilySupport.slots source a k D G E sym
    (ColdFamilySupport.cache source a k D G (BoundedFamily.exponent sym) E j)

/-- Exact cache facts on the physical parent tape map. -/
def Cached (a : PointwisePCPPAlgorithm) (k CH Cpad D G E : ℕ)
    (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad : k + 3 ≤ Cpad)
    (heads : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E) + 1) → ℕ)
    (data : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E) + 1) → List Bool) : Prop :=
  ∃ oracle, decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
      (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle ∧
    oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G
      (SelectedOracle.width source k CH Cpad code (List.ofFn x)) ∧
    let r := ColdNative.request source a k CH Cpad code x hpad oracle
    ∀ j : Fin 19,
      data (cacheSlot source a k D G E (BoundedFields.symmetric bits) j) =
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) [] j ∧
      heads (cacheSlot source a k D G E (BoundedFields.symmetric bits) j) = PCPPQueryClauseReuse.heads j

/-- Recover fields from the selected child already present in the parent run. -/
theorem cached_of_selected (a : PointwisePCPPAlgorithm)
    (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hpad : k + 3 ≤ Cpad) (hD : 1 ≤ D) (hsym : 0 < symDen) (hthr : 0 < thrDen) (hK : 0 < K)
    (hcut : 2 ^ a.minimumArity ≤ cutoff) (hd : 0 < delta) (hh : delta < 1 / 2) (hc : 1 ≤ copies)
    (hbudget : ∀ N, FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)
      ≤ K * (N + 1) ^ E)
    (heads : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E) + 1) → ℕ)
    (data : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E) + 1) → List Bool)
    (selected : BoundedFamily.headerValid (List.ofFn x) bits = true →
      BoundedFamilySupport.Selected source a k CH Cpad cutoff D G copies E K symDen thrDen
        (CloseoutMassThreshold.literalWidth delta copies) delta (CloseoutSampledWitness.massCap delta copies)
        code x bits hpad (BoundedFields.symmetric bits) heads data)
    (admitted : BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad = true) :
    Cached source a k CH Cpad D G E code x bits hpad heads data := by
  classical
  have both : BoundedFamily.headerValid (List.ofFn x) bits = true ∧
      ColdFamily.passed source a k CH Cpad cutoff D G copies
        (BoundedFamily.exponent (BoundedFields.symmetric bits))
        (BoundedFamily.denominator (BoundedFields.symmetric bits) symDen thrDen) delta code
        (BoundedFields.symmetric bits) x (BoundedFields.oracle bits) (BoundedFields.family bits) hpad = true := by
    simpa only [BoundedFamily.passed, Bool.and_eq_true] using admitted
  have cap : 16 * bits.length ≤ n := by
    have h := (of_decide_eq_true both.1).1
    simpa only [List.length_ofFn] using h
  have rawCap : 16 * (BoundedFields.oracle bits).length ≤ n := by
    rw [(BoundedFields.lengths bits).1]
    exact cap
  have familyCap : 16 * (BoundedFields.family bits).length ≤ n := by
    rw [(BoundedFields.lengths bits).2]
    exact cap
  obtain ⟨child, childRun, childHeads, childTapes⟩ := selected both.1
  obtain ⟨native, nativeRun, _nativeSteps, _nativeFlagHead, _nativeFlag, nativeFields⟩ :=
    ColdFamilySupport.family_run source a k CH Cpad cutoff D G copies
      (BoundedFamily.exponent (BoundedFields.symmetric bits)) E K
      (BoundedFamily.denominator (BoundedFields.symmetric bits) symDen thrDen) delta code
      (BoundedFields.symmetric bits) x (BoundedFields.oracle bits) (BoundedFields.family bits)
      hpad hD (by unfold BoundedFamily.denominator; split_ifs <;> assumption)
      hK hcut hd hh hc hbudget rawCap familyCap
  have same : child = native := Option.some.inj (childRun.symm.trans nativeRun)
  have tapesEq := congrArg (fun r => r.final.tapes) same
  have headsEq := congrArg (fun r => r.final.heads) same
  obtain ⟨oracle, hdecode, hsize, _retained, fields⟩ := nativeFields both.2
  refine ⟨oracle, hdecode, hsize, ?_⟩
  dsimp only
  intro j
  exact ⟨((childTapes _).trans (congrFun tapesEq _)).trans (fields j).1,
    ((childHeads _).trans (congrFun headsEq _)).trans (fields j).2⟩

/-- The cache and actual admission flag come from the same original-input run. -/
theorem bounded_cache (a : PointwisePCPPAlgorithm)
    (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hpad : k + 3 ≤ Cpad) (hD : 1 ≤ D) (hsym : 0 < symDen) (hthr : 0 < thrDen) (hK : 0 < K)
    (hcut : 2 ^ a.minimumArity ≤ cutoff) (hd : 0 < delta) (hh : delta < 1 / 2) (hc : 1 ≤ copies)
    (hbudget : ∀ N, FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)
      ≤ K * (N + 1) ^ E) :
    let km := CloseoutMassThreshold.literalWidth delta copies
    let q := CloseoutSampledWitness.massCap delta copies
    let fuel := 2 * BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen
      delta code x bits hpad
    ∃ actual, run (BoundedFamilySupport.actualMachine source a k CH Cpad cutoff D G copies E K
        symDen thrDen km delta q code) fuel
      (BoundedFamilySupport.input source a k D G E (List.ofFn x) bits) = some actual ∧
      actual.steps ≤ fuel ∧ actual.final.heads (BoundedFamilySupport.flag source a k D G E) = 0 ∧
      readTapeBit (actual.final.tapes (BoundedFamilySupport.flag source a k D G E)) 0 =
        BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad ∧
      (BoundedFamily.headerValid (List.ofFn x) bits = true →
        BoundedFamilySupport.Selected source a k CH Cpad cutoff D G copies E K symDen thrDen km
          delta q code x bits hpad (BoundedFields.symmetric bits) actual.final.heads actual.final.tapes) ∧
      (BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad = true →
        Cached source a k CH Cpad D G E code x bits hpad actual.final.heads actual.final.tapes) := by
  let existence := BoundedFamilySupport.bounded_run source a k CH Cpad cutoff D G copies E K symDen thrDen
    delta code x bits hpad hD hsym hthr hK hcut hd hh hc hbudget
  let actual := Classical.choose existence
  have facts := Classical.choose_spec existence
  refine ⟨actual, facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2, ?_⟩
  exact cached_of_selected source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits
    hpad hD hsym hthr hK hcut hd hh hc hbudget _ _ facts.2.2.2.2

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdCacheAtAdmission
