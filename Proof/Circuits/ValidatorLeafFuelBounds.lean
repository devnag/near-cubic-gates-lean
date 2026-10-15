import Proof.Circuits.ValidatorLeafWidthCore

namespace NearCubicWires.ValidatorLeafFuelBounds

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## §1 The counting ledgers -/

/-- The raw structural normalizer charges at most `35` steps per decoded
node. -/
theorem rawBalancedTraversalSteps_le (tree : RawBalancedTraversalTree) :
    rawBalancedTraversalSteps tree ≤ 35 * tree.nodeCount := by
  induction tree with
  | empty =>
      simp [rawBalancedTraversalSteps, RawBalancedTraversalTree.nodeCount]
  | leaf tag atom =>
      simp [rawBalancedTraversalSteps, RawBalancedTraversalTree.nodeCount]
  | branch tag left right ihLeft ihRight =>
      simp only [rawBalancedTraversalSteps, RawBalancedTraversalTree.nodeCount]
      omega

theorem balancedStructuralNormalizeFuel_le (tree : RawBalancedTraversalTree) :
    balancedStructuralNormalizeFuel tree ≤ 35 * tree.nodeCount + 2 := by
  have hsteps := rawBalancedTraversalSteps_le tree
  unfold balancedStructuralNormalizeFuel
  omega

theorem popFuel_le (forest : List BalancedTraversalTree) :
    popFuel forest ≤ 5 := by
  cases forest with
  | nil => simp [popFuel]
  | cons head tail => simp [popFuel]

/-- The flattener's phase loop charges a constant per node plus eight per
decoded stream element. -/
theorem phaseFuel_le (forest : List BalancedTraversalTree) :
    phaseFuel forest ≤
      16 * (forest.map BalancedTraversalTree.nodeCount).sum +
        8 * (forestStreamValues forest).length := by
  induction forest using phaseFuel.induct with
  | case1 => simp [phaseFuel]
  | case2 rest inductionHypothesis =>
      have hpop := popFuel_le rest
      simp only [phaseFuel, forestStreamValues, treeStreamValues,
        BalancedTraversalTree.nodeCount, BalancedTraversalTree.atoms,
        List.flatMap_cons, List.flatMap_nil,
        List.map_cons, List.sum_cons,
        List.nil_append] at inductionHypothesis ⊢
      omega
  | case3 atom rest inductionHypothesis =>
      have hpop := popFuel_le rest
      simp only [phaseFuel, forestStreamValues, treeStreamValues,
        BalancedTraversalTree.nodeCount, BalancedTraversalTree.atoms,
        List.flatMap_cons, List.flatMap_nil,
        List.map_cons, List.sum_cons, List.length_append,
        List.append_nil] at inductionHypothesis ⊢
      omega
  | case4 left right rest inductionHypothesis =>
      simp only [phaseFuel, forestStreamValues, treeStreamValues,
        BalancedTraversalTree.nodeCount, BalancedTraversalTree.atoms,
        List.flatMap_cons, List.flatMap_append,
        List.map_cons, List.sum_cons, List.length_append]
        at inductionHypothesis ⊢
      omega

/-- The structural-tree flattener, charged by node count and stream length. -/
theorem balancedTreeStreamFlattenFuel_le (tree : BalancedTraversalTree) :
    balancedTreeStreamFlattenFuel tree ≤
      16 * tree.nodeCount + 16 * (treeStreamValues tree).length + 7 := by
  have hphase := phaseFuel_le [tree]
  simp only [forestStreamValues, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hphase
  unfold balancedTreeStreamFlattenFuel
  omega

/-- The singleton-tagging traversal, charged by node count. -/
theorem balancedBitSingletonTreeFuel_le (tree : BalancedTraversalTree) :
    balancedBitSingletonTreeFuel tree ≤ 39 * tree.nodeCount + 2 := by
  have hstructural := balancedTraversalStructuralSteps_le_nodeCount tree
  have hatoms := atoms_length_le_nodeCount tree
  unfold balancedBitSingletonTreeFuel
  omega

/-- The balanced builder's dispatcher, charged by list length.  The recursive
case splits into two *nonempty* halves, so the constant per internal node is
absorbed by the per-element charge. -/
private theorem balancedBuildFuel_le_aux :
    ∀ length : ℕ, ∀ values : List ℕ, values.length = length → 1 ≤ length →
      balancedBuildFuel values + 29 ≤ 37 * length := by
  intro length
  induction length using Nat.strong_induction_on with
  | h length inductionHypothesis =>
      intro values hlength hpositive
      match values with
      | [] =>
          exfalso
          simp only [List.length_nil] at hlength
          omega
      | [value] =>
          have hone : length = 1 := by
            simp only [List.length_cons, List.length_nil] at hlength
            omega
          subst hone
          simp [balancedBuildFuel]
      | first :: second :: rest =>
          have hlen : (first :: second :: rest).length = rest.length + 2 := by
            simp
          have hcount : rest.length + 2 = length := by
            rw [← hlen]
            exact hlength
          have hunfold :
              balancedBuildFuel (first :: second :: rest) =
                29 +
                    balancedBuildFuel
                      ((first :: second :: rest).take
                        (((first :: second :: rest).length + 1) / 2)) +
                  balancedBuildFuel
                    ((first :: second :: rest).drop
                      (((first :: second :: rest).length + 1) / 2)) := by
            rw [balancedBuildFuel]
          have hleftLength :
              ((first :: second :: rest).take
                  ((rest.length + 2 + 1) / 2)).length =
                (rest.length + 2 + 1) / 2 := by
            rw [List.length_take, hlen]
            omega
          have hrightLength :
              ((first :: second :: rest).drop
                  ((rest.length + 2 + 1) / 2)).length =
                rest.length + 2 - (rest.length + 2 + 1) / 2 := by
            rw [List.length_drop, hlen]
          have hleft :=
            inductionHypothesis ((rest.length + 2 + 1) / 2) (by omega) _
              hleftLength (by omega)
          have hright :=
            inductionHypothesis (rest.length + 2 - (rest.length + 2 + 1) / 2)
              (by omega) _ hrightLength (by omega)
          rw [hunfold, hlen]
          omega

theorem balancedBuildFuel_le (values : List ℕ) :
    balancedBuildFuel values ≤ 37 * values.length + 3 := by
  cases hvalues : values with
  | nil => simp [balancedBuildFuel]
  | cons value rest =>
      have haux :=
        balancedBuildFuel_le_aux (value :: rest).length (value :: rest) rfl
          (by simp)
      omega

theorem taggedToBalancedFuel_le (values : List ℕ) :
    taggedToBalancedFuel values ≤ 42 * values.length + 14 := by
  have hbuild := balancedBuildFuel_le values
  unfold taggedToBalancedFuel
  omega

/-- The nonzero-count traversal, charged by node count. -/
theorem supplierSupportCountWorkFuel_le (forest : List BalancedTraversalTree) :
    supplierSupportCountWorkFuel forest ≤
      15 * (forest.map BalancedTraversalTree.nodeCount).sum + 5 := by
  induction forest using supplierSupportCountWorkFuel.induct with
  | case1 => simp [supplierSupportCountWorkFuel]
  | case2 rest inductionHypothesis =>
      simp only [supplierSupportCountWorkFuel, List.map_cons, List.sum_cons,
        BalancedTraversalTree.nodeCount] at inductionHypothesis ⊢
      omega
  | case3 atom rest inductionHypothesis =>
      have hstep : (if atom = 0 then 11 else 12) ≤ 12 := by split <;> omega
      simp only [supplierSupportCountWorkFuel, List.map_cons, List.sum_cons,
        BalancedTraversalTree.nodeCount] at inductionHypothesis ⊢
      omega
  | case4 left right rest inductionHypothesis =>
      simp only [supplierSupportCountWorkFuel, List.map_cons, List.sum_cons,
        BalancedTraversalTree.nodeCount] at inductionHypothesis ⊢
      omega

/-- The midpoint tree over `n` atoms has fewer than `2n + 1` nodes. -/
theorem balancedTraversalTree_nodeCount_le (values : List ℕ) :
    (balancedTraversalTree values).nodeCount ≤ 2 * values.length + 1 := by
  rw [balancedTraversalTree_nodeCount]
  split <;> omega

/-! ## §2 The balanced canonicalization pipeline

Every node of the pipeline is a linker or a context-preserving wrapper, so the
whole of it stays at the degree of the *node count* certificate it is handed. -/

private theorem length_flatMap_singletonTaggedBit (values : List ℕ) :
    ((values.map singletonTaggedBit).flatMap streamOfCode).length =
      values.length := by
  induction values with
  | nil => simp
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, List.length_append,
        List.length_cons, singletonTaggedBit, streamOfCode_encodeTaggedList,
        List.length_nil, inductionHypothesis]
      omega

theorem treeStreamValues_map_singletonTaggedBit_length
    (tree : BalancedTraversalTree) :
    (treeStreamValues (tree.map singletonTaggedBit)).length =
      tree.atoms.length := by
  simp only [treeStreamValues, BalancedTraversalTree.atoms_map]
  exact length_flatMap_singletonTaggedBit tree.atoms

/-- **The canonicalizer, dominated.**  Three counted traversals over the same
decoded tree; each is linear in the node count, so the stage is
degree-preserving over the node-count certificate. -/
theorem balancedCanonicalizeFuel_polyBounded
    {tree : BalancedTraversalTree} {measure coefficient degree : ℕ}
    (hnodes : PolyBounded tree.nodeCount measure coefficient degree) :
    PolyBounded (balancedCanonicalizeFuel tree) measure
      (programRegisterSpan taggedToBalancedProgram + 5 +
          (programRegisterSpan balancedClauseStreamFlattenProgram + 5 +
              (39 * coefficient + 2) +
            (32 * coefficient + 7)) +
        (42 * coefficient + 14)) degree := by
  have hatoms : tree.atoms.length ≤ tree.nodeCount :=
    atoms_length_le_nodeCount tree
  have hsingleton :
      PolyBounded (balancedBitSingletonTreeFuel tree) measure
        (39 * coefficient + 2) degree := by
    refine (((hnodes.const_mul 39).add
      (polyBounded_const 2 measure degree))).mono ?_
    exact balancedBitSingletonTreeFuel_le tree
  have hflatten :
      PolyBounded
        (balancedTreeStreamFlattenFuel (tree.map singletonTaggedBit)) measure
        (32 * coefficient + 7) degree := by
    refine (((hnodes.const_mul 32).add
      (polyBounded_const 7 measure degree))).mono ?_
    have hbound :=
      balancedTreeStreamFlattenFuel_le (tree.map singletonTaggedBit)
    rw [treeStreamValues_map_singletonTaggedBit_length tree,
      BalancedTraversalTree.nodeCount_map] at hbound
    omega
  have hbuilder :
      PolyBounded (taggedToBalancedFuel tree.atoms) measure
        (42 * coefficient + 14) degree := by
    refine (((hnodes.const_mul 42).add
      (polyBounded_const 14 measure degree))).mono ?_
    have hbound := taggedToBalancedFuel_le tree.atoms
    omega
  have hinner :=
    linkFuel_polyBounded (second := balancedClauseStreamFlattenProgram)
      hsingleton hflatten
  exact linkFuel_polyBounded (second := taggedToBalancedProgram) hinner hbuilder

/-- **The raw canonicalizer, dominated.** -/
theorem balancedRawCanonicalizeFuel_polyBounded
    {tree : RawBalancedTraversalTree} {measure coefficient degree : ℕ}
    (hnodes : PolyBounded tree.nodeCount measure coefficient degree) :
    PolyBounded (balancedRawCanonicalizeFuel tree) measure
      (programRegisterSpan balancedCanonicalizeProgram + 5 +
          (35 * coefficient + 2) +
        (programRegisterSpan taggedToBalancedProgram + 5 +
            (programRegisterSpan balancedClauseStreamFlattenProgram + 5 +
                (39 * coefficient + 2) +
              (32 * coefficient + 7)) +
          (42 * coefficient + 14))) degree := by
  have hnormalize :
      PolyBounded (balancedStructuralNormalizeFuel tree) measure
        (35 * coefficient + 2) degree := by
    refine (((hnodes.const_mul 35).add
      (polyBounded_const 2 measure degree))).mono ?_
    exact balancedStructuralNormalizeFuel_le tree
  have hnormalized :
      PolyBounded tree.normalized.nodeCount measure coefficient degree := by
    rw [nodeCount_normalized]
    exact hnodes
  exact linkFuel_polyBounded (second := balancedCanonicalizeProgram)
    hnormalize (balancedCanonicalizeFuel_polyBounded hnormalized)

theorem nativeNatEqFuel_polyBounded
    {left right measure leftCoefficient rightCoefficient degree : ℕ}
    (hleft : PolyBounded (natBitLength left) measure leftCoefficient degree)
    (hright : PolyBounded (natBitLength right) measure rightCoefficient degree) :
    PolyBounded (nativeNatEqFuel left right) measure
      (programRegisterSpan nativeNatEqCoreProgram + 5 + 6 +
        (programRegisterSpan nativeNatEqGateProgram + 5 +
            (pairedCallOverhead nativeNatLeProgram +
                (36 * max leftCoefficient rightCoefficient + 8) +
              (36 * max rightCoefficient leftCoefficient + 8)) +
          6)) degree := by
  have hforward :=
    NearCubicWires.ValidatorLegalSumWalk.nativeNatLeFuel_polyBounded hleft
      hright
  have hbackward :=
    NearCubicWires.ValidatorLegalSumWalk.nativeNatLeFuel_polyBounded hright
      hleft
  have hcompare :
      PolyBounded (nativeNatEqCompareFuel left right) measure
        (pairedCallOverhead nativeNatLeProgram +
            (36 * max leftCoefficient rightCoefficient + 8) +
          (36 * max rightCoefficient leftCoefficient + 8)) degree :=
    pairedCallFuel_polyBounded (source := nativeNatLeProgram) hforward hbackward
  have hcore :=
    linkFuel_polyBounded (second := nativeNatEqGateProgram) hcompare
      (polyBounded_const 6 measure degree)
  exact linkFuel_polyBounded (second := nativeNatEqCoreProgram)
    (polyBounded_const 6 measure degree) hcore

theorem balancedTrueTreeFuel_le (values : List ℕ) :
    balancedTrueTreeFuel values ≤ 71 * values.length + 37 := by
  have hstructural := balancedTraversalStructuralSteps_le_linear values
  unfold balancedTrueTreeFuel
  omega

theorem balancedBoolCountFuel_polyBounded
    {values : List Bool} {measure coefficient degree : ℕ}
    (hlength : PolyBounded values.length measure coefficient degree) :
    PolyBounded (balancedBoolCountFuel values) measure
      (programRegisterSpan balancedBoolCountProjectionProgram + 5 +
        (30 * coefficient + 27) + 5) degree := by
  have hwork :
      PolyBounded (supplierSupportCountPrepareFuel values) measure
        (30 * coefficient + 27) degree := by
    refine (((hlength.const_mul 30).add
      (polyBounded_const 27 measure degree))).mono ?_
    have hforest :=
      supplierSupportCountWorkFuel_le
        [balancedTraversalTree (values.map boolCode)]
    have hnodes :=
      balancedTraversalTree_nodeCount_le (values.map boolCode)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_map] at hforest hnodes
    unfold supplierSupportCountPrepareFuel
    omega
  exact linkFuel_polyBounded (second := balancedBoolCountProjectionProgram)
    hwork (polyBounded_const 5 measure degree)

theorem balancedLengthFuel_polyBounded
    {values : List ℕ} {measure coefficient degree : ℕ}
    (hlength : PolyBounded values.length measure coefficient degree) :
    PolyBounded (balancedLengthFuel values) measure
      (programRegisterSpan
            (linkPrograms balancedLengthCountInputProgram <|
              linkPrograms balancedBoolCountProgram
                balancedLengthProjectionProgram) + 5 +
          (71 * coefficient + 37) +
        (programRegisterSpan
              (linkPrograms balancedBoolCountProgram
                balancedLengthProjectionProgram) + 5 + 3 +
          (programRegisterSpan balancedLengthProjectionProgram + 5 +
              (programRegisterSpan balancedBoolCountProjectionProgram + 5 +
                (30 * coefficient + 27) + 5) +
            2))) degree := by
  have htrue :
      PolyBounded (balancedTrueTreeFuel values) measure
        (71 * coefficient + 37) degree := by
    refine (((hlength.const_mul 71).add
      (polyBounded_const 37 measure degree))).mono ?_
    exact balancedTrueTreeFuel_le values
  have htrueLength :
      PolyBounded (balancedTrueValues values).length measure coefficient
        degree := by
    have hlen : (balancedTrueValues values).length = values.length := by
      simp [balancedTrueValues]
    rw [hlen]
    exact hlength
  have hcount := balancedBoolCountFuel_polyBounded htrueLength
  have hinner :=
    linkFuel_polyBounded (second := balancedLengthProjectionProgram) hcount
      (polyBounded_const 2 measure degree)
  have houter :=
    linkFuel_polyBounded
      (second :=
        linkPrograms balancedBoolCountProgram balancedLengthProjectionProgram)
      (polyBounded_const 3 measure degree) hinner
  exact linkFuel_polyBounded
    (second :=
      linkPrograms balancedLengthCountInputProgram <|
        linkPrograms balancedBoolCountProgram balancedLengthProjectionProgram)
    htrue houter

/-- The decoded node count, from the raw code's width: degree-preserving. -/
theorem polyBounded_rawBalancedTraversalTree_nodeCount
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (rawBalancedTraversalTree raw).nodeCount measure
      (2 * coefficient) degree := by
  refine (hraw.const_mul 2).mono ?_
  have hnodes := rawBalancedTraversalTree_nodeCount_succ_le raw
  omega

/-- The canonicalization prepare stage, dominated. -/
theorem balancedCanonicalityPrepareFuel_polyBounded
    {tree : RawBalancedTraversalTree} {measure coefficient degree : ℕ}
    (hnodes : PolyBounded tree.nodeCount measure coefficient degree) :
    PolyBounded (balancedCanonicalityPrepareFuel tree) measure
      (programRegisterSpan (preserveRightProgram balancedRawCanonicalizeProgram) +
          5 + 2 +
        ((programRegisterSpan balancedCanonicalizeProgram + 5 +
              (35 * coefficient + 2) +
            (programRegisterSpan taggedToBalancedProgram + 5 +
                (programRegisterSpan balancedClauseStreamFlattenProgram + 5 +
                    (39 * coefficient + 2) +
                  (32 * coefficient + 7)) +
              (42 * coefficient + 14))) + 4)) degree :=
  linkFuel_polyBounded
    (second := preserveRightProgram balancedRawCanonicalizeProgram)
    (polyBounded_const 2 measure degree)
    (preserveRightFuel_polyBounded
      (balancedRawCanonicalizeFuel_polyBounded hnodes))

theorem balancedCanonicalityFuel_polyBounded
    {raw measure coefficient reencodeCoefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree)
    (hreencode :
      PolyBounded
        (natBitLength
          (encodeBalancedList (rawBalancedTraversalTree raw).atoms)) measure
        reencodeCoefficient degree) :
    PolyBounded (balancedCanonicalityFuel raw) measure
      (programRegisterSpan nativeNatEqProgram + 5 +
          (programRegisterSpan
                (preserveRightProgram balancedRawCanonicalizeProgram) + 5 + 2 +
            ((programRegisterSpan balancedCanonicalizeProgram + 5 +
                  (35 * (2 * coefficient) + 2) +
                (programRegisterSpan taggedToBalancedProgram + 5 +
                    (programRegisterSpan balancedClauseStreamFlattenProgram +
                        5 + (39 * (2 * coefficient) + 2) +
                      (32 * (2 * coefficient) + 7)) +
                  (42 * (2 * coefficient) + 14))) + 4)) +
        (programRegisterSpan nativeNatEqCoreProgram + 5 + 6 +
          (programRegisterSpan nativeNatEqGateProgram + 5 +
              (pairedCallOverhead nativeNatLeProgram +
                  (36 * max reencodeCoefficient coefficient + 8) +
                (36 * max coefficient reencodeCoefficient + 8)) +
            6))) degree := by
  have hnodes := polyBounded_rawBalancedTraversalTree_nodeCount hraw
  have hprepare := balancedCanonicalityPrepareFuel_polyBounded hnodes
  have hrawCode : (rawBalancedTraversalTree raw).rawCode = raw :=
    rawBalancedTraversalTree_rawCode raw
  have hequality :
      PolyBounded
        (nativeNatEqFuel
          (encodeBalancedList (rawBalancedTraversalTree raw).atoms)
          (rawBalancedTraversalTree raw).rawCode) measure
        (programRegisterSpan nativeNatEqCoreProgram + 5 + 6 +
          (programRegisterSpan nativeNatEqGateProgram + 5 +
              (pairedCallOverhead nativeNatLeProgram +
                  (36 * max reencodeCoefficient coefficient + 8) +
                (36 * max coefficient reencodeCoefficient + 8)) +
            6)) degree := by
    rw [hrawCode]
    exact nativeNatEqFuel_polyBounded hreencode hraw
  have hnode :=
    linkFuel_polyBounded (second := nativeNatEqProgram) hprepare hequality
  exact hnode

/-- **The validation-map guard, dominated.** -/
theorem balancedValidationMapGuardFuel_polyBounded
    {raw measure canonicalityCoefficient degree : ℕ}
    (hcanonicality :
      PolyBounded (balancedCanonicalityFuel raw) measure canonicalityCoefficient
        degree) :
    PolyBounded (balancedValidationMapGuardFuel raw) measure
      (programRegisterSpan balancedValidationMapGuardGateProgram + 5 +
          (programRegisterSpan (preserveRightProgram balancedCanonicalityProgram) +
              5 + 2 + (canonicalityCoefficient + 4)) +
        balancedValidationMapGuardGateFuel) degree := by
  have hinner :=
    linkFuel_polyBounded
      (second := preserveRightProgram balancedCanonicalityProgram)
      (polyBounded_const 2 measure degree)
      (preserveRightFuel_polyBounded hcanonicality)
  exact linkFuel_polyBounded
    (second := balancedValidationMapGuardGateProgram) hinner
    (polyBounded_const balancedValidationMapGuardGateFuel measure degree)

theorem balancedCanonicalityFuel_degree
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    ∃ canonicalityCoefficient : ℕ,
      PolyBounded (balancedCanonicalityFuel raw) measure canonicalityCoefficient
        (degree + degree) := by
  have hraised :
      PolyBounded (natBitLength raw) measure coefficient (degree + degree) :=
    hraw.degree_mono (by omega)
  have hreencode := polyBounded_natBitLength_encodeBalancedList_atoms hraw
  exact ⟨_, balancedCanonicalityFuel_polyBounded hraised hreencode⟩

theorem balancedValidationMapGuardFuel_degree
    {raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    ∃ guardCoefficient : ℕ,
      PolyBounded (balancedValidationMapGuardFuel raw) measure guardCoefficient
        (degree + degree) := by
  obtain ⟨canonicalityCoefficient, hcanonicality⟩ :=
    balancedCanonicalityFuel_degree hraw
  exact ⟨_, balancedValidationMapGuardFuel_polyBounded hcanonicality⟩

end NearCubicWires.ValidatorLeafFuelBounds
