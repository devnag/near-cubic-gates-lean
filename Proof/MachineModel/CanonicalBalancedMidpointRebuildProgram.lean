import Proof.MachineModel.CanonicalBalancedAtomIndexProgram
import Proof.MachineModel.CanonicalBalancedValidationProgram
import Proof.MachineModel.CanonicalGateAtomHeadListProgram

/-!
# The midpoint canonicalizer, rebuilt by index

`CanonicalBalancedValidationProgram.balancedCanonicalizeProgram` maps every
atom of a structural balanced tree to its own tagged singleton, folds the tree
into one `encodeTaggedList tree.atoms`, and rebuilds the canonical midpoint
code from that stream.  `ValidatorTaggedIntermediateVerdict` §3 shows the
middle step returns a value of width at least `2 ^ tree.atoms.length`, so the
stage's charge is geometric in the *public* atom count at a value the machine
actually produces.  No retuning of `balancedCanonicalizeBits` can repair that;
only a different program can.

This module is that program.  The linked intermediate is replaced by
**indexing**, which needs no cons list at all:

1. `balancedAtomCountProgram` folds the atom count off the shared traversal
   and returns it beside the untouched input code — which is exactly
   `generatedBalancedRangeInput`;

2. `atomRequestListProgram` over the identity stage turns that pair into the
   canonical balanced list of requests `Nat.pair index tree.code`, one per
   atom index.  Every intermediate here is a *midpoint* balanced code, so
   `CanonicalBalancedCall`'s fixed polynomial already covers it;

3. `balancedCallProgram balancedAtomSelectProgram` maps each request to the
   atom at its index.  The balanced-call request ABI hands a callee the
   request's left component as its native input length, which is precisely
   where `balancedAtomSelectProgram` reads its index, and the callee's output
   list is returned as one canonical balanced code.

The composite's output contract is `balancedCanonicalizeProgram`'s own —
`some (encodeBalancedList tree.atoms)` at `initialNPOracleState inputLength
tree.code` — so it is a drop-in replacement and nothing above restates.

* §1 the identity stage and the request family.

* §2 the rebuilt canonicalizer, executed.

* §3 the raw front door, executed.

* §4 the charge, in balanced measurements only.
-/

namespace NearCubicWires.CanonicalBalancedMidpointRebuildProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedAtomIndexProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hmem
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

private theorem foldr_max_le
    {values : List ℕ} {base bound : ℕ} (hbase : base ≤ bound)
    (hvalues : ∀ value ∈ values, value ≤ bound) :
    values.foldr max base ≤ bound := by
  induction values with
  | nil => simpa using hbase
  | cons head tail inductionHypothesis =>
      simp only [List.foldr]
      exact max_le (hvalues head (by simp))
        (inductionHypothesis fun value hvalue =>
          hvalues value (by simp [hvalue]))

private theorem natBitLength_mono' {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.succ_le_succ (Nat.log_mono_right hle)

/-! ## §1 The identity stage and the request family -/

def identityStageProgram : NPOracleProgram := [ .halt 0 ]

@[simp] theorem identityStageProgram_oracleFree :
    OracleFree identityStageProgram := by
  rfl

theorem run_identityStageProgram
    (inputLength value maximumBits : ℕ)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram identityStageProgram maximumBits 1
        (initialNPOracleState inputLength value) =
      some value :=
  run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [initialNPOracleState]) hbits

/-- One request per atom index, all against the same input code. -/
def atomIndexRequests (tree : BalancedTraversalTree) : List ℕ :=
  (List.range tree.atoms.length).map fun index => Nat.pair index tree.code

/-- The atom a request selects. -/
def atomIndexOutput (tree : BalancedTraversalTree) (request : ℕ) : ℕ :=
  tree.atoms.getD (Nat.unpair request).1 0

/-- **Reading every index rebuilds the atom list.** -/
theorem map_atomIndexOutput (tree : BalancedTraversalTree) :
    (atomIndexRequests tree).map (atomIndexOutput tree) = tree.atoms := by
  have hmap :
      (atomIndexRequests tree).map (atomIndexOutput tree) =
        (List.range tree.atoms.length).map
          (fun index => tree.atoms.getD index 0) := by
    simp only [atomIndexRequests, List.map_map]
    refine List.map_congr_left ?_
    intro index _hindex
    simp [atomIndexOutput]
  rw [hmap, map_range_getD]

theorem mem_atomIndexRequests
    {tree : BalancedTraversalTree} {index : ℕ}
    (hindex : index < tree.atoms.length) :
    Nat.pair index tree.code ∈ atomIndexRequests tree :=
  List.mem_map.mpr ⟨index, List.mem_range.mpr hindex, rfl⟩

/-- Width of every emitted request. -/
def atomIndexRequestBits (tree : BalancedTraversalTree) : ℕ :=
  ((atomIndexRequests tree).map natBitLength).foldr max 1

/-- Width of every selecting callee run. -/
def atomIndexSelectBits (tree : BalancedTraversalTree) : ℕ :=
  ((List.range tree.atoms.length).map fun index =>
    balancedAtomSelectBits index tree).foldr max 1

theorem atomIndexRequestBits_of_mem
    {tree : BalancedTraversalTree} {index : ℕ}
    (hindex : index < tree.atoms.length) :
    natBitLength (Nat.pair index tree.code) ≤ atomIndexRequestBits tree :=
  le_foldr_max_of_mem
    (List.mem_map.mpr ⟨_, mem_atomIndexRequests hindex, rfl⟩)

theorem atomIndexSelectBits_of_mem
    {tree : BalancedTraversalTree} {index : ℕ}
    (hindex : index < tree.atoms.length) :
    balancedAtomSelectBits index tree ≤ atomIndexSelectBits tree :=
  le_foldr_max_of_mem
    (List.mem_map.mpr ⟨index, List.mem_range.mpr hindex, rfl⟩)

/-! ## §2 The rebuilt canonicalizer -/

/-- **The repaired midpoint canonicalizer.**  Count, generate one request per
index, then select.  Nothing in the chain is a tagged public list. -/
def balancedCanonicalizeFoldProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms balancedAtomCountProgram
      (atomRequestListProgram identityStageProgram))
    (balancedCallProgram balancedAtomSelectProgram)

@[simp] theorem balancedCanonicalizeFoldProgram_oracleFree :
    OracleFree balancedCanonicalizeFoldProgram :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms balancedAtomCountProgram_oracleFree
      (atomRequestListProgram_oracleFree identityStageProgram
        identityStageProgram_oracleFree))
    (balancedCallProgram_oracleFree balancedAtomSelectProgram_oracleFree)

def balancedCanonicalizeFoldFuel
    (inputLength : ℕ) (tree : BalancedTraversalTree) : ℕ :=
  linkFuel (balancedCallProgram balancedAtomSelectProgram)
    (linkFuel (atomRequestListProgram identityStageProgram)
      (balancedAtomCountFuel tree)
      (indexedAtomListFuel identityStageProgram inputLength
        tree.atoms.length tree.code (fun _index => 1)))
    (balancedCallFuel balancedAtomSelectProgram
      (fun _request => balancedAtomSelectFuel tree) (atomIndexRequests tree))

def balancedCanonicalizeFoldStageBits
    (inputLength : ℕ) (tree : BalancedTraversalTree) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , balancedAtomCountBits inputLength tree
  , indexedAtomListBits inputLength tree.atoms.length tree.code
      (fun index => Nat.pair index tree.code)
  , atomIndexRequestBits tree
  , balancedCallRequiredBits (atomIndexOutput tree) (atomIndexRequests tree)
  , atomIndexSelectBits tree
  ]

/-- The repaired canonicalizer's charge.  Compare
`ValidatorTaggedIntermediateVerdict.two_pow_atoms_le_balancedCanonicalizeBits`:
no summand here is a tagged list of the public atoms. -/
def balancedCanonicalizeFoldBits
    (inputLength : ℕ) (tree : BalancedTraversalTree) : ℕ :=
  (balancedCanonicalizeFoldStageBits inputLength tree).foldr max 1

theorem balancedCanonicalizeFoldBits_of_mem
    {inputLength : ℕ} {tree : BalancedTraversalTree} {value : ℕ}
    (hmem : value ∈ balancedCanonicalizeFoldStageBits inputLength tree) :
    value ≤ balancedCanonicalizeFoldBits inputLength tree :=
  le_foldr_max_of_mem hmem

/-- **The repaired canonicalizer returns the published canonical code.**  The
output contract is `run_balancedCanonicalizeProgram`'s own, unchanged. -/
theorem run_balancedCanonicalizeFoldProgram
    (inputLength : ℕ) (tree : BalancedTraversalTree) :
    runNPOracleProgram balancedCanonicalizeFoldProgram
        (balancedCanonicalizeFoldBits inputLength tree)
        (balancedCanonicalizeFoldFuel inputLength tree)
        (initialNPOracleState inputLength tree.code) =
      some (encodeBalancedList tree.atoms) := by
  let maximumBits := balancedCanonicalizeFoldBits inputLength tree
  have bits_of_member {value : ℕ}
      (hmem : value ∈ balancedCanonicalizeFoldStageBits inputLength tree) :
      value ≤ maximumBits :=
    balancedCanonicalizeFoldBits_of_mem hmem
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [balancedCanonicalizeFoldStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [balancedCanonicalizeFoldStageBits]
  have hcount :
      runNPOracleProgram balancedAtomCountProgram maximumBits
          (balancedAtomCountFuel tree)
          (initialNPOracleState inputLength tree.code) =
        some (generatedBalancedRangeInput tree.atoms.length tree.code) := by
    refine run_bits_mono (run_balancedAtomCountProgram inputLength tree) ?_
    apply bits_of_member
    simp [balancedCanonicalizeFoldStageBits]
  have hrequestBits : atomIndexRequestBits tree ≤ maximumBits := by
    apply bits_of_member
    simp [balancedCanonicalizeFoldStageBits]
  have hlist :
      runNPOracleProgram (atomRequestListProgram identityStageProgram)
          maximumBits
          (indexedAtomListFuel identityStageProgram inputLength
            tree.atoms.length tree.code (fun _index => 1))
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput tree.atoms.length tree.code)) =
        some (encodeBalancedList (atomIndexRequests tree)) := by
    have hrun :=
      run_indexedAtomRequestListProgram identityStageProgram inputLength
        tree.atoms.length tree.code maximumBits (fun _index => 1)
        (fun index => Nat.pair index tree.code)
        (by
          apply bits_of_member
          simp [balancedCanonicalizeFoldStageBits])
        (by
          intro index hindex
          exact run_identityStageProgram inputLength
            (Nat.pair index tree.code) maximumBits
            ((atomIndexRequestBits_of_mem hindex).trans hrequestBits))
    simpa [atomIndexRequests] using hrun
  have hselect :
      runNPOracleProgram (balancedCallProgram balancedAtomSelectProgram)
          maximumBits
          (balancedCallFuel balancedAtomSelectProgram
            (fun _request => balancedAtomSelectFuel tree)
            (atomIndexRequests tree))
          (initialNPOracleState inputLength
            (encodeBalancedList (atomIndexRequests tree))) =
        some (encodeBalancedList tree.atoms) := by
    have hrequired :
        balancedCallRequiredBits (atomIndexOutput tree)
            (atomIndexRequests tree) ≤ maximumBits := by
      apply bits_of_member
      simp [balancedCanonicalizeFoldStageBits]
    have hselectBits : atomIndexSelectBits tree ≤ maximumBits := by
      apply bits_of_member
      simp [balancedCanonicalizeFoldStageBits]
    have hexec :
        ∀ request, request ∈ atomIndexRequests tree →
          runNPOracleProgram balancedAtomSelectProgram maximumBits
              (balancedAtomSelectFuel tree)
              (initialNPOracleState (Nat.unpair request).1
                (Nat.unpair request).2) =
            some (atomIndexOutput tree request) := by
      intro request hrequest
      rcases List.mem_map.mp hrequest with ⟨index, hindexMem, hrequestEq⟩
      have hindex : index < tree.atoms.length := List.mem_range.mp hindexMem
      subst hrequestEq
      have hrun :=
        run_bits_mono (run_balancedAtomSelectProgram index tree)
          ((atomIndexSelectBits_of_mem hindex).trans hselectBits)
      have hvalue :
          atomSelectValue index 0 0 tree.atoms =
            atomIndexOutput tree (Nat.pair index tree.code) := by
        simp only [atomIndexOutput, Nat.unpair_pair]
        exact atomSelectValue_zero index tree.atoms hindex
      rw [hvalue] at hrun
      simpa using hrun
    have hcall :=
      run_balancedCallProgram_from (callee := balancedAtomSelectProgram)
        (maximumBits := maximumBits) inputLength (atomIndexRequests tree)
        (fun _request => balancedAtomSelectFuel tree) (atomIndexOutput tree)
        hrequired hexec
    rwa [map_atomIndexOutput] at hcall
  apply run_linkPrograms hpositive hlength
  · exact run_linkPrograms hpositive hlength hcount hlist
  · exact hselect

/-! ## §3 The raw front door -/

/-- The raw normalization seam is untouched; only the canonicalizer behind it
changes. -/
def balancedRawCanonicalizeFoldProgram : NPOracleProgram :=
  linkPrograms balancedStructuralNormalizeProgram
    balancedCanonicalizeFoldProgram

@[simp] theorem balancedRawCanonicalizeFoldProgram_oracleFree :
    OracleFree balancedRawCanonicalizeFoldProgram :=
  oracleFree_linkPrograms balancedStructuralNormalizeProgram_oracleFree
    balancedCanonicalizeFoldProgram_oracleFree

def balancedRawCanonicalizeFoldFuel
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) : ℕ :=
  linkFuel balancedCanonicalizeFoldProgram
    (balancedStructuralNormalizeFuel tree)
    (balancedCanonicalizeFoldFuel inputLength tree.normalized)

/-- **The repaired raw canonicalizer's charge.**  The same shape
`balancedRawCanonicalizeBits` has, with the geometric summand replaced. -/
def balancedRawCanonicalizeFoldBits
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (balancedStructuralNormalizeBits inputLength tree)
      (balancedCanonicalizeFoldBits inputLength tree.normalized)

/-- **The repaired raw canonicalizer returns the published canonical code.** -/
theorem run_balancedRawCanonicalizeFoldProgram
    (inputLength : ℕ) (tree : RawBalancedTraversalTree)
    (hvalid : tree.Valid) :
    runNPOracleProgram balancedRawCanonicalizeFoldProgram
        (balancedRawCanonicalizeFoldBits inputLength tree)
        (balancedRawCanonicalizeFoldFuel inputLength tree)
        (initialNPOracleState inputLength tree.rawCode) =
      some (encodeBalancedList tree.atoms) := by
  let maximumBits := balancedRawCanonicalizeFoldBits inputLength tree
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, balancedRawCanonicalizeFoldBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, balancedRawCanonicalizeFoldBits]
  have hnormalize :
      balancedStructuralNormalizeBits inputLength tree ≤ maximumBits := by
    simp [maximumBits, balancedRawCanonicalizeFoldBits]
  have hcanonicalize :
      balancedCanonicalizeFoldBits inputLength tree.normalized ≤
        maximumBits := by
    simp [maximumBits, balancedRawCanonicalizeFoldBits]
  apply run_linkPrograms hpositive hlength
  · exact run_bits_mono
      (run_balancedStructuralNormalizeProgram inputLength tree hvalid)
      hnormalize
  · simpa [RawBalancedTraversalTree.atoms] using
      run_bits_mono
        (run_balancedCanonicalizeFoldProgram inputLength tree.normalized)
        hcanonicalize

/-- Total public normalization through the repaired canonicalizer. -/
theorem run_balancedRawCanonicalizeFoldProgram_total
    (inputLength raw : ℕ) :
    runNPOracleProgram balancedRawCanonicalizeFoldProgram
        (balancedRawCanonicalizeFoldBits inputLength
          (rawBalancedTraversalTree raw))
        (balancedRawCanonicalizeFoldFuel inputLength
          (rawBalancedTraversalTree raw))
        (initialNPOracleState inputLength raw) =
      some
        (encodeBalancedList (rawBalancedTraversalTree raw).atoms) := by
  have hrun :=
    run_balancedRawCanonicalizeFoldProgram inputLength
      (rawBalancedTraversalTree raw)
      (rawBalancedTraversalTree_valid raw)
  simpa [rawBalancedTraversalTree_rawCode] using hrun

/-! ## §4 The charge, in balanced measurements only -/

/-- **Every selecting callee is charged twice the counter's own charge.**  The
counter's charge already contains the traversal charge and the atom count, and
every requested index is below the atom count. -/
theorem atomIndexSelectBits_le
    (inputLength : ℕ) (tree : BalancedTraversalTree) :
    atomIndexSelectBits tree ≤
      2 * balancedAtomCountBits inputLength tree := by
  have hone : 1 ≤ balancedAtomCountBits inputLength tree := by
    simp [balancedAtomCountBits]
  have hlength :
      natBitLength tree.atoms.length ≤
        balancedAtomCountBits inputLength tree := by
    simp [balancedAtomCountBits]
  have htraversal :
      balancedTraversalRequiredBits (fun value => value) tree [] ≤
        balancedAtomCountBits inputLength tree := by
    simp [balancedAtomCountBits]
  simp only [atomIndexSelectBits]
  refine foldr_max_le (by omega) ?_
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨index, hindexMem, hindexEq⟩
  have hindex : index < tree.atoms.length := List.mem_range.mp hindexMem
  subst hindexEq
  refine balancedAtomSelectBits_le index tree
    (balancedAtomCountBits inputLength tree) hone ?_ hlength htraversal
  exact (natBitLength_mono' (by omega)).trans hlength

/-- **The repaired canonicalizer's charge, in balanced measurements.**  Four
summands, none of them a tagged list of the public atoms:

* the counting traversal's own charge, twice over — the second copy pays for
  every selecting callee;
* the generated request list's charge, which `CanonicalBalancedCall` closes by
  a fixed polynomial in the request count and the request widths;
* one balanced-call polynomial over the selecting requests;
* the width of a single request. -/
theorem balancedCanonicalizeFoldBits_le
    (inputLength : ℕ) (tree : BalancedTraversalTree) :
    balancedCanonicalizeFoldBits inputLength tree ≤
      max (2 * balancedAtomCountBits inputLength tree)
        (max
          (indexedAtomListBits inputLength tree.atoms.length tree.code
            (fun index => Nat.pair index tree.code))
          (max
            (balancedCallPolynomialBits (atomIndexOutput tree)
              (atomIndexRequests tree))
            (atomIndexRequestBits tree))) := by
  have hone : 1 ≤ balancedAtomCountBits inputLength tree := by
    simp [balancedAtomCountBits]
  have hinput :
      natBitLength inputLength ≤ balancedAtomCountBits inputLength tree := by
    simp [balancedAtomCountBits]
  have hselect := atomIndexSelectBits_le inputLength tree
  have hcall :=
    balancedCallRequiredBits_le_polynomial (atomIndexOutput tree)
      (atomIndexRequests tree)
  simp only [balancedCanonicalizeFoldBits, balancedCanonicalizeFoldStageBits,
    List.foldr_cons, List.foldr_nil]
  omega

/-- **The repaired raw canonicalizer's charge, in balanced measurements.** -/
theorem balancedRawCanonicalizeFoldBits_le
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) :
    balancedRawCanonicalizeFoldBits inputLength tree ≤
      max (balancedStructuralNormalizeBits inputLength tree)
        (max (2 * balancedAtomCountBits inputLength tree.normalized)
          (max
            (indexedAtomListBits inputLength tree.normalized.atoms.length
              tree.normalized.code
              (fun index => Nat.pair index tree.normalized.code))
            (max
              (balancedCallPolynomialBits (atomIndexOutput tree.normalized)
                (atomIndexRequests tree.normalized))
              (atomIndexRequestBits tree.normalized)))) := by
  have hstage := balancedCanonicalizeFoldBits_le inputLength tree.normalized
  have hone : 1 ≤ balancedStructuralNormalizeBits inputLength tree := by
    simp [balancedStructuralNormalizeBits]
  have hinput :
      natBitLength inputLength ≤
        balancedStructuralNormalizeBits inputLength tree := by
    simp [balancedStructuralNormalizeBits]
  simp only [balancedRawCanonicalizeFoldBits]
  omega

end NearCubicWires.CanonicalBalancedMidpointRebuildProgram
