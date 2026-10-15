import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorTraversalWidthLedger

namespace NearCubicWires.ValidatorTaggedIntermediateVerdict

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorTraversalWidthLedger

open private mappedSingletonStreams_valid from
  Proof.MachineModel.CanonicalBalancedValidationProgram

open private candidateWithRawBits from Proof.MachineModel.CanonicalNatValidationProgram

/-! ## §1 The machine's output-width floor -/

/-- **Every returned value fits the advertised width.**  `runNPOracleProgram`
returns `some` in exactly one place — the `.halt` branch — and that branch is
guarded by `natBitLength (state.registers outputRegister) ≤ maximumBits`.  So a
run theorem is simultaneously a width lower bound on its own charge. -/
theorem natBitLength_le_of_run
    {program : NPOracleProgram} {maximumBits fuel : ℕ}
    {state : NPOracleState} {value : ℕ}
    (hrun : runNPOracleProgram program maximumBits fuel state = some value) :
    natBitLength value ≤ maximumBits := by
  induction fuel generalizing state with
  | zero => simp only [runNPOracleProgram, reduceCtorEq] at hrun
  | succ fuel inductionHypothesis =>
      rw [runNPOracleProgram] at hrun
      repeat' split at hrun
      all_goals
        first
          | exact inductionHypothesis hrun
          | (simp only [Option.some.injEq] at hrun
             subst hrun
             assumption)
          | simp only [reduceCtorEq] at hrun

/-! ## §2 The decode chain, clock-free and fold-free -/

/-- **The tagged conversion's own output pins its charge.**  The first half of
the decoder returns `encodeTaggedList bits`, so its charge is at least that
value's width. -/
theorem natBitLength_encodeTaggedList_le_balancedBitsToTaggedBits
    (inputLength : ℕ) (bits : List ℕ) :
    natBitLength (encodeTaggedList bits) ≤
      balancedBitsToTaggedBits inputLength bits :=
  natBitLength_le_of_run (run_balancedBitsToTaggedProgram inputLength bits)

/-- **The decode chain's first half is geometric.** -/
theorem two_pow_length_le_balancedBitsToTaggedBits
    (inputLength : ℕ) (bits : List ℕ) :
    2 ^ bits.length ≤ balancedBitsToTaggedBits inputLength bits :=
  (two_pow_length_le_natBitLength_encodeTaggedList bits).trans
    (natBitLength_encodeTaggedList_le_balancedBitsToTaggedBits inputLength bits)

/-- **The width the conversion reads.**  Its input is the canonical balanced
code of the same bits, and that code is quadratic in the bit count.  Read
beside the previous theorem: the stage takes a quadratic-width input to a
geometric-width output.  The defect is the conversion, not the charge. -/
theorem natBitLength_encodeBalancedList_bits_le
    (bits : List ℕ) (hbits : ∀ bit ∈ bits, natBitLength bit ≤ 1) :
    natBitLength (encodeBalancedList bits) ≤ 16 * (bits.length + 1) ^ 2 := by
  have hbound :=
    natBitLength_encodeBalancedList_le_quadratic bits 1 (by omega) hbits
  simpa using hbound

/-- **The first residual width, from below — without the fold.**
`ValidatorTraversalWidthLedger` §2 obtains this bound by unfolding
`taggedBitFoldBits`.  The same bound holds through the *other* summand, at a
value the machine actually returns, so retuning `taggedBitFoldBits` cannot
move it. -/
theorem two_pow_length_le_canonicalNatDecodeListBits_of_run
    (inputLength : ℕ) (bits : List ℕ) :
    2 ^ bits.length ≤ canonicalNatDecodeListBits inputLength bits := by
  have hconvert := two_pow_length_le_balancedBitsToTaggedBits inputLength bits
  obtain ⟨power, hpower⟩ : ∃ power : ℕ, (2 : ℕ) ^ bits.length = power := ⟨_, rfl⟩
  rw [hpower] at hconvert ⊢
  simp only [canonicalNatDecodeListBits]
  omega

/-! ## §3 The flattener and the canonicalizer, clock-free -/

/-- **The flattener's own output pins its charge.** -/
theorem two_pow_le_balancedClauseStreamFlattenMaximumBits
    (streams : List (List ℕ)) :
    2 ^ streams.flatten.length ≤
      balancedClauseStreamFlattenMaximumBits streams :=
  (two_pow_length_le_natBitLength_encodeTaggedList streams.flatten).trans
    (natBitLength_le_of_run
      (run_balancedClauseStreamFlattenProgram streams 0))

/-- **The structural entry point's own output pins its charge.**  This is the
summand `balancedCanonicalizeBits` actually carries. -/
theorem two_pow_le_balancedTreeStreamFlattenMaximumBits
    (tree : BalancedTraversalTree)
    (hvalid : ∀ atom ∈ tree.atoms,
      encodeTaggedList (streamOfCode atom) = atom) :
    2 ^ (treeStreamValues tree).length ≤
      balancedTreeStreamFlattenMaximumBits tree :=
  (two_pow_length_le_natBitLength_encodeTaggedList
      (treeStreamValues tree)).trans
    (natBitLength_le_of_run
      (run_balancedClauseStreamFlattenTree tree 0 hvalid))

/-- **The canonicalizer's width, from below — without the builder's clock.**
The midpoint canonicalizer flattens the mapped tree to one tagged stream before
rebuilding, and that stream is returned by the middle stage.  So the charge is
geometric in the atom count through a summand the `pairIter` clock never
touches. -/
theorem two_pow_atoms_le_balancedCanonicalizeBits
    (inputLength : ℕ) (tree : BalancedTraversalTree) :
    2 ^ tree.atoms.length ≤ balancedCanonicalizeBits inputLength tree := by
  have hflatten :=
    two_pow_le_balancedTreeStreamFlattenMaximumBits
      (tree.map singletonTaggedBit) (mappedSingletonStreams_valid tree)
  rw [treeStreamValues_map_singleton] at hflatten
  obtain ⟨power, hpower⟩ :
      ∃ power : ℕ, (2 : ℕ) ^ tree.atoms.length = power := ⟨_, rfl⟩
  rw [hpower] at hflatten ⊢
  simp only [balancedCanonicalizeBits]
  omega

/-- **The second residual width, from below — without the clock.**
`ValidatorTraversalWidthLedger` §3 obtains a bound on this charge by unfolding
the builder's `pairIter` clock.  The same shape of bound holds through the
flattening summand, at a value the machine actually returns. -/
theorem two_pow_atoms_le_balancedRawCanonicalizeBits
    (inputLength : ℕ) (tree : RawBalancedTraversalTree) :
    2 ^ tree.atoms.length ≤ balancedRawCanonicalizeBits inputLength tree := by
  have hcanonicalize :=
    two_pow_atoms_le_balancedCanonicalizeBits inputLength tree.normalized
  obtain ⟨power, hpower⟩ :
      ∃ power : ℕ, (2 : ℕ) ^ tree.normalized.atoms.length = power := ⟨_, rfl⟩
  rw [hpower] at hcanonicalize
  simp only [RawBalancedTraversalTree.atoms, hpower]
  simp only [balancedRawCanonicalizeBits]
  omega

/-! ## §4 The builder's honest floor, under the clock

`taggedToBalancedRegisterBitsFor` is `natBitLength` of a `pairIter` clock at
the builder's own fuel: a bound that squares once per executed instruction,
over a base that already contains the input.  That clock is a genuine
over-charge — the builder's writes are the counting scratch, a continuation
stack of midpoint height, the canonical subtree codes and the output, none of
which is a tower of that depth.  What is *not* an over-charge is the base: the
program's input register holds the tagged stream, so the charge contains the
tagged codec's own width, and re-deriving the stage honestly cannot go below
it. -/

/-- The tagged input sits inside the builder's charge. -/
theorem natBitLength_encodeTaggedList_le_taggedToBalancedRegisterBitsFor
    (inputLength : ℕ) (values : List ℕ) :
    natBitLength (encodeTaggedList values) ≤
      taggedToBalancedRegisterBitsFor inputLength values := by
  have hbase :
      encodeTaggedList values ≤
        taggedToBalancedInitialBoundFor inputLength values := by
    simp only [taggedToBalancedInitialBoundFor]
    omega
  have hclock :
      taggedToBalancedInitialBoundFor inputLength values ≤
        pairIter (taggedToBalancedFuel values)
          (taggedToBalancedInitialBoundFor inputLength values) :=
    value_le_pairIter _ _
  simp only [taggedToBalancedRegisterBitsFor]
  exact ValidatorLeafWidthCore.natBitLength_mono (hbase.trans hclock)

/-- **The builder's honest floor.**  Even charged only at what its input
register demonstrably holds, the stage is geometric in the atom count. -/
theorem two_pow_length_le_taggedToBalancedRegisterBitsFor
    (inputLength : ℕ) (values : List ℕ) :
    2 ^ values.length ≤ taggedToBalancedRegisterBitsFor inputLength values :=
  (two_pow_length_le_natBitLength_encodeTaggedList values).trans
    (natBitLength_encodeTaggedList_le_taggedToBalancedRegisterBitsFor
      inputLength values)

/-! ## §5 The verdict

§2 and §3 restate `ValidatorTraversalWidthLedger`'s two starting lower bounds
without touching either of the two definitions a repair would retune — the
tagged bit fold's working set and the builder's `pairIter` clock.  Both new
proofs go through §1, so both are statements about the *programs*: the
canonical natural validator's charge is geometric because the fixed programs it
links return `encodeTaggedList` of a public-length list.

The consequence is that `ValidatorTraversalWidthLedger.not_polyBounded_…` is
not repairable by re-charging.  §5 below re-derives its hypothesis chain from
§2 alone. -/

/-- The candidate pass's charge, from the returned tagged stream. -/
theorem two_pow_atoms_le_canonicalNatCandidateBits_of_run
    (inputLength raw : ℕ) :
    2 ^ (rawBalancedTraversalTree raw).atoms.length ≤
      canonicalNatCandidateBits inputLength raw := by
  have hdecode :=
    two_pow_length_le_canonicalNatDecodeListBits_of_run inputLength
      (rawBalancedTraversalTree raw).atoms
  obtain ⟨power, hpower⟩ :
      ∃ value : ℕ,
        (2 : ℕ) ^ (rawBalancedTraversalTree raw).atoms.length = value :=
    ⟨_, rfl⟩
  rw [hpower] at hdecode ⊢
  simp only [canonicalNatCandidateBits]
  omega

/-- **The verdict.**  The canonical natural validator's charge on the canonical
atom family is geometric because the linked programs return a tagged list of
that many public atoms.  Retuning `taggedBitFoldBits`,
`balancedClauseStreamFlattenMaximumBits` or `taggedToBalancedRegisterBitsFor`
cannot lower it: the bound below never unfolds any of the three. -/
theorem two_pow_le_canonicalNatValidationBits_canonicalAtomFamily_of_run
    (inputLength n : ℕ) :
    2 ^ n ≤ canonicalNatValidationBits inputLength (canonicalAtomFamily n) := by
  have hcandidate :=
    two_pow_atoms_le_canonicalNatCandidateBits_of_run inputLength
      (canonicalAtomFamily n)
  rw [atoms_canonicalAtomFamily, List.length_replicate] at hcandidate
  have hwrapper :=
    le_preserveRightBits
      (canonicalNatCandidateBits inputLength (canonicalAtomFamily n))
      (canonicalAtomFamily n) (canonicalAtomFamily n)
      (canonicalNatCandidate (canonicalAtomFamily n))
  obtain ⟨power, hpower⟩ : ∃ value : ℕ, (2 : ℕ) ^ n = value := ⟨_, rfl⟩
  rw [hpower] at hcandidate ⊢
  simp only [canonicalNatValidationBits, candidateWithRawBits]
  omega

end NearCubicWires.ValidatorTaggedIntermediateVerdict
