import Proof.MachineModel.StructuralAtomEmitterLoopProgram

/-!
# The structural atom emitter at the balanced codec

`StructuralAtomEmitterLoopProgram.structuralAtomEmitterProgram` is the
generated index loop under a point-preserving wrapper, followed by the
balanced-to-tagged converter under a second one.  The loop itself already
returns the canonical BALANCED atom list
(`run_structuralAtomRangeProgram`); the tagged codec — whose width head
`encodeTaggedList` is geometric in the atom count
(`ValidatorTraversalWidthLedger.two_pow_length_le_natBitLength_encodeTaggedList`)
and whose containments at the emitter charge are the Lean-checked kill sites
of `TightInverseSelectorAdapterTaggedCodecFloor` — enters ONLY through that
second stage.

This twin drops the second stage: one point-preserving wrapper around the
landed index loop, returning `pair (encodeBalancedList atoms) pointCode`.
Its width charge holds the balanced payload, whose bit length is polynomial
in the atom count and the atom widths (`balancedListCodeBits_le` — the
midpoint-balanced antidote), beside the request frame; no tagged codec, no
balanced-to-tagged builder clock, no `Encodable` list code appears on either
axis.  The frozen emitter is untouched and remains the tagged-consumer
route's producer; this is the emitter half of the balanced-codec migration,
and the balanced recovery-query selector consumes exactly this output shape.
-/

namespace NearCubicWires.BalancedStructuralAtomEmitterProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedFlattenProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The emitter: the loop's balanced list beside the point code -/

/-- **The balanced structural atom emitter.**  One fixed instruction stream
carrying no index and no schedule immediate: the generated index loop under a
single point-preserving wrapper.  The balanced-to-tagged converter of the
frozen emitter is gone. -/
def balancedStructuralAtomEmitterProgram (callee : NPOracleProgram) :
    NPOracleProgram :=
  preserveRightProgram (structuralAtomRangeProgram callee)

theorem balancedStructuralAtomEmitterProgram_oracleFree
    {callee : NPOracleProgram} (hcallee : OracleFree callee) :
    OracleFree (balancedStructuralAtomEmitterProgram callee) :=
  preserveRightProgram_oracleFree _
    (structuralAtomRangeProgram_oracleFree hcallee)

def balancedStructuralAtomEmitterFuel (callee : NPOracleProgram)
    (inputLength count context : ℕ) (calleeFuel : ℕ → ℕ) : ℕ :=
  preserveRightFuel
    (structuralAtomRangeFuel callee inputLength count context calleeFuel)

def balancedStructuralAtomEmitterBits
    (rangeBits count context pointCode : ℕ) (atoms : List ℕ) : ℕ :=
  preserveRightBits rangeBits
    (generatedBalancedRangeInput count context) pointCode
    (encodeBalancedList atoms)

/-- **The balanced emitter, executed.**  From the loop's input frame the
stream returns exactly the balanced atom list beside the retained point
code. -/
theorem run_balancedStructuralAtomEmitterProgram
    (callee : NPOracleProgram) {rangeBits : ℕ}
    (inputLength count context pointCode : ℕ) (calleeFuel output : ℕ → ℕ)
    (hpositive : 1 ≤ rangeBits)
    (hlengthBits : natBitLength inputLength ≤ rangeBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits inputLength count context ≤ rangeBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms inputLength context 0 count)) ≤
        rangeBits)
    (hcallBits :
      balancedCallRequiredBits output
          (balancedRangeRequestAtoms inputLength context 0 count) ≤
        rangeBits)
    (hcallee : ∀ request,
      request ∈ balancedRangeRequestAtoms inputLength context 0 count →
      runNPOracleProgram callee rangeBits (calleeFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) =
        some (output request)) :
    runNPOracleProgram (balancedStructuralAtomEmitterProgram callee)
        (balancedStructuralAtomEmitterBits rangeBits count context pointCode
          ((balancedRangeRequestAtoms inputLength context 0 count).map output))
        (balancedStructuralAtomEmitterFuel callee inputLength count context
          calleeFuel)
        (initialNPOracleState inputLength
          (Nat.pair (generatedBalancedRangeInput count context) pointCode)) =
      some
        (Nat.pair
          (encodeBalancedList
            ((balancedRangeRequestAtoms inputLength context 0 count).map
              output))
          pointCode) :=
  run_preserveRightProgram (structuralAtomRangeProgram callee) inputLength
    rangeBits
    (structuralAtomRangeFuel callee inputLength count context calleeFuel)
    (generatedBalancedRangeInput count context) pointCode
    (encodeBalancedList
      ((balancedRangeRequestAtoms inputLength context 0 count).map output))
    (run_structuralAtomRangeProgram callee inputLength count context
      calleeFuel output hpositive hlengthBits hrangeBits hlistBits hcallBits
      hcallee)

/-! ## 2. The balanced emitter at an executable projection PCP -/

/-- **The balanced structural atom emitter at an executable projection
PCP.**  Modulo one run of one pointwise callee per global formula index, the
fixed stream returns exactly the BALANCED canonical atom schedule beside the
retained point code. -/
theorem run_balancedStructuralAtomEmitterProgram_table
    (callee : NPOracleProgram) {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound pointCode : ℕ) (calleeFuel : ℕ → ℕ)
    (hpositive : 1 ≤ rangeBits)
    (hlengthBits : natBitLength n ≤ rangeBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits n (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) ≤
        rangeBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms n
              (structuralAtomContext pcp input bound) 0
              (structuralAtomCount pcp input bound))) ≤
        rangeBits)
    (hcallBits :
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp input bound
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms n (structuralAtomContext pcp input bound) 0
            (structuralAtomCount pcp input bound)) ≤
        rangeBits)
    (hcallee : ∀ index, index < structuralAtomCount pcp input bound →
      runNPOracleProgram callee rangeBits
          (calleeFuel
            (balancedRangeRequestAtom n index
              (structuralAtomContext pcp input bound)))
          (initialNPOracleState n
            (Nat.pair index (structuralAtomContext pcp input bound))) =
        some (structuralAtomValue pcp input bound index)) :
    runNPOracleProgram (balancedStructuralAtomEmitterProgram callee)
        (balancedStructuralAtomEmitterBits rangeBits
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) pointCode
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (balancedStructuralAtomEmitterFuel callee n
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) calleeFuel)
        (initialNPOracleState n
          (Nat.pair
            (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
              (structuralAtomContext pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodeBalancedList
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
          pointCode) := by
  have hmap := structuralAtomRequests_map pcp input bound
  rw [← hmap]
  refine run_balancedStructuralAtomEmitterProgram callee n
    (structuralAtomCount pcp input bound)
    (structuralAtomContext pcp input bound) pointCode calleeFuel
    (fun request =>
      structuralAtomValue pcp input bound (structuralAtomRequestIndex request))
    hpositive hlengthBits hrangeBits hlistBits hcallBits ?_
  intro request hrequest
  rw [balancedRangeRequestAtoms_eq_map_range, List.mem_map] at hrequest
  obtain ⟨index, hindex, hrequestEq⟩ := hrequest
  rw [Nat.zero_add] at hrequestEq
  subst hrequestEq
  rw [structuralAtomRequestIndex_atom]
  have hleft :
      (Nat.unpair
        (balancedRangeRequestAtom n index
          (structuralAtomContext pcp input bound))).1 = n := by
    simp [balancedRangeRequestAtom]
  have hright :
      (Nat.unpair
        (balancedRangeRequestAtom n index
          (structuralAtomContext pcp input bound))).2 =
        Nat.pair index (structuralAtomContext pcp input bound) := by
    simp [balancedRangeRequestAtom]
  rw [hleft, hright]
  exact hcallee index (List.mem_range.mp hindex)

/-! ## 3. Width ledgers — the balanced payload is the whole charge -/

/-- The output frame word is polynomial in the atom count and the atom
widths: the `balancedListCodeBits_le` antidote, paired with the retained
point code. -/
theorem natBitLength_pair_encodeBalancedList_le
    (atoms : List ℕ) (pointCode : ℕ) :
    natBitLength (Nat.pair (encodeBalancedList atoms) pointCode) ≤
      2 * max (1 + 2 * atoms.length ^ 4 * balancedListAtomBits atoms)
        (natBitLength pointCode) :=
  (pairCodeBits_le (encodeBalancedList atoms) pointCode).trans
    (Nat.mul_le_mul_left 2
      (max_le_max (balancedListCodeBits_le atoms) (Nat.le_refl _)))

/-- Closed-form collapse of the emitter charge: three input bounds, one
budget.  There is no fourth head — the tagged conversion stage does not
exist in this stream. -/
theorem balancedStructuralAtomEmitterBits_le
    {rangeBits count context pointCode budget : ℕ} {atoms : List ℕ}
    (hrange : rangeBits ≤ budget)
    (hframe :
      natBitLength
          (Nat.pair (generatedBalancedRangeInput count context) pointCode) ≤
        budget)
    (hpayload :
      natBitLength (Nat.pair (encodeBalancedList atoms) pointCode) ≤ budget) :
    balancedStructuralAtomEmitterBits rangeBits count context pointCode
        atoms ≤ budget :=
  max_le hrange (max_le hframe hpayload)

/-- The emitter charge against its own polynomial budget: the range stage,
the request frame, and the balanced payload bound of
`balancedListCodeBits_le`. -/
theorem balancedStructuralAtomEmitterBits_le_poly
    (rangeBits count context pointCode : ℕ) (atoms : List ℕ) :
    balancedStructuralAtomEmitterBits rangeBits count context pointCode
        atoms ≤
      max rangeBits
        (max
          (natBitLength
            (Nat.pair (generatedBalancedRangeInput count context) pointCode))
          (2 * max (1 + 2 * atoms.length ^ 4 * balancedListAtomBits atoms)
            (natBitLength pointCode))) :=
  balancedStructuralAtomEmitterBits_le
    (Nat.le_max_left _ _)
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
    ((natBitLength_pair_encodeBalancedList_le atoms pointCode).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))

end NearCubicWires.BalancedStructuralAtomEmitterProgram
