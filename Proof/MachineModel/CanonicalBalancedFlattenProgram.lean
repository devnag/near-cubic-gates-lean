import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.Circuits.CanonicalBalancedBuilder
import Proof.Circuits.CanonicalBalancedCall

/-!
# Concatenating canonical balanced sequences

`CanonicalBalanced` is the sole public variable-length ABI, and its midpoint
split makes concatenation genuinely structural: the code of `xs ++ ys` shares
no subtree with the codes of `xs` and `ys`.  Every polynomial compiler below
the structural `𝔽₂` row needs that operation — a monomial of a product is the
concatenation of one monomial per factor — so this module supplies it once.

Nothing new is looped.  The private forward tagged stream of
`CanonicalBalancedBuilder` is already the repository's sole conversion
boundary, and `BalancedClauseStreamFlattenProgram` already folds a balanced
tree of tagged streams into one stream.  What is missing is only the *other*
direction of the boundary, and it is a balanced call away: mapping each atom to
its own singleton stream turns the existing fold into a balanced-to-tagged
converter, after which flattening and rebuilding are the two programs that
already exist.

The three exported programs are therefore

* `balancedToTaggedProgram`: `encodeBalancedList` to `encodeTaggedList`;
* `balancedFlattenProgram`: a balanced list of balanced lists to the balanced
  code of their concatenation;
* `balancedAppendProgram`: the two-element special case, on the pair ABI.

All three are fixed, oracle-free, and carry closed fuel and register-width
formulas.
-/

namespace NearCubicWires.CanonicalBalancedFlattenProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

private theorem stageBits_le_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-- The singleton tagged stream of the request code. -/
def taggedSingletonProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .pair 0 2 0 2
  , .set 2 1 3
  , .pair 2 0 0 4
  , .halt 0
  ]

@[simp] theorem taggedSingletonProgram_oracleFree :
    OracleFree taggedSingletonProgram := by
  rfl

def taggedSingletonFuel : ℕ := 5

theorem run_taggedSingletonProgram
    (inputLength value maximumBits : ℕ) (hpositive : 1 ≤ maximumBits)
    (hbits : natBitLength (encodeTaggedList [value]) ≤ maximumBits) :
    runNPOracleProgram taggedSingletonProgram maximumBits taggedSingletonFuel
        (initialNPOracleState inputLength value) =
      some (encodeTaggedList [value]) := by
  have hcode : encodeTaggedList [value] = Nat.pair 1 (Nat.pair value 0) := by
    simp [encodeTaggedList]
  have hinner : natBitLength (Nat.pair value 0) ≤ maximumBits := by
    refine le_trans (natBitLength_mono ?_) hbits
    rw [hcode]
    exact Nat.right_le_pair 1 (Nat.pair value 0)
  have hone : natBitLength 1 ≤ maximumBits := by
    refine le_trans (natBitLength_mono ?_) hbits
    rw [hcode]
    exact Nat.left_le_pair 1 (Nat.pair value 0)
  have hzero : natBitLength 0 ≤ maximumBits := by
    simpa [natBitLength] using hpositive
  rw [show taggedSingletonFuel = 4 + 1 by rfl]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair value 0) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hinner]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := encodeTaggedList [value]) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hcode])
    hbits]
  exact run_halt_instruction (fuel := 0) (value := encodeTaggedList [value])
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hbits

/-! ## §2 The balanced code read as a tagged stream

Mapping §1 over the balanced list and folding the resulting singletons is
exactly the identity on the atom sequence, so the composite is the converse of
`CanonicalBalancedBuilder`. -/

/-- **The balanced-to-tagged converter.** -/
def balancedToTaggedProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms nativeInputRequestTreeProgram
      (balancedCallProgram taggedSingletonProgram))
    balancedClauseStreamFlattenProgram

theorem balancedToTaggedProgram_oracleFree :
    OracleFree balancedToTaggedProgram :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms nativeInputRequestTreeProgram_oracleFree
      (balancedCallProgram_oracleFree taggedSingletonProgram_oracleFree))
    balancedClauseStreamFlattenProgram_oracleFree

/-- The singleton streams the converter folds. -/
def taggedSingletonStreams (values : List ℕ) : List (List ℕ) :=
  values.map fun value => [value]

@[simp] theorem taggedSingletonStreams_flatten (values : List ℕ) :
    (taggedSingletonStreams values).flatten = values := by
  unfold taggedSingletonStreams
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp [inductionHypothesis]

theorem taggedSingletonStreams_map (values : List ℕ) :
    (taggedSingletonStreams values).map encodeTaggedList =
      values.map fun value => encodeTaggedList [value] := by
  unfold taggedSingletonStreams
  rw [List.map_map]
  rfl

/-- The balanced-call output of §1 as a function of the request code. -/
def taggedSingletonOutput (request : ℕ) : ℕ :=
  encodeTaggedList [(Nat.unpair request).2]

theorem taggedSingletonOutput_requests (inputLength : ℕ) (values : List ℕ) :
    (values.map (nativeInputRequest inputLength)).map taggedSingletonOutput =
      values.map fun value => encodeTaggedList [value] := by
  rw [List.map_map]
  apply List.map_congr_left
  intro value _hvalue
  simp [taggedSingletonOutput, nativeInputRequest]

def balancedToTaggedRequestFuel (inputLength : ℕ) (values : List ℕ) : ℕ :=
  linkFuel (balancedCallProgram taggedSingletonProgram)
    (nativeInputRequestTreeFuel values)
    (balancedCallFuel taggedSingletonProgram (fun _ => taggedSingletonFuel)
      (values.map (nativeInputRequest inputLength)))

def balancedToTaggedFuel (inputLength : ℕ) (values : List ℕ) : ℕ :=
  linkFuel balancedClauseStreamFlattenProgram
    (balancedToTaggedRequestFuel inputLength values)
    (balancedClauseStreamFlattenFuel (taggedSingletonStreams values))

def balancedToTaggedStageBits (inputLength : ℕ) (values : List ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , nativeInputRequestTreeBits inputLength values
  , balancedCallRequiredBits taggedSingletonOutput
      (values.map (nativeInputRequest inputLength))
  , balancedClauseStreamFlattenMaximumBits (taggedSingletonStreams values)
  ]

def balancedToTaggedBits (inputLength : ℕ) (values : List ℕ) : ℕ :=
  (balancedToTaggedStageBits inputLength values).foldr max 1

/-- **The balanced code of a list, read back as its tagged stream.** -/
theorem run_balancedToTaggedProgram
    (inputLength maximumBits : ℕ) (values : List ℕ)
    (hbits : balancedToTaggedBits inputLength values ≤ maximumBits) :
    runNPOracleProgram balancedToTaggedProgram maximumBits
        (balancedToTaggedFuel inputLength values)
        (initialNPOracleState inputLength (encodeBalancedList values)) =
      some (encodeTaggedList values) := by
  have bits_of_member {entry : ℕ}
      (hentry : entry ∈ balancedToTaggedStageBits inputLength values) :
      entry ≤ maximumBits :=
    le_trans (stageBits_le_of_mem hentry) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [balancedToTaggedStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [balancedToTaggedStageBits]
  have htree :
      runNPOracleProgram nativeInputRequestTreeProgram maximumBits
          (nativeInputRequestTreeFuel values)
          (initialNPOracleState inputLength (encodeBalancedList values)) =
        some
          (encodeBalancedList
            (values.map (nativeInputRequest inputLength))) :=
    run_bits_mono (run_nativeInputRequestTreeProgram inputLength values)
      (by
        apply bits_of_member
        simp [balancedToTaggedStageBits])
  have hcallBits :
      balancedCallRequiredBits taggedSingletonOutput
          (values.map (nativeInputRequest inputLength)) ≤
        maximumBits := by
    apply bits_of_member
    simp [balancedToTaggedStageBits]
  have hcall :
      runNPOracleProgram (balancedCallProgram taggedSingletonProgram)
          maximumBits
          (balancedCallFuel taggedSingletonProgram
            (fun _ => taggedSingletonFuel)
            (values.map (nativeInputRequest inputLength)))
          (initialNPOracleState inputLength
            (encodeBalancedList
              (values.map (nativeInputRequest inputLength)))) =
        some
          (encodeBalancedList
            ((taggedSingletonStreams values).map encodeTaggedList)) := by
    rw [taggedSingletonStreams_map,
      ← taggedSingletonOutput_requests inputLength values]
    refine run_balancedCallProgram_from inputLength
      (values.map (nativeInputRequest inputLength))
      (fun _ => taggedSingletonFuel) taggedSingletonOutput hcallBits ?_
    intro request hrequest
    refine run_taggedSingletonProgram (Nat.unpair request).1
      (Nat.unpair request).2 maximumBits hpositive ?_
    refine le_trans (natBitLength_mono ?_)
      (le_trans (balancedCallRequiredBits_pair taggedSingletonOutput hrequest)
        hcallBits)
    exact Nat.right_le_pair request (taggedSingletonOutput request)
  have hflatten :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          (balancedClauseStreamFlattenFuel (taggedSingletonStreams values))
          (initialNPOracleState inputLength
            (encodeBalancedList
              ((taggedSingletonStreams values).map encodeTaggedList))) =
        some (encodeTaggedList values) := by
    have hrun :=
      run_balancedClauseStreamFlattenProgram (taggedSingletonStreams values)
        inputLength
    rw [taggedSingletonStreams_flatten] at hrun
    exact run_bits_mono hrun
      (by
        apply bits_of_member
        simp [balancedToTaggedStageBits])
  exact run_linkPrograms hpositive hlength
    (run_linkPrograms hpositive hlength htree hcall) hflatten

/-! ## §3 The concatenation of a balanced list of balanced lists

With §2 in hand the concatenation is the composite the repository already
owns: read every inner code as a tagged stream, fold the streams, and rebuild
the canonical balanced code once. -/

/-- **The balanced concatenation program.** -/
def balancedFlattenProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms nativeInputRequestTreeProgram
      (balancedCallProgram balancedToTaggedProgram))
    (linkPrograms balancedClauseStreamFlattenProgram taggedToBalancedProgram)

theorem balancedFlattenProgram_oracleFree :
    OracleFree balancedFlattenProgram :=
  oracleFree_linkPrograms
    (oracleFree_linkPrograms nativeInputRequestTreeProgram_oracleFree
      (balancedCallProgram_oracleFree balancedToTaggedProgram_oracleFree))
    (oracleFree_linkPrograms balancedClauseStreamFlattenProgram_oracleFree
      taggedToBalancedProgram_oracleFree)

/-- The inner list named by one balanced-call request. -/
def balancedFlattenCalleeList (request : ℕ) : List ℕ :=
  (decodeBalancedList (Nat.unpair request).2).getD []

@[simp] theorem balancedFlattenCalleeList_request
    (inputLength : ℕ) (values : List ℕ) :
    balancedFlattenCalleeList
        (nativeInputRequest inputLength (encodeBalancedList values)) =
      values := by
  simp [balancedFlattenCalleeList, nativeInputRequest]

def balancedFlattenCalleeFuel (request : ℕ) : ℕ :=
  balancedToTaggedFuel (Nat.unpair request).1
    (balancedFlattenCalleeList request)

def balancedFlattenOutput (request : ℕ) : ℕ :=
  encodeTaggedList (balancedFlattenCalleeList request)

private theorem balancedFlattenRequests
    (inputLength : ℕ) (streams : List (List ℕ)) :
    ((streams.map encodeBalancedList).map
        (nativeInputRequest inputLength)).map balancedFlattenOutput =
      streams.map encodeTaggedList := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro values _hvalues
  simp [balancedFlattenOutput]

def balancedFlattenRequestFuel
    (inputLength : ℕ) (streams : List (List ℕ)) : ℕ :=
  linkFuel (balancedCallProgram balancedToTaggedProgram)
    (nativeInputRequestTreeFuel (streams.map encodeBalancedList))
    (balancedCallFuel balancedToTaggedProgram balancedFlattenCalleeFuel
      ((streams.map encodeBalancedList).map (nativeInputRequest inputLength)))

def balancedFlattenOutputFuel (streams : List (List ℕ)) : ℕ :=
  linkFuel taggedToBalancedProgram
    (balancedClauseStreamFlattenFuel streams)
    (taggedToBalancedFuel streams.flatten)

def balancedFlattenFuel (inputLength : ℕ) (streams : List (List ℕ)) : ℕ :=
  linkFuel (linkPrograms balancedClauseStreamFlattenProgram
      taggedToBalancedProgram)
    (balancedFlattenRequestFuel inputLength streams)
    (balancedFlattenOutputFuel streams)

/-- Register width the inner converter needs on every atom of the outer
list. -/
def balancedFlattenCalleeBits
    (inputLength : ℕ) (streams : List (List ℕ)) : ℕ :=
  (streams.map fun values => balancedToTaggedBits inputLength values).foldr
    max 1

private theorem balancedFlattenCalleeBits_member
    {inputLength : ℕ} {streams : List (List ℕ)} {values : List ℕ}
    (hvalues : values ∈ streams) :
    balancedToTaggedBits inputLength values ≤
      balancedFlattenCalleeBits inputLength streams :=
  stageBits_le_of_mem (List.mem_map.mpr ⟨values, hvalues, rfl⟩)

def balancedFlattenStageBits
    (inputLength : ℕ) (streams : List (List ℕ)) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , nativeInputRequestTreeBits inputLength (streams.map encodeBalancedList)
  , balancedCallRequiredBits balancedFlattenOutput
      ((streams.map encodeBalancedList).map (nativeInputRequest inputLength))
  , balancedFlattenCalleeBits inputLength streams
  , balancedClauseStreamFlattenMaximumBits streams
  , taggedToBalancedRegisterBitsFor inputLength streams.flatten
  ]

def balancedFlattenBits (inputLength : ℕ) (streams : List (List ℕ)) : ℕ :=
  (balancedFlattenStageBits inputLength streams).foldr max 1

/-- **The balanced code of a concatenation, executed.** -/
theorem run_balancedFlattenProgram
    (inputLength maximumBits : ℕ) (streams : List (List ℕ))
    (hbits : balancedFlattenBits inputLength streams ≤ maximumBits) :
    runNPOracleProgram balancedFlattenProgram maximumBits
        (balancedFlattenFuel inputLength streams)
        (initialNPOracleState inputLength
          (encodeBalancedList (streams.map encodeBalancedList))) =
      some (encodeBalancedList streams.flatten) := by
  have bits_of_member {entry : ℕ}
      (hentry : entry ∈ balancedFlattenStageBits inputLength streams) :
      entry ≤ maximumBits :=
    le_trans (stageBits_le_of_mem hentry) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [balancedFlattenStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [balancedFlattenStageBits]
  have htree :
      runNPOracleProgram nativeInputRequestTreeProgram maximumBits
          (nativeInputRequestTreeFuel (streams.map encodeBalancedList))
          (initialNPOracleState inputLength
            (encodeBalancedList (streams.map encodeBalancedList))) =
        some
          (encodeBalancedList
            ((streams.map encodeBalancedList).map
              (nativeInputRequest inputLength))) :=
    run_bits_mono
      (run_nativeInputRequestTreeProgram inputLength
        (streams.map encodeBalancedList))
      (by
        apply bits_of_member
        simp [balancedFlattenStageBits])
  have hcallBits :
      balancedCallRequiredBits balancedFlattenOutput
          ((streams.map encodeBalancedList).map
            (nativeInputRequest inputLength)) ≤
        maximumBits := by
    apply bits_of_member
    simp [balancedFlattenStageBits]
  have hcalleeBits :
      balancedFlattenCalleeBits inputLength streams ≤ maximumBits := by
    apply bits_of_member
    simp [balancedFlattenStageBits]
  have hcall :
      runNPOracleProgram (balancedCallProgram balancedToTaggedProgram)
          maximumBits
          (balancedCallFuel balancedToTaggedProgram balancedFlattenCalleeFuel
            ((streams.map encodeBalancedList).map
              (nativeInputRequest inputLength)))
          (initialNPOracleState inputLength
            (encodeBalancedList
              ((streams.map encodeBalancedList).map
                (nativeInputRequest inputLength)))) =
        some (encodeBalancedList (streams.map encodeTaggedList)) := by
    rw [← balancedFlattenRequests inputLength streams]
    refine run_balancedCallProgram_from inputLength
      ((streams.map encodeBalancedList).map (nativeInputRequest inputLength))
      balancedFlattenCalleeFuel balancedFlattenOutput hcallBits ?_
    intro request hrequest
    rcases List.mem_map.mp hrequest with ⟨code, hcode, rfl⟩
    rcases List.mem_map.mp hcode with ⟨values, hvalues, rfl⟩
    have hleft :
        (Nat.unpair
          (nativeInputRequest inputLength (encodeBalancedList values))).1 =
          inputLength := by
      simp [nativeInputRequest]
    have hright :
        (Nat.unpair
          (nativeInputRequest inputLength (encodeBalancedList values))).2 =
          encodeBalancedList values := by
      simp [nativeInputRequest]
    rw [hleft, hright]
    unfold balancedFlattenCalleeFuel balancedFlattenOutput
    rw [hleft, balancedFlattenCalleeList_request]
    exact run_balancedToTaggedProgram inputLength maximumBits values
      (le_trans (balancedFlattenCalleeBits_member hvalues) hcalleeBits)
  have hflatten :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          (balancedClauseStreamFlattenFuel streams)
          (initialNPOracleState inputLength
            (encodeBalancedList (streams.map encodeTaggedList))) =
        some (encodeTaggedList streams.flatten) :=
    run_bits_mono
      (run_balancedClauseStreamFlattenProgram streams inputLength)
      (by
        apply bits_of_member
        simp [balancedFlattenStageBits])
  have hbuild :
      runNPOracleProgram taggedToBalancedProgram maximumBits
          (taggedToBalancedFuel streams.flatten)
          (initialNPOracleState inputLength
            (encodeTaggedList streams.flatten)) =
        some (encodeBalancedList streams.flatten) :=
    run_bits_mono
      (run_taggedToBalancedProgram_from inputLength streams.flatten)
      (by
        apply bits_of_member
        simp [balancedFlattenStageBits])
  exact run_linkPrograms hpositive hlength
    (run_linkPrograms hpositive hlength htree hcall)
    (run_linkPrograms hpositive hlength hflatten hbuild)

/-! ## §4 The two-element case

Appending two balanced codes is §3 at a two-element outer list, so the whole
front end is the eight instructions that build that list. -/

/-- The balanced code of the pair's two components, as a two-element list. -/
def pairToBalancedPairProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 1 3
  , .pair 4 2 2 4
  , .pair 4 3 3 5
  , .pair 2 3 2 6
  , .set 4 2 7
  , .pair 4 2 0 8
  , .halt 0
  ]

@[simp] theorem pairToBalancedPairProgram_oracleFree :
    OracleFree pairToBalancedPairProgram := by
  rfl

def pairToBalancedPairFuel : ℕ := 9

theorem encodeBalancedList_pair (left right : ℕ) :
    encodeBalancedList [left, right] =
      Nat.pair 2 (Nat.pair (Nat.pair 1 left) (Nat.pair 1 right)) := by
  simp [encodeBalancedList]

theorem run_pairToBalancedPairProgram
    (inputLength left right maximumBits : ℕ)
    (hbits : natBitLength (encodeBalancedList [left, right]) ≤ maximumBits) :
    runNPOracleProgram pairToBalancedPairProgram maximumBits
        pairToBalancedPairFuel
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some (encodeBalancedList [left, right]) := by
  rw [encodeBalancedList_pair] at hbits
  have hbranches :
      natBitLength (Nat.pair (Nat.pair 1 left) (Nat.pair 1 right)) ≤
        maximumBits :=
    le_trans (natBitLength_mono (Nat.right_le_pair 2 _)) hbits
  have hleftLeaf : natBitLength (Nat.pair 1 left) ≤ maximumBits :=
    le_trans (natBitLength_mono (Nat.left_le_pair _ _)) hbranches
  have hrightLeaf : natBitLength (Nat.pair 1 right) ≤ maximumBits :=
    le_trans (natBitLength_mono (Nat.right_le_pair _ _)) hbranches
  have hleft : natBitLength left ≤ maximumBits :=
    le_trans (natBitLength_mono (Nat.right_le_pair 1 left)) hleftLeaf
  have hright : natBitLength right ≤ maximumBits :=
    le_trans (natBitLength_mono (Nat.right_le_pair 1 right)) hrightLeaf
  have hone : natBitLength 1 ≤ maximumBits :=
    le_trans (natBitLength_mono (Nat.left_le_pair 1 left)) hleftLeaf
  have htwo : natBitLength 2 ≤ maximumBits :=
    le_trans (natBitLength_mono (Nat.left_le_pair 2 _)) hbits
  rw [encodeBalancedList_pair]
  rw [show pairToBalancedPairFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  rw [show (8 : ℕ) = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_set_instruction (value := 1) (by rfl) rfl hone]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 left) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleftLeaf]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 right) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrightLeaf]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair 1 left) (Nat.pair 1 right)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbranches]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_set_instruction (value := 2) (by rfl) rfl htwo]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair 2 (Nat.pair (Nat.pair 1 left) (Nat.pair 1 right)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbits]
  exact run_halt_instruction (fuel := 0)
    (value := Nat.pair 2 (Nat.pair (Nat.pair 1 left) (Nat.pair 1 right)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hbits

/-- **The balanced append program.** -/
def balancedAppendProgram : NPOracleProgram :=
  linkPrograms pairToBalancedPairProgram balancedFlattenProgram

theorem balancedAppendProgram_oracleFree :
    OracleFree balancedAppendProgram :=
  oracleFree_linkPrograms pairToBalancedPairProgram_oracleFree
    balancedFlattenProgram_oracleFree

def balancedAppendFuel (inputLength : ℕ) (left right : List ℕ) : ℕ :=
  linkFuel balancedFlattenProgram pairToBalancedPairFuel
    (balancedFlattenFuel inputLength [left, right])

def balancedAppendStageBits
    (inputLength : ℕ) (left right : List ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , natBitLength
      (encodeBalancedList [encodeBalancedList left, encodeBalancedList right])
  , balancedFlattenBits inputLength [left, right]
  ]

def balancedAppendBits (inputLength : ℕ) (left right : List ℕ) : ℕ :=
  (balancedAppendStageBits inputLength left right).foldr max 1

/-- **Two balanced codes concatenated, executed on the pair ABI.** -/
theorem run_balancedAppendProgram
    (inputLength maximumBits : ℕ) (left right : List ℕ)
    (hbits : balancedAppendBits inputLength left right ≤ maximumBits) :
    runNPOracleProgram balancedAppendProgram maximumBits
        (balancedAppendFuel inputLength left right)
        (initialNPOracleState inputLength
          (Nat.pair (encodeBalancedList left) (encodeBalancedList right))) =
      some (encodeBalancedList (left ++ right)) := by
  have bits_of_member {entry : ℕ}
      (hentry : entry ∈ balancedAppendStageBits inputLength left right) :
      entry ≤ maximumBits :=
    le_trans (stageBits_le_of_mem hentry) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [balancedAppendStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [balancedAppendStageBits]
  have hfront :
      runNPOracleProgram pairToBalancedPairProgram maximumBits
          pairToBalancedPairFuel
          (initialNPOracleState inputLength
            (Nat.pair (encodeBalancedList left) (encodeBalancedList right))) =
        some
          (encodeBalancedList
            [encodeBalancedList left, encodeBalancedList right]) :=
    run_pairToBalancedPairProgram inputLength (encodeBalancedList left)
      (encodeBalancedList right) maximumBits
      (by
        apply bits_of_member
        simp [balancedAppendStageBits])
  have hstreams :
      ([left, right] : List (List ℕ)).map encodeBalancedList =
        [encodeBalancedList left, encodeBalancedList right] := by
    simp
  have hflattenList : ([left, right] : List (List ℕ)).flatten = left ++ right := by
    simp
  have hflatten :
      runNPOracleProgram balancedFlattenProgram maximumBits
          (balancedFlattenFuel inputLength [left, right])
          (initialNPOracleState inputLength
            (encodeBalancedList
              [encodeBalancedList left, encodeBalancedList right])) =
        some (encodeBalancedList (left ++ right)) := by
    have hrun :=
      run_balancedFlattenProgram inputLength maximumBits [left, right]
        (by
          apply bits_of_member
          simp [balancedAppendStageBits])
    rw [hstreams, hflattenList] at hrun
    exact hrun
  exact run_linkPrograms hpositive hlength hfront hflatten

end NearCubicWires.CanonicalBalancedFlattenProgram
