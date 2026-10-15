import Proof.MachineModel.BoundedOracleStructuralFormulaPrefixSATProgram
import Proof.MachineModel.CanonicalSymmetricRowTableRequestProgram
import Proof.MachineModel.CaseTwoOccurrenceProgram

namespace NearCubicWires.CaseTwoDescriptionBitPoolProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaPrefixSATProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CanonicalSymmetricRowTableRequestProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-- The prefix-SAT request of one description coordinate. -/
def descriptionBitRequestOutput (context index : ℕ) : ℕ :=
  Nat.pair context (encodeUnary (index + 1))

/-- Register ABI:

* `r0`: the pool's request body and then the reducer's request;
* `r2`: the requested coordinate and then the unary countdown;
* `r3`: the retained atom stream;
* `r4`: the unary accumulator;
* `r5`: the constant one, also the unconditional back edge. -/
def descriptionBitRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 0 3
  , .set 5 1 4
  , .increment 2 5
  , .branchZero 2 9 6
  , .pair 5 4 4 7
  , .decrement 2 8
  , .branchZero 5 5 5
  , .pair 3 4 0 10
  , .halt 0
  ]

@[simp] theorem descriptionBitRequestProgram_oracleFree :
    OracleFree descriptionBitRequestProgram := by
  rfl

private def descriptionBitRequestLoopFuel (counter : ℕ) : ℕ :=
  4 * counter + 3

/-- Five setup instructions, four instructions per unary cell, and three for
the exit test, the pairing and the halt. -/
def descriptionBitRequestFuel (index : ℕ) : ℕ :=
  4 * index + 12

def descriptionBitRequestBits (context index : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair index context)
      (max (index + 1) (descriptionBitRequestOutput context index)))

private theorem encodeUnary_succ (count : ℕ) :
    encodeUnary (count + 1) = Nat.pair 1 (encodeUnary count) := rfl

private theorem encodeUnary_mono {left right : ℕ} (hle : left ≤ right) :
    encodeUnary left ≤ encodeUnary right := by
  induction right with
  | zero =>
      rw [Nat.le_zero.mp hle]
  | succ right ih =>
      rcases Nat.lt_or_ge left (right + 1) with hlt | hge
      · refine (ih (Nat.lt_succ_iff.mp hlt)).trans ?_
        rw [encodeUnary_succ]
        exact Nat.right_le_pair 1 (encodeUnary right)
      · rw [Nat.le_antisymm hle hge]

private theorem run_descriptionBitRequestLoop
    (context maximumBits : ℕ) (counter accumulated : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 5)
    (hcounter : state.registers 2 = counter)
    (hcontext : state.registers 3 = context)
    (haccumulated : state.registers 4 = encodeUnary accumulated)
    (hone : state.registers 5 = 1)
    (hcounterBits : natBitLength counter ≤ maximumBits)
    (hunaryBits :
      natBitLength (encodeUnary (accumulated + counter)) ≤ maximumBits)
    (houtputBits :
      natBitLength (Nat.pair context (encodeUnary (accumulated + counter))) ≤
        maximumBits) :
    runNPOracleProgram descriptionBitRequestProgram maximumBits
        (descriptionBitRequestLoopFuel counter) state =
      some (Nat.pair context (encodeUnary (accumulated + counter))) := by
  induction counter generalizing accumulated state with
  | zero =>
      have houtput :
          natBitLength (Nat.pair context (encodeUnary accumulated)) ≤
            maximumBits := by
        simpa using houtputBits
      rw [descriptionBitRequestLoopFuel]
      rw [show 4 * 0 + 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcounter, if_pos rfl]
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction
        (value := Nat.pair context (encodeUnary accumulated))
        (by rfl) rfl
        (by simp [NPOracleState.jump, hcontext, haccumulated])
        houtput]
      rw [run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        houtput]
      simp
  | succ counter ih =>
      have htotal :
          accumulated + (counter + 1) = accumulated + 1 + counter := by
        omega
      have hstepBits :
          natBitLength (encodeUnary (accumulated + 1)) ≤ maximumBits := by
        refine (natBitLength_mono (encodeUnary_mono ?_)).trans hunaryBits
        omega
      have hcounterStepBits : natBitLength counter ≤ maximumBits :=
        (natBitLength_mono (Nat.le_succ counter)).trans hcounterBits
      rw [htotal] at hunaryBits houtputBits ⊢
      rw [descriptionBitRequestLoopFuel]
      rw [show 4 * (counter + 1) + 3 =
          (descriptionBitRequestLoopFuel counter + 3) + 1 by
        unfold descriptionBitRequestLoopFuel
        omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcounter, if_neg (Nat.succ_ne_zero counter)]
      rw [show descriptionBitRequestLoopFuel counter + 3 =
          (descriptionBitRequestLoopFuel counter + 2) + 1 by omega]
      rw [run_pair_instruction (value := encodeUnary (accumulated + 1))
        (by rfl) rfl
        (by simp [NPOracleState.jump, hone, haccumulated, encodeUnary_succ])
        hstepBits]
      rw [show descriptionBitRequestLoopFuel counter + 2 =
          (descriptionBitRequestLoopFuel counter + 1) + 1 by omega]
      rw [run_decrement_instruction (value := counter)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hcounter])
        hcounterStepBits]
      rw [run_branchZero_instruction (by rfl) rfl, ite_self]
      exact ih (accumulated + 1) _ rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump, hcontext])
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump, hone])
        hcounterStepBits hunaryBits houtputBits

/-- **The coordinate request, executed.**  One pool request body becomes one
prefix-SAT request, with the coordinate counted out in unary. -/
theorem run_descriptionBitRequestProgram (inputLength context index : ℕ) :
    runNPOracleProgram descriptionBitRequestProgram
        (descriptionBitRequestBits context index)
        (descriptionBitRequestFuel index)
        (initialNPOracleState inputLength (Nat.pair index context)) =
      some (descriptionBitRequestOutput context index) := by
  have houtputBits :
      natBitLength (descriptionBitRequestOutput context index) ≤
        descriptionBitRequestBits context index :=
    natBitLength_mono ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hunaryBits :
      natBitLength (encodeUnary (index + 1)) ≤
        descriptionBitRequestBits context index :=
    (natBitLength_mono
      (Nat.right_le_pair context (encodeUnary (index + 1)))).trans houtputBits
  have hrequestBits :
      natBitLength (Nat.pair index context) ≤
        descriptionBitRequestBits context index :=
    natBitLength_mono (Nat.le_max_left _ _)
  have hindexBits :
      natBitLength index ≤ descriptionBitRequestBits context index :=
    (natBitLength_mono (Nat.left_le_pair index context)).trans hrequestBits
  have hcontextBits :
      natBitLength context ≤ descriptionBitRequestBits context index :=
    (natBitLength_mono (Nat.right_le_pair index context)).trans hrequestBits
  have hsuccBits :
      natBitLength (index + 1) ≤ descriptionBitRequestBits context index :=
    natBitLength_mono ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hzeroBits :
      natBitLength 0 ≤ descriptionBitRequestBits context index :=
    (natBitLength_mono (Nat.zero_le _)).trans hindexBits
  have honeBits :
      natBitLength 1 ≤ descriptionBitRequestBits context index :=
    (natBitLength_mono (by omega)).trans hsuccBits
  rw [show descriptionBitRequestFuel index =
      descriptionBitRequestLoopFuel (index + 1) + 1 + 1 + 1 + 1 + 1 by
    unfold descriptionBitRequestFuel descriptionBitRequestLoopFuel
    omega]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hindexBits]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  rw [run_increment_instruction (value := index + 1)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hsuccBits]
  rw [show descriptionBitRequestOutput context index =
      Nat.pair context (encodeUnary (0 + (index + 1))) by
    rw [Nat.zero_add]
    rfl]
  refine run_descriptionBitRequestLoop context
    (descriptionBitRequestBits context index) (index + 1) 0 _ ?_ ?_ ?_ ?_ ?_
    hsuccBits ?_ ?_
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, encodeUnary]
  · simp [NPOracleState.write, NPOracleState.jump]
  · rw [Nat.zero_add]
    exact hunaryBits
  · rw [Nat.zero_add]
    exact houtputBits

def descriptionBitLeafProgram : NPOracleProgram :=
  linkPrograms descriptionBitRequestProgram
    boundedOracleStructuralFormulaPrefixSATProgram

theorem descriptionBitLeafProgram_containsSAT :
    containsSAT descriptionBitLeafProgram = true := by
  rw [descriptionBitLeafProgram, containsSAT_linkPrograms,
    boundedOracleStructuralFormulaPrefixSATProgram_containsSAT]
  exact Bool.or_true _

def descriptionBitValue
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound index : ℕ) : ℕ :=
  prefixSATOutput (index + 1) (boundedOracleRecoveryFormula pcp input bound)

/-- The atom stream the whole pool shares. -/
def descriptionAtomContext
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : ℕ :=
  encodeBalancedList (boundedOracleStructuralFormulaAtoms pcp input bound)

def descriptionBitLeafFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound index : ℕ) : ℕ :=
  linkFuel boundedOracleStructuralFormulaPrefixSATProgram
    (descriptionBitRequestFuel index)
    (boundedOracleStructuralFormulaPrefixFuel pcp input bound (index + 1))

def descriptionBitLeafBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength index : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (descriptionBitRequestBits (descriptionAtomContext pcp input bound) index)
    (boundedOracleStructuralFormulaPrefixMaximumBits pcp input bound
      (index + 1) inputLength)

theorem run_descriptionBitLeafProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength index : ℕ) :
    runNPOracleProgram descriptionBitLeafProgram
        (descriptionBitLeafBits pcp input bound inputLength index)
        (descriptionBitLeafFuel pcp input bound index)
        (initialNPOracleState inputLength
          (Nat.pair index (descriptionAtomContext pcp input bound))) =
      some (descriptionBitValue pcp input bound index) := by
  have hsecond :
      runNPOracleProgram boundedOracleStructuralFormulaPrefixSATProgram
          (boundedOracleStructuralFormulaPrefixMaximumBits pcp input bound
            (index + 1) inputLength)
          (boundedOracleStructuralFormulaPrefixFuel pcp input bound (index + 1))
          (initialNPOracleState inputLength
            (descriptionBitRequestOutput
              (descriptionAtomContext pcp input bound) index)) =
        some (descriptionBitValue pcp input bound index) := by
    simpa only [descriptionBitRequestOutput, descriptionAtomContext,
      descriptionBitValue, boundedOracleStructuralFormulaPrefixInput] using
      run_boundedOracleStructuralFormulaPrefixSATProgram pcp input bound
        (index + 1) inputLength
  exact run_occurrenceStage
    (run_descriptionBitRequestProgram inputLength
      (descriptionAtomContext pcp input bound) index)
    hsecond

/-! ## 3. The pool -/

def descriptionBitPoolProgram : NPOracleProgram :=
  indexedPoolListProgram descriptionBitLeafProgram

def descriptionBitPoolFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength count : ℕ) : ℕ :=
  indexedPoolListFuel descriptionBitLeafProgram inputLength count
    (descriptionAtomContext pcp input bound)
    (descriptionBitLeafFuel pcp input bound)

def descriptionBitPoolBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength count : ℕ) : ℕ :=
  max
    (indexedPoolListBits inputLength count
      (descriptionAtomContext pcp input bound)
      (descriptionBitValue pcp input bound))
    (((List.range count).map
      (descriptionBitLeafBits pcp input bound inputLength)).foldr max 1)

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) : value ≤ values.foldr max 1 := by
  induction values with
  | nil => exact absurd hmem List.not_mem_nil
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

/-- **The description pool, executed.**  From the pool's own request word the
fixed stream returns the balanced list of every recovered description bit
below the requested count. -/
theorem run_descriptionBitPoolProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound inputLength count maximumBits : ℕ)
    (hbits :
      descriptionBitPoolBits pcp input bound inputLength count ≤ maximumBits) :
    runNPOracleProgram descriptionBitPoolProgram maximumBits
        (descriptionBitPoolFuel pcp input bound inputLength count)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count
            (descriptionAtomContext pcp input bound))) =
      some
        (encodeBalancedList
          ((List.range count).map (descriptionBitValue pcp input bound))) := by
  have hpoolBits :
      indexedPoolListBits inputLength count
          (descriptionAtomContext pcp input bound)
          (descriptionBitValue pcp input bound) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hleafBits :
      ∀ index : ℕ, index < count →
        descriptionBitLeafBits pcp input bound inputLength index ≤
          maximumBits := by
    intro index hindex
    have hmember :
        descriptionBitLeafBits pcp input bound inputLength index ∈
          (List.range count).map
            (descriptionBitLeafBits pcp input bound inputLength) :=
      List.mem_map_of_mem (List.mem_range.mpr hindex)
    exact (le_foldr_max_of_mem hmember).trans
      ((Nat.le_max_right _ _).trans hbits)
  exact run_indexedPoolListProgram descriptionBitLeafProgram inputLength count
    (descriptionAtomContext pcp input bound) maximumBits
    (descriptionBitLeafFuel pcp input bound)
    (descriptionBitValue pcp input bound) hpoolBits
    (fun index hindex =>
      run_bits_mono
        (run_descriptionBitLeafProgram pcp input bound inputLength index)
        (hleafBits index hindex))

/-! ## 4. The canonical description -/

/-- On a legal accepting oracle the pooled coordinates are the canonical
bounded-circuit description of the oracle's own circuit, bit for bit. -/
theorem map_descriptionBitValue_eq_canonical
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical : CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input) :
    (List.range
          (descriptionWidth (pcp.nativeWidth n)
            (sizeBound (pcp.nativeWidth n)))).map
        (descriptionBitValue pcp input (sizeBound (pcp.nativeWidth n))) =
      (canonicalBoundedCircuitDescription (sizeBound (pcp.nativeWidth n))
        canonical.circuit).map Bool.toNat := by
  have hlength :
      (canonicalBoundedCircuitDescription (sizeBound (pcp.nativeWidth n))
          canonical.circuit).length =
        descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)) :=
    canonicalBoundedCircuitDescription_length canonical.circuit
      canonical.sizeBounded
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, hlength]
  · intro index hleft _hright
    have hindex :
        index <
          descriptionWidth (pcp.nativeWidth n)
            (sizeBound (pcp.nativeWidth n)) := by
      simpa only [List.length_map, List.length_range] using hleft
    have hbit :=
      prefixSATOutput_boundedOracle_eq_canonical pcp input canonical
        ⟨index, hindex⟩
    simp only [List.getElem_map, List.getElem_range]
    simpa only [descriptionBitValue, canonicalDescriptionInput] using hbit

/-- **The canonical description, emitted.**  From the coordinate count and the
emitter's atom stream, the pool returns the balanced list of the canonical
bounded-circuit description of the recovered oracle. -/
theorem run_descriptionBitPoolProgram_eq_canonical
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical : CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input)
    (inputLength maximumBits : ℕ)
    (hbits :
      descriptionBitPoolBits pcp input (sizeBound (pcp.nativeWidth n))
          inputLength
          (descriptionWidth (pcp.nativeWidth n)
            (sizeBound (pcp.nativeWidth n))) ≤
        maximumBits) :
    runNPOracleProgram descriptionBitPoolProgram maximumBits
        (descriptionBitPoolFuel pcp input (sizeBound (pcp.nativeWidth n))
          inputLength
          (descriptionWidth (pcp.nativeWidth n)
            (sizeBound (pcp.nativeWidth n))))
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput
            (descriptionWidth (pcp.nativeWidth n)
              (sizeBound (pcp.nativeWidth n)))
            (descriptionAtomContext pcp input
              (sizeBound (pcp.nativeWidth n))))) =
      some
        (encodeBalancedList
          ((canonicalBoundedCircuitDescription (sizeBound (pcp.nativeWidth n))
            canonical.circuit).map Bool.toNat)) := by
  rw [← map_descriptionBitValue_eq_canonical pcp input canonical]
  exact run_descriptionBitPoolProgram pcp input
    (sizeBound (pcp.nativeWidth n)) inputLength
    (descriptionWidth (pcp.nativeWidth n) (sizeBound (pcp.nativeWidth n)))
    maximumBits hbits

end NearCubicWires.CaseTwoDescriptionBitPoolProgram
