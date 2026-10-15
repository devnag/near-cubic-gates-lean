import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorSweptLeafClosure

namespace NearCubicWires.ValidatorTopologyRangeLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorResidualLeafBudget
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

open private booleanTopologyComparisonPrepareFuel booleanTopologyAndFuel
  booleanTopologyComparisonCallFuel booleanTopologyComparisonCallProgram
  booleanTopologyAndProgram booleanNodeTopologyRangeCalleeFuel from
  Proof.MachineModel.CanonicalBooleanNodeTopologyProgram

/-! ## §1 One comparison request -/

/-- Monotonicity of a linker node in both charges.  Stated over a *variable*
program, so no composed register span is ever evaluated. -/
private theorem linkFuel_mono {second : NPOracleProgram}
    {first first' tail tail' : ℕ} (hfirst : first ≤ first')
    (htail : tail ≤ tail') :
    linkFuel second first tail ≤ linkFuel second first' tail' := by
  simp only [linkFuel]
  omega

private theorem preserveRightFuel_mono {source source' : ℕ}
    (hle : source ≤ source') :
    preserveRightFuel source ≤ preserveRightFuel source' := by
  simp only [preserveRightFuel]
  omega

/-- One increment widens a code by at most one bit. -/
private theorem natBitLength_succ_le_succ (value : ℕ) :
    natBitLength (value + 1) ≤ natBitLength value + 1 := by
  rcases Nat.eq_zero_or_pos value with rfl | hpositive
  · have hzero : natBitLength 0 = 1 := natBitLength_zero
    have hone : natBitLength (0 + 1) = 1 := natBitLength_one
    omega
  · have hle : value + 1 ≤ value * 2 := by omega
    have hmono : Nat.log 2 (value + 1) ≤ Nat.log 2 (value * 2) :=
      Nat.log_mono_right hle
    have hmul : Nat.log 2 (value * 2) = Nat.log 2 value + 1 :=
      Nat.log_mul_base (by omega) (by omega)
    unfold natBitLength
    omega

/-- The closed program-shape overhead of one native less-than request. -/
def nativeLtRequestOverhead : ℕ :=
  nativeCallOverhead binaryNatLtProgram + 2 +
    (programRegisterSpan nativeNatLeProgram + 14)

/-- **One less-than request's charge is linear in the request's own width.**
Both operands are projections of the request, so nothing here reads a decoded
magnitude. -/
theorem nativeLtRequestFuel_le (request : ℕ) :
    nativeLtRequestFuel request ≤
      nativeLtRequestOverhead + 36 * (natBitLength request + 1) := by
  have hcall :=
    nativeCallFuel_le binaryNatLtProgram
      (2 + binaryNatLtLoopFuel (Nat.unpair request).2 (Nat.unpair request).1)
      (Nat.unpair request).1 (Nat.unpair request).2
  have hloop :=
    binaryNatLtLoopFuel_le (Nat.unpair request).2 (Nat.unpair request).1
  have hleft :
      natBitLength ((Nat.unpair request).2 + 1) ≤ natBitLength request + 1 := by
    have hstep := natBitLength_succ_le_succ (Nat.unpair request).2
    have hproject :
        natBitLength (Nat.unpair request).2 ≤ natBitLength request :=
      natBitLength_mono (Nat.unpair_right_le request)
    omega
  have hright :
      natBitLength (Nat.unpair request).1 ≤ natBitLength request :=
    natBitLength_mono (Nat.unpair_left_le request)
  have hmax :
      max (natBitLength ((Nat.unpair request).2 + 1))
          (natBitLength (Nat.unpair request).1) ≤ natBitLength request + 1 :=
    Nat.max_le.2 ⟨hleft, by omega⟩
  have hscale :
      36 * max (natBitLength ((Nat.unpair request).2 + 1))
            (natBitLength (Nat.unpair request).1) ≤
        36 * (natBitLength request + 1) :=
    Nat.mul_le_mul_left _ hmax
  simp only [nativeLtRequestFuel, nativeLtRequestOverhead]
  omega

/-- One packed comparison request, from bounds on its two operands. -/
private theorem natBitLength_nativeLtRequest_le {left right bound : ℕ}
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound) :
    natBitLength (nativeLtRequest left right) ≤ 2 * bound := by
  have hpair := pairCodeBits_le right left
  simp only [nativeLtRequest, nativeInputRequest]
  omega

/-- **The comparison pair's width.**  Every operand the topology check compares
is `0`, `1`, a projection of the descriptor, the public arity or the index. -/
theorem natBitLength_booleanTopologyComparisonRequests_le
    (inputLength descriptor index bound : ℕ) (hone : 1 ≤ bound)
    (hdescriptor : natBitLength descriptor ≤ bound)
    (hinput : natBitLength inputLength ≤ bound)
    (hindex : natBitLength index ≤ bound) :
    natBitLength (booleanTopologyComparisonRequests inputLength descriptor index)
      ≤ 4 * bound := by
  have hzero : natBitLength 0 ≤ bound := by
    rw [natBitLength_zero]; omega
  have hunit : natBitLength 1 ≤ bound := by
    rw [natBitLength_one]; omega
  have hbody :
      natBitLength (Nat.unpair (Nat.unpair descriptor).2).2 ≤ bound :=
    le_trans
      (natBitLength_mono
        ((Nat.unpair_right_le _).trans (Nat.unpair_right_le descriptor)))
      hdescriptor
  have hbodyLeft :
      natBitLength (Nat.unpair (Nat.unpair (Nat.unpair descriptor).2).2).1 ≤
        bound :=
    le_trans (natBitLength_mono (Nat.unpair_left_le _)) hbody
  have hbodyRight :
      natBitLength (Nat.unpair (Nat.unpair (Nat.unpair descriptor).2).2).2 ≤
        bound :=
    le_trans (natBitLength_mono (Nat.unpair_right_le _)) hbody
  have htrue : natBitLength topologyTrueRequest ≤ 2 * bound := by
    rw [topologyTrueRequest]
    exact natBitLength_nativeLtRequest_le hzero hunit
  have hfalse : natBitLength topologyFalseRequest ≤ 2 * bound := by
    rw [topologyFalseRequest]
    exact natBitLength_nativeLtRequest_le hunit hzero
  have hpack :
      ∀ first second : ℕ, natBitLength first ≤ 2 * bound →
        natBitLength second ≤ 2 * bound →
        natBitLength (Nat.pair first second) ≤ 4 * bound := by
    intro first second hfirst hsecond
    have hpair := pairCodeBits_le first second
    omega
  simp only [booleanTopologyComparisonRequests]
  split
  · exact hpack _ _ hfalse hfalse
  · split
    · exact hpack _ _ hfalse hfalse
    · split
      · exact hpack _ _ htrue htrue
      · split
        · exact hpack _ _
            (natBitLength_nativeLtRequest_le hbody hinput) htrue
        · split
          · exact hpack _ _
              (natBitLength_nativeLtRequest_le hbody hindex) htrue
          · split
            · exact hpack _ _
                (natBitLength_nativeLtRequest_le hbodyLeft hindex)
                (natBitLength_nativeLtRequest_le hbodyRight hindex)
            · exact hpack _ _ hfalse hfalse

/-! ## §2 The per-descriptor topology charge -/

/-- The charge one comparison pair costs, as a closed linear budget. -/
def topologyComparisonBudget (bound : ℕ) : ℕ :=
  pairedCallOverhead nativeLtRequestProgram +
      (nativeLtRequestOverhead + 36 * (4 * bound + 1)) +
    (nativeLtRequestOverhead + 36 * (4 * bound + 1))

/-- One paired call is a closed overhead plus its two operand charges. -/
private theorem pairedCallFuel_le (source : NPOracleProgram)
    (left right : ℕ) :
    pairedCallFuel source left right ≤
      pairedCallOverhead source + left + right := by
  simp only [pairedCallFuel, pairedCallOverhead, linkFuel, preserveRightFuel]
  omega

/-- **The topology check's comparison call, bounded.** -/
theorem booleanTopologyComparisonCallFuel_le
    (inputLength descriptor index bound : ℕ) (hone : 1 ≤ bound)
    (hdescriptor : natBitLength descriptor ≤ bound)
    (hinput : natBitLength inputLength ≤ bound)
    (hindex : natBitLength index ≤ bound) :
    booleanTopologyComparisonCallFuel
        (Nat.unpair
          (booleanTopologyComparisonRequests inputLength descriptor index)).1
        (Nat.unpair
          (booleanTopologyComparisonRequests inputLength descriptor index)).2 ≤
      topologyComparisonBudget bound := by
  have hrequests :=
    natBitLength_booleanTopologyComparisonRequests_le inputLength descriptor
      index bound hone hdescriptor hinput hindex
  have hfirst :
      natBitLength
          (Nat.unpair
            (booleanTopologyComparisonRequests inputLength descriptor index)).1 ≤
        4 * bound :=
    le_trans (natBitLength_mono (Nat.unpair_left_le _)) hrequests
  have hsecond :
      natBitLength
          (Nat.unpair
            (booleanTopologyComparisonRequests inputLength descriptor index)).2 ≤
        4 * bound :=
    le_trans (natBitLength_mono (Nat.unpair_right_le _)) hrequests
  have hleftLeaf :=
    nativeLtRequestFuel_le
      (Nat.unpair
        (booleanTopologyComparisonRequests inputLength descriptor index)).1
  have hrightLeaf :=
    nativeLtRequestFuel_le
      (Nat.unpair
        (booleanTopologyComparisonRequests inputLength descriptor index)).2
  have hpaired :=
    pairedCallFuel_le nativeLtRequestProgram
      (nativeLtRequestFuel
        (Nat.unpair
          (booleanTopologyComparisonRequests inputLength descriptor index)).1)
      (nativeLtRequestFuel
        (Nat.unpair
          (booleanTopologyComparisonRequests inputLength descriptor index)).2)
  simp only [booleanTopologyComparisonCallFuel, topologyComparisonBudget]
  omega

/-- The budget one descriptor's topology check costs. -/
def topologyNodeBudget (bound : ℕ) : ℕ :=
  linkFuel
    (linkPrograms booleanTopologyComparisonCallProgram booleanTopologyAndProgram)
    booleanTopologyComparisonPrepareFuel
    (linkFuel booleanTopologyAndProgram (topologyComparisonBudget bound)
      booleanTopologyAndFuel)

/-- **The per-descriptor topology charge, bounded.** -/
theorem booleanNodeTopologyFuel_le
    (inputLength descriptor index bound : ℕ) (hone : 1 ≤ bound)
    (hdescriptor : natBitLength descriptor ≤ bound)
    (hinput : natBitLength inputLength ≤ bound)
    (hindex : natBitLength index ≤ bound) :
    booleanNodeTopologyFuel inputLength descriptor index ≤
      topologyNodeBudget bound := by
  have hcall :=
    booleanTopologyComparisonCallFuel_le inputLength descriptor index bound hone
      hdescriptor hinput hindex
  simp only [booleanNodeTopologyFuel, topologyNodeBudget]
  exact linkFuel_mono le_rfl (linkFuel_mono hcall le_rfl)

def topologyLookupBudget (count bound : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram canonicalBalancedLookupProgram)
      booleanNodeTopologyProgram)
    8
    (linkFuel booleanNodeTopologyProgram
      (preserveRightFuel (27 * (count + 1))) (topologyNodeBudget bound))

theorem booleanNodeTopologyLookupFuel_le
    (inputLength : ℕ) (descriptors : List ℕ) (index bound : ℕ)
    (hone : 1 ≤ bound) (hindex : index < descriptors.length)
    (hdescriptor : ∀ code ∈ descriptors, natBitLength code ≤ bound)
    (hinput : natBitLength inputLength ≤ bound)
    (hindexWidth : natBitLength index ≤ bound) :
    booleanNodeTopologyLookupFuel inputLength descriptors index ≤
      topologyLookupBudget descriptors.length bound := by
  have hmember : descriptors[index]! ∈ descriptors := by
    rw [getElem!_pos descriptors index hindex]
    exact List.getElem_mem hindex
  have hlookup := balancedLookupFuel_le descriptors index hindex
  have htopology :=
    booleanNodeTopologyFuel_le inputLength descriptors[index]! index bound hone
      (hdescriptor _ hmember) hinput hindexWidth
  simp only [booleanNodeTopologyLookupFuel, topologyLookupBudget]
  exact linkFuel_mono le_rfl
    (linkFuel_mono (preserveRightFuel_mono hlookup) htopology)

/-! ### The budgets, dominated -/

theorem exists_topologyNodeBudget_polyBounded (coefficient degree : ℕ) :
    ∃ budget : ℕ, ∀ bound measure : ℕ,
      PolyBounded bound measure coefficient degree →
      PolyBounded (topologyNodeBudget bound) measure budget degree := by
  exact ⟨_, fun bound measure hbound => by
  have hleaf :
      PolyBounded (nativeLtRequestOverhead + 36 * (4 * bound + 1)) measure
        (nativeLtRequestOverhead + 36 * (4 * coefficient + 1)) degree :=
    (polyBounded_const nativeLtRequestOverhead measure degree).add
      (((hbound.const_mul 4).add
        (polyBounded_const 1 measure degree)).const_mul 36)
  have hcomparison :
      PolyBounded (topologyComparisonBudget bound) measure
        (pairedCallOverhead nativeLtRequestProgram +
            (nativeLtRequestOverhead + 36 * (4 * coefficient + 1)) +
          (nativeLtRequestOverhead + 36 * (4 * coefficient + 1))) degree :=
    ((polyBounded_const (pairedCallOverhead nativeLtRequestProgram) measure
      degree).add hleaf).add hleaf
  exact linkFuel_polyBounded (polyBounded_const _ measure degree)
    (linkFuel_polyBounded hcomparison (polyBounded_const _ measure degree))⟩

theorem exists_topologyLookupBudget_polyBounded
    (countCoefficient coefficient degree : ℕ) :
    ∃ budget : ℕ, ∀ count bound measure : ℕ,
      PolyBounded count measure countCoefficient degree →
      PolyBounded bound measure coefficient degree →
      PolyBounded (topologyLookupBudget count bound) measure budget degree := by
  obtain ⟨nodeBudget, hnode⟩ :=
    exists_topologyNodeBudget_polyBounded coefficient degree
  exact ⟨_, fun count bound measure hcount hbound => by
  have hlookup :
      PolyBounded (27 * (count + 1)) measure (27 * (countCoefficient + 1))
        degree :=
    ((hcount.add (polyBounded_const 1 measure degree)).const_mul 27)
  exact linkFuel_polyBounded (polyBounded_const 8 measure degree)
    (linkFuel_polyBounded (preserveRightFuel_polyBounded hlookup)
      (hnode bound measure hbound))⟩

/-! ## §3 The range aggregation

`booleanNodeTopologyRangeFuel` is one `fixedBooleanRangeAggregationFuel`: a
generated range, a counted call at the descriptor count, and one Boolean count.
The counted call is the only degree-raising node. -/

/-- Every generated request's index is an index into the descriptor list. -/
private theorem booleanNodeTopologyRangeIndex_lt
    {inputLength count context request : ℕ}
    (hrequest : request ∈ fixedBooleanRangeRequests inputLength count context) :
    booleanNodeTopologyRangeIndex request < count := by
  rw [fixedBooleanRangeRequests, balancedRangeRequestAtoms_eq_map_range,
    List.mem_map] at hrequest
  obtain ⟨offset, hoffset, rfl⟩ := hrequest
  rw [List.mem_range] at hoffset
  simp only [booleanNodeTopologyRangeIndex, balancedRangeRequestAtom,
    Nat.unpair_pair]
  omega

/-- **The topology range aggregation, dominated.**  This is the second of the
Boolean circuit validator's two remaining charges, and it is now closed: the
walk's only degree-raising node is the counted call at the descriptor count. -/
theorem exists_booleanNodeTopologyRangeFuel_polyBounded
    (countCoefficient coefficient countDegree degree : ℕ)
    (hraise : countDegree ≤ degree) :
    ∃ budget : ℕ, ∀ (inputLength : ℕ) (descriptors : List ℕ) (bound measure : ℕ),
      1 ≤ bound →
      (∀ code ∈ descriptors, natBitLength code ≤ bound) →
      natBitLength inputLength ≤ bound →
      natBitLength descriptors.length ≤ bound →
      PolyBounded descriptors.length measure countCoefficient countDegree →
      PolyBounded bound measure coefficient degree →
      PolyBounded (booleanNodeTopologyRangeFuel inputLength descriptors) measure
        budget (countDegree + degree) := by
  obtain ⟨leafBudget, hleafBudget⟩ :=
    exists_topologyLookupBudget_polyBounded countCoefficient coefficient degree
  exact ⟨_, fun inputLength descriptors bound measure hone hdescriptor hinput
      hindexWidth hcount hbound => by
  have hleaf :=
    hleafBudget descriptors.length bound measure (hcount.degree_mono hraise)
      hbound
  have hsum : degree ≤ countDegree + degree := by omega
  have hcountSum : countDegree ≤ countDegree + degree := by omega
  have hrequestLength :
      (fixedBooleanRangeRequests inputLength descriptors.length
        (booleanNodeTopologyRangeContext descriptors)).length =
        descriptors.length := by
    simp only [fixedBooleanRangeRequests, balancedRangeRequestAtoms_length]
  have hvalueLength :
      (fixedBooleanRangeValues inputLength descriptors.length
        (booleanNodeTopologyRangeContext descriptors)
        (booleanNodeTopologyRangeValue inputLength descriptors)).length =
        descriptors.length := by
    simp only [fixedBooleanRangeValues, List.length_map, hrequestLength]
  have hrange :
      PolyBounded
        (generatedBalancedRangeFuel inputLength descriptors.length
          (booleanNodeTopologyRangeContext descriptors)) measure
        (42 * countCoefficient + 42) (countDegree + degree) := by
    refine (((hcount.add (polyBounded_const 1 measure countDegree)).const_mul
      42).degree_mono hcountSum).mono ?_
    exact generatedBalancedRangeFuel_le_linear _ _ _
  have hcall :=
    balancedCallFuel_polyBounded
      (callee := booleanNodeTopologyLookupProgram)
      (calleeFuel := booleanNodeTopologyRangeCalleeFuel inputLength descriptors)
      (bound := topologyLookupBudget descriptors.length bound)
      (by rw [hrequestLength]; exact hcount) hleaf
      (by
        intro request hrequest
        have hindex := booleanNodeTopologyRangeIndex_lt hrequest
        simpa only [booleanNodeTopologyRangeCalleeFuel] using
          booleanNodeTopologyLookupFuel_le inputLength descriptors
            (booleanNodeTopologyRangeIndex request) bound hone hindex
            hdescriptor hinput
            (le_trans (natBitLength_mono (Nat.le_of_lt hindex)) hindexWidth))
  have hcountFuel :
      PolyBounded
        (balancedBoolCountFuel
          (fixedBooleanRangeValues inputLength descriptors.length
            (booleanNodeTopologyRangeContext descriptors)
            (booleanNodeTopologyRangeValue inputLength descriptors))) measure
        (programRegisterSpan balancedBoolCountProjectionProgram + 5 +
          (30 * countCoefficient + 27) + 5) (countDegree + degree) :=
    (balancedBoolCountFuel_polyBounded
      (show PolyBounded
        (fixedBooleanRangeValues inputLength descriptors.length
          (booleanNodeTopologyRangeContext descriptors)
          (booleanNodeTopologyRangeValue inputLength descriptors)).length
        measure countCoefficient countDegree by
        rw [hvalueLength]; exact hcount)).degree_mono hcountSum
  simp only [booleanNodeTopologyRangeFuel, fixedBooleanRangeAggregationFuel,
    fixedBooleanRangeAfterGenerationFuel, fixedBooleanRangeMappedFuel,
    fixedBooleanRangeCallFuel, fixedBooleanRangeTailFuel]
  exact linkFuel_polyBounded hrange
    (linkFuel_polyBounded (preserveRightFuel_polyBounded hcall)
      (linkFuel_polyBounded (polyBounded_const 4 measure (countDegree + degree))
        hcountFuel))⟩

end NearCubicWires.ValidatorTopologyRangeLedger
