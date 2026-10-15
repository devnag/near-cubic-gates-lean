import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorLeafPremiseSweep
import Proof.Circuits.ValidatorTaggedSpineLedger

namespace NearCubicWires.ValidatorNodePreparationLedger

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedListValidationProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorDescriptionLeafClosure
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorTaggedSpineLedger
open NearCubicWires.VerifiedLinker

open private taggedListRetainFuel taggedNatRequests taggedNatRequestFuel
  taggedNatOutputTree taggedNatSingletonTree taggedNatSingletonTree_values from
  Proof.MachineModel.CanonicalTaggedNatListValidationProgram

/-! ## §1 The unit-budget transfer rule

`PolyBounded value (natBitLength raw) budget k` is a statement about one code.
Composed with a certificate for that code's width against the real measure it
becomes a statement about the request family, at `k` times the width's degree.
This is `ValidatorDescriptionLeafClosure` §1 read in the direction the walk
needs. -/

/-- **The transfer rule.**  A unit budget over a code's width, spent against a
width certificate. -/
theorem polyBounded_of_unitBudget
    {value width measure coefficient degree : ℕ} (budget k : ℕ)
    (hwidth : PolyBounded width measure coefficient degree)
    (hvalue : PolyBounded value width budget k) :
    PolyBounded value measure (budget * (coefficient + 1) ^ k) (k * degree) :=
  (polyBounded_unitBudget budget k hwidth).mono hvalue

/-- A unit budget survives a widening of the code it is read against. -/
theorem polyBounded_unitBudget_mono
    {value width width' budget k : ℕ} (hle : width ≤ width')
    (hvalue : PolyBounded value width budget k) :
    PolyBounded value width' budget k :=
  hvalue.trans (unitBudget_mono budget k hle)

/-- A unit budget read against a decoded atom's width, re-read against the code
the atom was parsed from. -/
theorem polyBounded_unitBudget_of_decoded
    {value inner outer budget k : ℕ} (hle : inner ≤ 3 * outer)
    (hvalue : PolyBounded value inner budget k) :
    PolyBounded value outer (budget * 3 ^ k) k :=
  hvalue.trans (unitBudget_of_decoded budget k hle)

/-! ## §2 The tagged-nat list validator

`taggedNatListValidationFuel` is a six-node `linkFuel` chain over six charges:
the retained spine, the tagged-to-balanced rebuild, the request framing, the
counted call into the canonical natural validator, the singleton tagging and the
stream flattener.  Five are counted by the record's *field count*, which
`ValidatorTaggedSpineLedger` §3 caps by the record's width; the sixth is the
counted call, and it is the only node that raises the degree. -/

/-- The record's field count, as a unit budget. -/
theorem polyBounded_taggedNatFieldCodes_length (raw : ℕ) :
    PolyBounded (taggedNatFieldCodes raw).length (natBitLength raw) 1 1 := by
  have hcount := taggedNatFieldCodes_length_succ_le raw
  have hself : (natBitLength raw + 1) ^ 1 = natBitLength raw + 1 := pow_one _
  change (taggedNatFieldCodes raw).length ≤ 1 * (natBitLength raw + 1) ^ 1
  omega

/-- The validated field outputs are counted by the same ledger. -/
theorem polyBounded_taggedNatFieldOutputs_length (raw : ℕ) :
    PolyBounded (taggedNatFieldOutputs raw).length (natBitLength raw) 1 1 := by
  have hcount := taggedNatFieldOutputs_length_succ_le raw
  have hself : (natBitLength raw + 1) ^ 1 = natBitLength raw + 1 := pow_one _
  change (taggedNatFieldOutputs raw).length ≤ 1 * (natBitLength raw + 1) ^ 1
  omega

/-- **The retained spine's ledger.**  One structural walk under two linkers and
a context-preserving wrapper: `ValidatorTaggedSpineLedger` §2's halving step is
the whole content. -/
theorem exists_taggedListRetainFuel_polyBounded :
    ∃ budget : ℕ, ∀ raw : ℕ,
      PolyBounded (taggedListRetainFuel raw) (natBitLength raw) budget 1 := by
  exact ⟨_, fun raw => by
  have hself := polyBounded_width_self (natBitLength raw)
  have hspine :
      PolyBounded (taggedListValidationFuel raw) (natBitLength raw) 14 1 := by
    refine ((hself.const_mul 7).add
      (polyBounded_const 7 (natBitLength raw) 1)).mono ?_
    exact taggedListValidationFuel_le raw
  rw [taggedListRetainFuel]
  exact linkFuel_polyBounded
    (linkFuel_polyBounded (polyBounded_const 2 (natBitLength raw) 1)
      (preserveRightFuel_polyBounded hspine))
    (polyBounded_const 4 (natBitLength raw) 1)⟩

/-- **The counted call into the canonical natural validator.**  The only
degree-raising node of the chain: one call per field, and every field is no
wider than the record. -/
theorem exists_taggedNatBalancedCallFuel_polyBounded :
    ∃ budget : ℕ, ∀ inputLength raw : ℕ,
      PolyBounded
        (balancedCallFuel canonicalNatValidationProgram taggedNatRequestFuel
          (taggedNatRequests inputLength raw))
        (natBitLength raw) budget 2 := by
  exact ⟨_, fun inputLength raw => by
  have hcount :
      PolyBounded (taggedNatRequests inputLength raw).length
        (natBitLength raw) 1 1 := by
    rw [taggedNatRequests, List.length_map]
    exact polyBounded_taggedNatFieldCodes_length raw
  have hcallee :
      PolyBounded
        (canonicalNatValidationCoefficient 1 * (natBitLength raw + 1))
        (natBitLength raw) (canonicalNatValidationCoefficient 1) 1 := by
    change canonicalNatValidationCoefficient 1 * (natBitLength raw + 1) ≤
      canonicalNatValidationCoefficient 1 * (natBitLength raw + 1) ^ 1
    rw [pow_one]
  have hbound :
      ∀ request ∈ taggedNatRequests inputLength raw,
        taggedNatRequestFuel request ≤
          canonicalNatValidationCoefficient 1 * (natBitLength raw + 1) := by
    intro request hrequest
    rw [taggedNatRequests, List.mem_map] at hrequest
    obtain ⟨field, hfield, rfl⟩ := hrequest
    have hwidth :
        PolyBounded (natBitLength field) (natBitLength raw) 1 1 := by
      have hle := natBitLength_le_of_mem_taggedNatFieldCodes hfield
      have hself : (natBitLength raw + 1) ^ 1 = natBitLength raw + 1 :=
        pow_one _
      change natBitLength field ≤ 1 * (natBitLength raw + 1) ^ 1
      omega
    have hleaf := canonicalNatValidationFuel_polyBounded hwidth
    have hproject :
        taggedNatRequestFuel (nativeInputRequest inputLength field) =
          canonicalNatValidationFuel field := by
      rw [taggedNatRequestFuel, nativeInputRequest, Nat.unpair_pair]
    have hleafLe :
        canonicalNatValidationFuel field ≤
          canonicalNatValidationCoefficient 1 * (natBitLength raw + 1) ^ 1 :=
      hleaf
    rw [pow_one] at hleafLe
    rw [hproject]
    exact hleafLe
  exact balancedCallFuel_polyBounded hcount hcallee hbound⟩

/-- **The tagged-nat list validator's ledger.**  Degree `2` over the record's
own width: one counted call over a field count that is itself width-linear. -/
theorem exists_taggedNatListValidationFuel_polyBounded :
    ∃ budget : ℕ, ∀ inputLength raw : ℕ,
      PolyBounded (taggedNatListValidationFuel inputLength raw)
        (natBitLength raw) budget 2 := by
  obtain ⟨retainBudget, hretain⟩ := exists_taggedListRetainFuel_polyBounded
  obtain ⟨callBudget, hcall⟩ := exists_taggedNatBalancedCallFuel_polyBounded
  exact ⟨_, fun inputLength raw => by
  have hfields := polyBounded_taggedNatFieldCodes_length raw
  have houtputs := polyBounded_taggedNatFieldOutputs_length raw
  have hnodes :
      PolyBounded (taggedNatOutputTree raw).nodeCount (natBitLength raw) 3 1 := by
    refine ((houtputs.const_mul 2).add
      (polyBounded_const 1 (natBitLength raw) 1)).mono ?_
    rw [taggedNatOutputTree]
    exact balancedTraversalTree_nodeCount_le _
  have hretainStep :
      PolyBounded (taggedListRetainFuel raw) (natBitLength raw) retainBudget 2 :=
    (hretain raw).degree_mono (by omega)
  have hrebuild :
      PolyBounded (taggedToBalancedFuel (taggedNatFieldCodes raw))
        (natBitLength raw) (42 + 14) 2 := by
    refine (((hfields.const_mul 42).add
      (polyBounded_const 14 (natBitLength raw) 1)).degree_mono
        (by omega)).mono ?_
    exact taggedToBalancedFuel_le _
  have hframing :
      PolyBounded (nativeInputRequestTreeFuel (taggedNatFieldCodes raw))
        (natBitLength raw) (71 * 1 + 37) 2 :=
    (nativeInputRequestTreeFuel_polyBounded hfields).degree_mono (by omega)
  have hsingleton :
      PolyBounded (balancedBitSingletonTreeFuel (taggedNatOutputTree raw))
        (natBitLength raw) (39 * 3 + 2) 2 := by
    refine (((hnodes.const_mul 39).add
      (polyBounded_const 2 (natBitLength raw) 1)).degree_mono
        (by omega)).mono ?_
    exact balancedBitSingletonTreeFuel_le _
  have hflatten :
      PolyBounded (balancedTreeStreamFlattenFuel (taggedNatSingletonTree raw))
        (natBitLength raw) (16 * 3 + (16 * 1 + 7)) 2 := by
    refine ((((hnodes.const_mul 16).add
      ((houtputs.const_mul 16).add
        (polyBounded_const 7 (natBitLength raw) 1))).degree_mono
          (by omega))).mono ?_
    have hbound := balancedTreeStreamFlattenFuel_le (taggedNatSingletonTree raw)
    have hcount :
        (treeStreamValues (taggedNatSingletonTree raw)).length =
          (taggedNatFieldOutputs raw).length := by
      rw [taggedNatSingletonTree_values]
    have hmap :
        (taggedNatSingletonTree raw).nodeCount =
          (taggedNatOutputTree raw).nodeCount := by
      simp only [taggedNatSingletonTree, BalancedTraversalTree.nodeCount_map]
    omega
  rw [taggedNatListValidationFuel]
  exact linkFuel_polyBounded
    (linkFuel_polyBounded
      (linkFuel_polyBounded
        (linkFuel_polyBounded
          (linkFuel_polyBounded hretainStep hrebuild) hframing)
        (hcall inputLength raw))
      hsingleton)
    hflatten⟩

/-- **The node validator's ledger.**  One linker over §2. -/
theorem exists_booleanNodeValidationFuel_polyBounded :
    ∃ budget : ℕ, ∀ inputLength raw : ℕ,
      PolyBounded (booleanNodeValidationFuel inputLength raw)
        (natBitLength raw) budget 2 := by
  obtain ⟨taggedBudget, htagged⟩ :=
    exists_taggedNatListValidationFuel_polyBounded
  exact ⟨_, fun inputLength raw => by
  rw [booleanNodeValidationFuel]
  exact linkFuel_polyBounded (htagged inputLength raw)
    (polyBounded_const _ (natBitLength raw) 2)⟩

/-- The structural parse's descriptor count, as a unit budget. -/
theorem polyBounded_booleanNodeListAtoms_length (raw : ℕ) :
    PolyBounded (booleanNodeListAtoms raw).length (natBitLength raw) 2 1 := by
  have hcount := rawBalancedTraversalTree_atoms_length_succ_le raw
  have hself : (natBitLength raw + 1) ^ 1 = natBitLength raw + 1 := pow_one _
  change (booleanNodeListAtoms raw).length ≤ 2 * (natBitLength raw + 1) ^ 1
  rw [booleanNodeListAtoms]
  omega

/-- **The batch's counted call.**  One node validation per descriptor: the
second and last degree-raising node on the preparation path. -/
theorem exists_booleanNodeCallFuelFor_polyBounded :
    ∃ budget : ℕ, ∀ inputLength raw : ℕ,
      PolyBounded
        (booleanNodeCallFuelFor inputLength (booleanNodeListAtoms raw))
        (natBitLength raw) budget 3 := by
  obtain ⟨nodeBudget, hnode⟩ := exists_booleanNodeValidationFuel_polyBounded
  exact ⟨_, fun inputLength raw => by
  have hcount :
      PolyBounded
        (booleanNodeRequests inputLength (booleanNodeListAtoms raw)).length
        (natBitLength raw) 2 1 := by
    rw [booleanNodeRequests, List.length_map]
    exact polyBounded_booleanNodeListAtoms_length raw
  have hcallee :
      PolyBounded (nodeBudget * 3 ^ 2 * (natBitLength raw + 1) ^ 2)
        (natBitLength raw) (nodeBudget * 3 ^ 2) 2 := le_rfl
  have hbound :
      ∀ request ∈ booleanNodeRequests inputLength (booleanNodeListAtoms raw),
        booleanNodeCallFuel request ≤
          nodeBudget * 3 ^ 2 * (natBitLength raw + 1) ^ 2 := by
    intro request hrequest
    rw [booleanNodeRequests, List.mem_map] at hrequest
    obtain ⟨node, hnodeMember, rfl⟩ := hrequest
    have hatom : node ∈ (rawBalancedTraversalTree raw).atoms := by
      rw [booleanNodeListAtoms] at hnodeMember
      exact hnodeMember
    have hwidth := natBitLength_le_of_mem_atoms hatom
    have hproject :
        booleanNodeCallFuel (nativeInputRequest inputLength node) =
          booleanNodeValidationFuel inputLength node := by
      rw [booleanNodeCallFuel, nativeInputRequest, Nat.unpair_pair]
    rw [hproject]
    exact (hnode inputLength node).trans (unitBudget_of_decoded nodeBudget 2 hwidth)
  rw [booleanNodeCallFuelFor]
  exact balancedCallFuel_polyBounded hcount hcallee hbound⟩

/-- **The preparation fork's ledger.**  Degree `3` over the node-list code's own
width: this is the first of the Boolean circuit validator's two remaining
charges, and it is now closed. -/
theorem exists_booleanCircuitPreparationFuel_polyBounded :
    ∃ budget : ℕ, ∀ inputLength raw : ℕ,
      PolyBounded
        (booleanCircuitPreparationFuel inputLength (booleanNodeListAtoms raw))
        (natBitLength raw) budget 3 := by
  obtain ⟨callBudget, hcall⟩ := exists_booleanNodeCallFuelFor_polyBounded
  exact ⟨_, fun inputLength raw => by
  have hatoms := polyBounded_booleanNodeListAtoms_length raw
  have hlength :
      PolyBounded (balancedLengthFuel (booleanNodeListAtoms raw))
        (natBitLength raw) (balancedLengthCoefficient 2) 3 :=
    (balancedLengthFuel_polyBounded' hatoms).degree_mono (by omega)
  have hframing :
      PolyBounded
        (nativeInputRequestTreeFuel (booleanNodeListAtoms raw))
        (natBitLength raw) (71 * 2 + 37) 3 :=
    (nativeInputRequestTreeFuel_polyBounded hatoms).degree_mono (by omega)
  have hbatch :
      PolyBounded
        (booleanNodeBatchFuel inputLength (booleanNodeListAtoms raw))
        (natBitLength raw)
        (programRegisterSpan (balancedCallProgram booleanNodeValidationProgram) +
          5 + (71 * 2 + 37) + callBudget) 3 := by
    rw [booleanNodeBatchFuel]
    exact linkFuel_polyBounded hframing (hcall inputLength raw)
  rw [booleanCircuitPreparationFuel]
  exact forkCallFuel_polyBounded hlength hbatch⟩

end NearCubicWires.ValidatorNodePreparationLedger
