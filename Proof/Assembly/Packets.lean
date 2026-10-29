import Proof.Assembly.LiveRows
import Proof.MachineModel.ClosureBinaryRequest
import Proof.MachineModel.ClosureCompactFamily
import Proof.MachineModel.ClosureBinaryPool
import Proof.CaseAnalysis.FinalModeNativeStageFields

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierTouching
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter NearCubicWires.SupplierRadix
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open scoped BigOperators

namespace FixedLivePackets
open P1Closure CloseoutRawRows
namespace Packets
noncomputable section

structure Row {q : Nat} (occ : List (SupportedNormalizedGate q)) (L : Nat) where
  polynomial : StructuralGF2Polynomial
  reference : StructuralGF2Polynomial
  degree : Nat
  select : BitInput (CyclicChoice.live occ L)ᶜ.card → Bool

structure Family (q L : Nat) where
  occurrences : List (SupportedNormalizedGate q)
  rows : List (Row occurrences L)

def seedList {q : Nat} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : Nat) :
    List (LiveRows.Seed occ I den) :=
  List.ofFn (canonicalWalkSampleFinEquiv
    (2 ^ toeplitzWalkSideBits (canonicalGradedRank occ.length (LiveRows.bound occ I))) den).symm

def coordinateDegree {q : Nat} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : Nat) : Nat :=
  canonicalWalkLength den * structuralListCoordinateRawDegree (canonicalGradedDepth (LiveRows.bound occ I))
    (executableGradedWindow (LiveRows.bound occ I)) gradedTerminalWindow

/-- Explicit lexicographic finite product; physical rows need no chosen Finset order. -/
def finiteProduct : (n : Nat) → (bounds : Fin n → Nat) →
    List ((i : Fin n) → Fin (bounds i))
  | 0, _ => [fun i => Fin.elim0 i]
  | n+1, bounds => (List.finRange (bounds 0)).flatMap (fun head =>
      (finiteProduct n (fun i => bounds i.succ)).map (fun tail => Fin.cons head tail))

def symOffsetList (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :=
  (finiteProduct r.circuits.length (fun i => (r.circuits.get i).bottomCount+1)).map
    (fun offset i => (offset i).val)

def thrSelectionList (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) : List (ThresholdRows.Selection a r) :=
  finiteProduct r.circuits.length (fun i => (ThresholdRows.children a (r.circuits.get i)).length)

def symFamily (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat) : Family r.q L :=
  let occ := symmetricFourfoldOccurrences r
  let I := CyclicChoice.live occ L
  let den := symmetricListDenominator r target
  ⟨occ, (seedList occ I den).flatMap (fun e =>
    (symOffsetList r).map (fun offset =>
      { polynomial := LiveRows.symPolynomial true r I den e offset
        reference := LiveRows.symPolynomial false r I den e offset
        degree := r.circuits.length * coordinateDegree occ I den
        select := fun z => decide (LiveRows.symOffsets r I
          (C10SupplierRowInput.joinInput I (fun _ => false) z) = offset) }))⟩

def thrFamily (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat) : Family r.q L :=
  let occ := thresholdFourfoldOccurrences r
  let I := CyclicChoice.live occ L
  let den := CloseoutFinalC10ThresholdRows.listDenominator a r target
  let cutoff := CloseoutFinalC10ThresholdRows.primeCutoff a r target
  ⟨occ, (thrSelectionList a r).flatMap (fun sel =>
    (List.ofFn (primeIndexFinEquiv cutoff).symm).flatMap (fun p =>
      (seedList occ I den).flatMap (fun e =>
        (List.finRange p.val).map (fun offset =>
          { polynomial := LiveRows.thrPolynomial true a r I den sel p.val offset.val e
            reference := LiveRows.thrPolynomial false a r I den sel p.val offset.val e
            degree := modulusDigitCount p.val * coordinateDegree occ I den
            select := fun z => decide (LiveRows.modularOffset occ I
              (C10SupplierRowInput.joinInput I (fun _ => false) z)
              (ThresholdRows.equation a r sel) p.val = offset.val) }))))⟩

def request (sources : EightSources) (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) : Family q L :=
  if mode then symFamily ⟨q, atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩ L target
  else thrFamily (decompositionOf sources) ⟨q, atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩ L target

abbrev live {q L : Nat} (F : Family q L) := CyclicChoice.live F.occurrences L
abbrev residual {q L : Nat} (_F : Family q L) := q - normalizedLiveCount q L

/-- Both clauses are used: card in the actual pool arity; touch in its width policy. -/
structure Geometry {q L : Nat} (F : Family q L) : Prop where
  card : (live F).card = normalizedLiveCount q L
  touch : q * LiveRows.bound F.occurrences (live F) ≤
    normalizedLiveCount q L * supportIncidenceMass (occurrenceSupport F.occurrences)
  arity : (residual F + 1)/2 + residual F/2 = (live F)ᶜ.card

theorem geometry (law : CyclicChoice.Laws) {q L : Nat} (F : Family q L) : Geometry F := by
  have h := law (occurrenceSupport F.occurrences) (normalizedLiveCount_le q L)
  have hc : (live F)ᶜ.card = q - normalizedLiveCount q L := by
    rw [Finset.card_compl, Fintype.card_fin]
    exact congrArg (fun x => q - x) h.1
  refine ⟨h.1,h.2,?_⟩
  rw [hc]
  dsimp only [residual]
  omega

def pool {q L : Nat} (a : DecompositionAlgorithm) (F : Family q L) (g : Geometry F) :=
  BinaryPool.pool a (live F) F.occurrences (residual F) g.arity

def lowered {q L : Nat} (a : DecompositionAlgorithm) (F : Family q L) (r : Row F.occurrences L) :
    StructuralGF2Polynomial :=
  Normalized.structuralGF2Substitute
    (fun code => Ring.norm (CloseoutRowsUniversal.atomOfCode a (live F) F.occurrences code)) r.polynomial

def one {q L : Nat} (a : DecompositionAlgorithm) (F : Family q L) (g : Geometry F)
    (r : Row F.occurrences L) (yi : Fin (C10SupplierRowInput.liveList (live F)).length) :
    List (List (Fin (pool a F g).length)) :=
  Ring.norm ((lowered a F r).map (List.map (fun code =>
    Fin.cast (BinaryPool.pool_length a (live F) F.occurrences (residual F) g.arity).symm
      (C10SupplierRowInput.poolIndex a (live F) F.occurrences (residual F) g.arity yi code))))

def packets {q L : Nat} (a : DecompositionAlgorithm) (F : Family q L) (g : Geometry F)
    (r : Row F.occurrences L) : List (List (List (Fin (pool a F g).length))) :=
  List.ofFn (one a F g r)

/-- Each packet uses one live-assignment block, plus the shared false sentinel.
The full pooled alphabet would incorrectly charge K times the degree. -/
def alphabet {q L : Nat} (a : DecompositionAlgorithm) (F : Family q L) : Nat :=
  (C10SupplierRowInput.childList a (live F) F.occurrences).length + 2

def PacketFacts {q L : Nat} (a : DecompositionAlgorithm) (F : Family q L) (g : Geometry F)
    (r : Row F.occurrences L) : Prop :=
  (∀ yi, Ring.Normal (one a F g r yi) ∧ Ring.Degree r.degree (one a F g r yi) ∧
    (one a F g r yi).length ≤ (alphabet a F)^r.degree) ∧
  (∀ yi (x : BitInput ((residual F+1)/2+residual F/2)),
    Ring.Eval (fun i => ((pool a F g).get i).eval x) (one a F g r yi) =
      evaluateStructuralGF2
        (LiveRows.residualAssignment F.occurrences (live F)
          (C10SupplierRowInput.joinInput (live F) (BinaryPool.assignmentAt (live F) yi.val)
            (C10SupplierRowInput.residualPoint (live F) (residual F) g.arity x))) r.reference)

/-- The exact normalization, lowering and finite-pool packet theorem consumed below. -/
def CompilerLaws : Prop :=
  ∀ (sources : EightSources) (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp))
    (g : Geometry (request sources L target mode atoms))
    (r : Row (request sources L target mode atoms).occurrences L),
    r ∈ (request sources L target mode atoms).rows →
      PacketFacts (decompositionOf sources) (request sources L target mode atoms) g r

end
end Packets
end FixedLivePackets
