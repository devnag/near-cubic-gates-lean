import Proof.SourceAssembly.SourceRequestConsumer

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open FixedLivePackets PacketProduction MaskedFamilySource
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

section segments
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- The bare native circuit word of one factor, in the branch mode. -/
def circuitWord (mode : Bool) (α : C10TotalDecode.Atom pcpp) : List Bool :=
  if mode then symWord (C10NaturalModeAtoms.nativeSymmetricAtom α)
  else thrWord (C10NaturalModeAtoms.nativeThresholdAtom α)

/-- One factor's native segment: its circuit word, framed. -/
def natSeg (mode : Bool) (α : C10TotalDecode.Atom pcpp) : List Bool :=
  RepairOrdinary.frame (circuitWord mode α)

/-- One occurrence's support bitmap, framed (`Request.supportWord`'s summand). -/
def bitmapFrame (g : SupportedNormalizedGate q) : List Bool :=
  RepairOrdinary.frame (List.ofFn (fun i : Fin q => decide (i ∈ g.support)))

/-- One factor's bottom occurrences, in the order the request lists them. -/
def factorOccurrences (mode : Bool) (α : C10TotalDecode.Atom pcpp) : List (SupportedNormalizedGate q) :=
  if mode then symmetricCircuitOccurrences (C10NaturalModeAtoms.nativeSymmetricAtom α)
  else thresholdCircuitOccurrences (C10NaturalModeAtoms.nativeThresholdAtom α)

/-- One factor's support segment. -/
def supSeg (mode : Bool) (α : C10TotalDecode.Atom pcpp) : List Bool :=
  (factorOccurrences mode α).flatMap bitmapFrame

/-- One THR factor's TOP content: retained top arity and decomposition children. -/
def topContent (a : DecompositionAlgorithm) (α : C10TotalDecode.Atom pcpp) : List Bool :=
  natWord (C10NaturalModeAtoms.nativeThresholdAtom α).top.support.card ++
    exactListWord (ThresholdRows.children a (C10NaturalModeAtoms.nativeThresholdAtom α))

/-- One factor's TOP segment (`[]` in the SYM branch). -/
def topSeg (a : DecompositionAlgorithm) (mode : Bool) (α : C10TotalDecode.Atom pcpp) : List Bool :=
  if mode then [] else RepairOrdinary.frame (topContent a α)

/-- The native header: mode tag, `q`, `L`, `target`, factor count. -/
def header (mode : Bool) (q L target k : Nat) : List Bool :=
  natWord (if mode then 0 else 1) ++ natWord q ++ natWord L ++ natWord target ++ natWord k

end segments

section decompose
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

theorem native_eq (L target : Nat) (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) :
    (monomialRequest L target mode atoms four).nativeWord
      = header mode q L target atoms.length ++ atoms.flatMap (natSeg mode) := by
  cases mode
  · show natWord 1 ++ natWord q ++ natWord L ++ natWord target
        ++ natWord (atoms.map C10NaturalModeAtoms.nativeThresholdAtom).length
        ++ (atoms.map C10NaturalModeAtoms.nativeThresholdAtom).flatMap
          (fun c => RepairOrdinary.frame (thrWord c)) = _
    rw [List.length_map, List.flatMap_map]
    rfl
  · show natWord 0 ++ natWord q ++ natWord L ++ natWord target
        ++ natWord (atoms.map C10NaturalModeAtoms.nativeSymmetricAtom).length
        ++ (atoms.map C10NaturalModeAtoms.nativeSymmetricAtom).flatMap
          (fun c => RepairOrdinary.frame (symWord c)) = _
    rw [List.length_map, List.flatMap_map]
    rfl

theorem support_eq (a : DecompositionAlgorithm) (L target : Nat) (mode : Bool)
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    (monomialRequest L target mode atoms four).supportWord a = atoms.flatMap (supSeg mode) := by
  cases mode
  · show ((atoms.map C10NaturalModeAtoms.nativeThresholdAtom).flatMap
        thresholdCircuitOccurrences).flatMap bitmapFrame = _
    rw [List.flatMap_map, List.flatMap_assoc]
    rfl
  · show ((atoms.map C10NaturalModeAtoms.nativeSymmetricAtom).flatMap
        symmetricCircuitOccurrences).flatMap bitmapFrame = _
    rw [List.flatMap_map, List.flatMap_assoc]
    rfl

theorem top_eq (a : DecompositionAlgorithm) (L target : Nat) (mode : Bool)
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    (monomialRequest L target mode atoms four).topWord a = atoms.flatMap (topSeg a mode) := by
  cases mode
  · show (atoms.map C10NaturalModeAtoms.nativeThresholdAtom).flatMap
        (fun c => RepairOrdinary.frame (natWord c.top.support.card
          ++ exactListWord (ThresholdRows.children a c))) = _
    rw [List.flatMap_map]
    rfl
  · show [] = atoms.flatMap (topSeg a true)
    clear four
    induction atoms with
    | nil => rfl
    | cons x xs ih => rw [List.flatMap_cons, ← ih]; rfl

theorem occurrences_length (a : DecompositionAlgorithm) (L target : Nat) (mode : Bool)
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    ((monomialRequest L target mode atoms four).family a).occurrences.length
      = (atoms.map (fun α => (factorOccurrences mode α).length)).sum := by
  cases mode
  · show ((atoms.map C10NaturalModeAtoms.nativeThresholdAtom).flatMap
        thresholdCircuitOccurrences).length = _
    rw [List.flatMap_map, List.length_flatMap]
    rfl
  · show ((atoms.map C10NaturalModeAtoms.nativeSymmetricAtom).flatMap
        symmetricCircuitOccurrences).length = _
    rw [List.flatMap_map, List.length_flatMap]
    rfl

end decompose

/-! ## Four factor slots, absent factors contributing nothing -/

/-- Factor slot `i` of a `≤ 4`-factor monomial: the factor's segment, or `[]` when absent. -/
def slotSeg {α : Type} (f : α → List Bool) (atoms : List α) (i : Nat) : List Bool :=
  (atoms[i]?.map f).getD []

theorem slots_flatMap {α : Type} (f : α → List Bool) (atoms : List α) (four : atoms.length ≤ 4) :
    slotSeg f atoms 0 ++ slotSeg f atoms 1 ++ slotSeg f atoms 2 ++ slotSeg f atoms 3
      = atoms.flatMap f := by
  match atoms, four with
  | [], _ => rfl
  | [x0], _ => simp [slotSeg]
  | [x0, x1], _ => simp [slotSeg]
  | [x0, x1, x2], _ => simp [slotSeg]
  | [x0, x1, x2, x3], _ => simp [slotSeg]
  | _ :: _ :: _ :: _ :: _ :: _, h => simp at h; omega

end
end NearCubicWires.SourceRequest
