import Proof.Assembly.Production

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace RCFive.RowKeys
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch
open NearCubicWires NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairOrdinary
open FixedLivePackets PacketProduction
open scoped BigOperators
noncomputable section

structure SymKey (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat) where
  seed : LiveRows.Seed (symmetricFourfoldOccurrences r)
    (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)
  offset : Fin r.circuits.length → Nat

def symKeys (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat) :
    List (SymKey r L target) :=
  (Packets.seedList (symmetricFourfoldOccurrences r)
    (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)).flatMap
    (fun seed => (Packets.symOffsetList r).map (fun offset => ⟨seed,offset⟩))

def symRow (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat)
    (key : SymKey r L target) : Packets.Row (Packets.symFamily r L target).occurrences L :=
  let occ := symmetricFourfoldOccurrences r
  let I := CyclicChoice.live occ L
  let den := symmetricListDenominator r target
  { polynomial := LiveRows.symPolynomial true r I den key.seed key.offset
    reference := LiveRows.symPolynomial false r I den key.seed key.offset
    degree := r.circuits.length * Packets.coordinateDegree occ I den
    select := fun z => decide (LiveRows.symOffsets r I
      (C10SupplierRowInput.joinInput I (fun _ => false) z) = key.offset) }

theorem sym_rows_eq (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat) :
    (symKeys r L target).map (symRow r L target) = (Packets.symFamily r L target).rows := by
  simp [symKeys,symRow,Packets.symFamily,List.map_flatMap,List.map_map,Function.comp_def]

structure PrimeSeedKey (Selection Seed Prime : Type) (radix : Prime → Nat) where
  selection : Selection
  prime : Prime
  seed : Seed
  residue : Fin (radix prime)

abbrev ThrKey (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat) :=
  PrimeSeedKey (ThresholdRows.Selection a r)
    (LiveRows.Seed (thresholdFourfoldOccurrences r)
      (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r target))
    (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target)) Subtype.val

def thrKeys (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat) :
    List (ThrKey a r L target) :=
  (Packets.thrSelectionList a r).flatMap (fun selection =>
    (List.ofFn (primeIndexFinEquiv (CloseoutFinalC10ThresholdRows.primeCutoff a r target)).symm).flatMap
      (fun prime => (Packets.seedList (thresholdFourfoldOccurrences r)
        (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r target)).flatMap
          (fun seed => (List.finRange prime.val).map (fun residue => ⟨selection,prime,seed,residue⟩))))

def thrRow (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat)
    (key : ThrKey a r L target) : Packets.Row (Packets.thrFamily a r L target).occurrences L :=
  let occ := thresholdFourfoldOccurrences r
  let I := CyclicChoice.live occ L
  let den := CloseoutFinalC10ThresholdRows.listDenominator a r target
  { polynomial := LiveRows.thrPolynomial true a r I den key.selection key.prime.val key.residue.val key.seed
    reference := LiveRows.thrPolynomial false a r I den key.selection key.prime.val key.residue.val key.seed
    degree := modulusDigitCount key.prime.val * Packets.coordinateDegree occ I den
    select := fun z => decide (LiveRows.modularOffset occ I
      (C10SupplierRowInput.joinInput I (fun _ => false) z)
      (ThresholdRows.equation a r key.selection) key.prime.val = key.residue.val) }

theorem thr_rows_eq (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat) :
    (thrKeys a r L target).map (thrRow a r L target) = (Packets.thrFamily a r L target).rows := by
  simp [thrKeys,thrRow,Packets.thrFamily,List.map_flatMap,List.map_map,Function.comp_def]

theorem finiteProduct_length (n : Nat) (bounds : Fin n → Nat) :
    (Packets.finiteProduct n bounds).length = ∏ i, bounds i := by
  induction n with
  | zero => simp [Packets.finiteProduct]
  | succ n ih =>
    simp [Packets.finiteProduct,List.length_flatMap,ih,Fin.prod_univ_succ]

theorem sym_count (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat) :
    (symKeys r L target).length =
      (Packets.seedList (symmetricFourfoldOccurrences r)
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)).length *
      (∏ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount+1)) := by
  simp [symKeys,List.length_flatMap,Packets.symOffsetList,finiteProduct_length]

private theorem sum_const {α : Type} (xs : List α) (n : Nat) :
    (xs.map (fun _ => n)).sum = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Nat.add_mul,Nat.add_comm]

/-- The residue radix belongs to the current prime; it is inside the sum. -/
theorem thr_count (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat) :
    (thrKeys a r L target).length =
      (Packets.thrSelectionList a r).length *
      ((List.ofFn (primeIndexFinEquiv (CloseoutFinalC10ThresholdRows.primeCutoff a r target)).symm).map
        (fun prime => (Packets.seedList (thresholdFourfoldOccurrences r)
          (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
          (CloseoutFinalC10ThresholdRows.listDenominator a r target)).length * prime.val)).sum := by
  simp only [thrKeys,List.length_flatMap,List.length_map,List.length_finRange,
    sum_const]

theorem thr_empty (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat)
    (h : Packets.thrSelectionList a r = []) :
    thrKeys a r L target = [] ∧ (Packets.thrFamily a r L target).rows = [] := by
  simp [thrKeys,Packets.thrFamily,h]

/-- Packet enumeration consumes exactly the same ordered keys as selection. -/
theorem sym_raw_eq (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat)
    (g : Packets.Geometry (Packets.symFamily r L target)) :
    (symKeys r L target).flatMap (fun key =>
      ExternalRowFamily.rawWord a (Packets.symFamily r L target) g (symRow r L target key)) =
    (Packets.symFamily r L target).rows.flatMap
      (ExternalRowFamily.rawWord a (Packets.symFamily r L target) g) := by
  rw [← sym_rows_eq]
  simp only [List.flatMap_map]

theorem thr_raw_eq (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat)
    (g : Packets.Geometry (Packets.thrFamily a r L target)) :
    (thrKeys a r L target).flatMap (fun key =>
      ExternalRowFamily.rawWord a (Packets.thrFamily a r L target) g (thrRow a r L target key)) =
    (Packets.thrFamily a r L target).rows.flatMap
      (ExternalRowFamily.rawWord a (Packets.thrFamily a r L target) g) := by
  rw [← thr_rows_eq]
  simp only [List.flatMap_map]

end
end RCFive.RowKeys
