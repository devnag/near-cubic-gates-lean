import Proof.CaseAnalysis.WitnessBoundedFamilyLayout
import Proof.CaseAnalysis.WitnessFamilyDecoded

/-! The whole bounded flag uses the original header and exactly one
source-dependent typed family. Malformed or oversized guesses cannot pass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
open SourceInterfaces RepairSource RepairRepresentation CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem passed_exact (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies symDen thrDen : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad:k+3≤Cpad) :
    passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad=true ↔
      16*bits.length≤n ∧ CompetitorWitnessTriple.headerValid bits ∧
        ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) (BoundedFields.oracle bits)=true ∧
          ∃ oracle,decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
            (value (BoundedFields.oracle bits))=some oracle ∧
            ColdFamily.decodedFamily source a k CH Cpad D copies (exponent (BoundedFields.symmetric bits))
              (denominator (BoundedFields.symmetric bits) symDen thrDen) delta code (BoundedFields.symmetric bits)
              x (BoundedFields.family bits) hpad oracle := by
  classical
  rw [passed,Bool.and_eq_true,headerValid,decide_eq_true_eq,List.length_ofFn]
  rw [ColdFamily.passed_exact]
  exact and_assoc

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
