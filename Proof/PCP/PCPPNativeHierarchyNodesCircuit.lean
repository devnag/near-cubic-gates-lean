import Proof.PCP.PCPPNativeHierarchyNodesDock
import Proof.PCP.PCPPNativeCompactCircuit

/-! The exact source-selected circuit at the original hierarchy input.
The source parameter is fixed before the hierarchy exponent. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def pcp (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) :=
  source.output (HierarchyStreams.request k CH Cpad code (List.ofFn x))
def width (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) :=
  HierarchyStreams.R source k CH Cpad code (List.ofFn x)
def queries (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) :=
  HierarchyStreams.Q source k CH Cpad code (List.ofFn x)
theorem positive (k CH Cpad : ℕ) (code x : List Bool) (hpad : k+3≤Cpad) :
    1≤(HierarchyStreams.request k CH Cpad code x).1 := by
  have h:=(HierarchyPadding.linear_length k CH Cpad code x hpad).1
  change 1≤(HierarchyPadding.rawInput k CH Cpad code x).length
  omega
theorem width_fits (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (hpad : k+3≤Cpad) :
    (pcp source k CH Cpad code x).width≤width source k CH Cpad code x :=
  Dimensions.width_fits source _ (positive k CH Cpad code (List.ofFn x) hpad)
theorem queries_fit (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (hpad : k+3≤Cpad) :
    (pcp source k CH Cpad code x).queries≤queries source k CH Cpad code x :=
  Dimensions.queries_fit source _ (positive k CH Cpad code (List.ofFn x) hpad)
def circuit (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (hpad : k+3≤Cpad)
    (oracle : BooleanCircuit (width source k CH Cpad code x)) :=
  PCPPNativeCompactNodes.circuit (pcp source k CH Cpad code x) (width source k CH Cpad code x)
    (queries source k CH Cpad code x) (width_fits source k CH Cpad code x hpad)
    (queries_fit source k CH Cpad code x hpad) x oracle
def budget (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (bound : List Bool)
    (oracle : BooleanCircuit (width source k CH Cpad code x)) :=
  PCPPNativeHierarchy.budget source k CH Cpad code (List.ofFn x) bound (PCPPNative.descriptor oracle)+1+
    PCPPNativeCounterNodes.budget oracle (pcp source k CH Cpad code x) (queries source k CH Cpad code x)

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
