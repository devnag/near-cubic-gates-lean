import Proof.Wire_3_5.Shared.StarPartition
import Proof.Foundations.SupplierPipeline

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.CanonicalBinary

abbrev Carrier (n : ℕ) := List (NormalizedThresholdGate n)

namespace Carrier
variable {n : ℕ}

def atomResidual (g : NormalizedThresholdGate n) (c u v : BitInput n) : ℕ :=
  (residualPlus g.eval c u v).toNat + (residualMinus g.eval c u v).toNat

def population (X : Carrier n) (c u v : BitInput n) : ℕ :=
  (X.map fun g => atomResidual g c u v).sum

def residualBits (X : Carrier n) (c u v : BitInput n) : List Bool :=
  X.flatMap fun g => [residualPlus g.eval c u v, residualMinus g.eval c u v]

def WithinEnvelope (deg : ℕ) (X : Carrier n) : Prop :=
  X.length ≤ (n + 1) ^ deg ∧ ∀ g ∈ X, g.encodingBits ≤ (n + 1) ^ deg

/-- The canonical code of a carrier (the Theorem 2.5 list codecs): a balanced list of atom codes. -/
def code (X : Carrier n) : ℕ :=
  encodeBalancedList (X.map fun g => encodeTaggedList [encodeIntList (List.ofFn g.weight), encodeInt g.threshold])

end Carrier

def inputResidualBits (P : StarParams) (σ : P.Translation) (X : Carrier P.n) (x : BitInput P.n) : List Bool :=
  Carrier.residualBits X (P.center σ x) (P.errorVector P.leftBlock (P.leftErrors σ x))
    (P.errorVector P.rightBlock (P.rightErrors σ x))

def inputPopulation (P : StarParams) (σ : P.Translation) (X : Carrier P.n) (x : BitInput P.n) : ℕ :=
  Carrier.population X (P.center σ x) (P.errorVector P.leftBlock (P.leftErrors σ x))
    (P.errorVector P.rightBlock (P.rightErrors σ x))

/-- The charged gates of a `THR∘THR` circuit: the bottoms at retained top positions (the only bottoms its function
and its wire count see). -/
def thrGates {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) : Carrier n :=
  ((List.finRange C.bottomCount).filter fun i => decide (i ∈ C.top.support)).map fun i => (C.bottom i).gate

/-- The charged gates of a `SYM∘THR` circuit: every bottom. -/
def symGates {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) : Carrier n :=
  (List.finRange C.bottomCount).map fun i => (C.bottom i).gate

def GatesIn {n a : ℕ} (gates : Fin a → Carrier n) (named : List (Carrier n)) : Prop :=
  ∀ i, (gates i).Subperm named.flatten

end NearCubicWires.WireExponent3_5.Stars
