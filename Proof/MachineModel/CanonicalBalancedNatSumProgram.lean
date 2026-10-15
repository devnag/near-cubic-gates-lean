import Proof.Circuits.CanonicalBalancedTraversal
import Proof.Foundations.VerifiedLinker

namespace NearCubicWires.CanonicalBalancedNatSumProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

def balancedNatSumProgram : NPOracleProgram :=
  balancedTraversalController 34 35 ++
    [ .add 9 3 9 balancedTraversalLeafReturnPc
    , .halt 9
    ]

theorem balancedNatSumProgram_controllerAt :
    BalancedTraversalControllerAt balancedNatSumProgram 34 35 := by
  intro pc instruction hlookup
  have hpc : pc < (balancedTraversalController 34 35).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [balancedNatSumProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

@[simp] theorem balancedNatSumProgram_oracleFree :
    OracleFree balancedNatSumProgram := by
  rfl

def balancedNatSumFuel (values : List ℕ) : ℕ :=
  balancedTraversalStructuralSteps (balancedTraversalTree values) +
    values.length + 2

def balancedNatSumBits
    (inputLength : ℕ) (values : List ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (balancedTraversalRequiredBits (fun value => value)
        (balancedTraversalTree values) [])
      (natBitLength values.sum)

theorem run_balancedNatSumProgram
    (inputLength : ℕ) (values : List ℕ) :
    runNPOracleProgram balancedNatSumProgram
        (balancedNatSumBits inputLength values)
        (balancedNatSumFuel values)
        (initialNPOracleState inputLength
          (encodeBalancedList values)) =
      some values.sum := by
  let initial :=
    initialNPOracleState inputLength (encodeBalancedList values)
  have hrequired :
      balancedTraversalRequiredBits (fun value => value)
          (balancedTraversalTree values) [] ≤
        balancedNatSumBits inputLength values :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hfit :
      BalancedTraversalFits
        (balancedNatSumBits inputLength values) (fun value => value)
        (balancedTraversalTree values) [] :=
    (balancedTraversalRequiredBits_le_iff
      (balancedNatSumBits inputLength values) (fun value => value)
      (balancedTraversalTree values) []).mp hrequired
  have hsumBits :
      natBitLength values.sum ≤ balancedNatSumBits inputLength values :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  obtain
      ⟨finish, hruns, hpc, _hcurrent, _hstack, hsum,
        _hpersistent⟩ :=
    run_balancedTraversalNatSum values initial
      balancedNatSumProgram_controllerAt (by rfl) (by rfl)
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState]) hfit
      (by simpa [initial, initialNPOracleState] using hsumBits)
  have hhalt :
      runNPOracleProgram balancedNatSumProgram
          (balancedNatSumBits inputLength values) 1 finish =
        some values.sum :=
    run_halt_instruction (fuel := 0) (by rfl) hpc
      (by simpa [initial, initialNPOracleState] using hsum)
      hsumBits
  rw [show balancedNatSumFuel values =
      (balancedTraversalStructuralSteps (balancedTraversalTree values) +
        values.length + 1) + 1 by
    simp [balancedNatSumFuel]]
  rw [hruns]
  exact hhalt

/-! ## Composition boundary

Keep the producer abstract while proving the standard producer-to-sum link.
Concrete producers can be large generated controllers; specializing this opaque
theorem avoids normalizing their instruction layout in every downstream proof.
-/

def balancedNatSumAfterProgram (producer : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms producer balancedNatSumProgram

@[simp] theorem balancedNatSumAfterProgram_oracleFree
    (producer : NPOracleProgram) (hproducer : OracleFree producer) :
    OracleFree (balancedNatSumAfterProgram producer) := by
  exact oracleFree_linkPrograms hproducer balancedNatSumProgram_oracleFree

def balancedNatSumAfterBits
    (inputLength producerBits : ℕ) (values : List ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max producerBits (balancedNatSumBits inputLength values)

def balancedNatSumAfterFuel
    (producerFuel : ℕ) (values : List ℕ) : ℕ :=
  linkFuel balancedNatSumProgram producerFuel (balancedNatSumFuel values)

theorem run_balancedNatSumAfterProgram
    (producer : NPOracleProgram)
    (inputLength inputCode producerBits producerFuel : ℕ)
    (values : List ℕ)
    (hproducer :
      runNPOracleProgram producer producerBits producerFuel
          (initialNPOracleState inputLength inputCode) =
        some (encodeBalancedList values)) :
    runNPOracleProgram (balancedNatSumAfterProgram producer)
        (balancedNatSumAfterBits inputLength producerBits values)
        (balancedNatSumAfterFuel producerFuel values)
        (initialNPOracleState inputLength inputCode) =
      some values.sum := by
  let maximumBits :=
    balancedNatSumAfterBits inputLength producerBits values
  have hpositive : 1 ≤ maximumBits :=
    Nat.le_max_left _ _
  have hlength : natBitLength inputLength ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hproducerBits : producerBits ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hsumBits :
      balancedNatSumBits inputLength values ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hproducer' :=
    run_bits_mono hproducer hproducerBits
  have hsum :=
    run_bits_mono (run_balancedNatSumProgram inputLength values) hsumBits
  simpa only [maximumBits, balancedNatSumAfterProgram,
    balancedNatSumAfterFuel] using
      (run_linkPrograms hpositive hlength hproducer' hsum)

theorem balancedNatSumFuel_le_linear (values : List ℕ) :
    balancedNatSumFuel values ≤ 71 * values.length + 37 := by
  have hstructural :=
    balancedTraversalStructuralSteps_le_linear values
  unfold balancedNatSumFuel
  omega

end NearCubicWires.CanonicalBalancedNatSumProgram
