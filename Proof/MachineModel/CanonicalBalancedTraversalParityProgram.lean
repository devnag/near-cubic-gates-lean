import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalTaggedParityProgram

namespace NearCubicWires.CanonicalBalancedTraversalParityProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTaggedParityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## §1 Parity of a bit list is its sum modulo two

`taggedParity` is the semantic output the substrate's run theorems deliver, so
the repair has to reproduce it exactly.  For a list whose entries are Boolean
codes it is the residue of the plain natural sum, which is what a balanced
summation traversal already computes. -/

theorem sum_le_length_of_le_one {values : List ℕ}
    (hvalues : ∀ value ∈ values, value ≤ 1) :
    values.sum ≤ values.length := by
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      have hvalue : value ≤ 1 := hvalues value (by simp)
      have hrest :=
        inductionHypothesis fun candidate hcandidate =>
          hvalues candidate (List.mem_cons_of_mem _ hcandidate)
      simp only [List.sum_cons, List.length_cons]
      omega

private theorem parityStep_eq_mod_two
    {value accumulator : ℕ} (hvalue : value ≤ 1) (haccumulator : accumulator ≤ 1) :
    parityStep value accumulator = (accumulator + value) % 2 := by
  unfold parityStep
  split
  · omega
  · split
    · omega
    · omega

theorem taggedParityFrom_eq_mod_two
    (values : List ℕ) (accumulator : ℕ) (haccumulator : accumulator ≤ 1)
    (hvalues : ∀ value ∈ values, value ≤ 1) :
    taggedParityFrom values accumulator = (accumulator + values.sum) % 2 := by
  induction values generalizing accumulator with
  | nil =>
      simp only [taggedParityFrom, List.sum_nil]
      omega
  | cons value values inductionHypothesis =>
      have hvalue : value ≤ 1 := hvalues value (by simp)
      have hrest : ∀ candidate ∈ values, candidate ≤ 1 :=
        fun candidate hcandidate =>
          hvalues candidate (List.mem_cons_of_mem _ hcandidate)
      have hstep := parityStep_eq_mod_two hvalue haccumulator
      have hstepLe : parityStep value accumulator ≤ 1 := by omega
      rw [taggedParityFrom,
        inductionHypothesis (parityStep value accumulator) hstepLe hrest,
        hstep, List.sum_cons]
      omega

/-- **The repair's semantic key.**  On Boolean codes the tagged fold and the
balanced sum agree modulo two. -/
theorem taggedParity_eq_sum_mod_two
    (values : List ℕ) (hvalues : ∀ value ∈ values, value ≤ 1) :
    taggedParity values = values.sum % 2 := by
  rw [taggedParity, taggedParityFrom_eq_mod_two values 0 (by omega) hvalues]
  omega

/-! ## §2 The low bit of a natural

Three instructions.  `testBit` is a total random-access digit extraction whose
result is always one bit, so its bounded write needs nothing beyond a positive
register width. -/

theorem bits_of_le_one
    {maximumBits value : ℕ} (hvalue : value ≤ 1) (hpositive : 1 ≤ maximumBits) :
    natBitLength value ≤ maximumBits := by
  have hmono : natBitLength value ≤ natBitLength 1 := natBitLength_mono hvalue
  have hone : natBitLength 1 = 1 := by norm_num [natBitLength]
  omega

/-- Register ABI: `r0` is the input word and then the output bit; `r2` is the
digit index, fixed at zero. -/
def natLowBitProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .testBit 0 2 0 2
  , .halt 0
  ]

@[simp] theorem natLowBitProgram_oracleFree : OracleFree natLowBitProgram := by
  rfl

def natLowBitFuel : ℕ := 3

theorem run_natLowBitProgram
    (inputLength maximumBits code : ℕ) (hpositive : 1 ≤ maximumBits) :
    runNPOracleProgram natLowBitProgram maximumBits natLowBitFuel
        (initialNPOracleState inputLength code) =
      some (code % 2) := by
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    bits_of_le_one (by omega) hpositive
  have hbitBits : natBitLength (code % 2) ≤ maximumBits :=
    bits_of_le_one (by omega) hpositive
  rw [show natLowBitFuel = 2 + 1 by rfl]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_testBit_instruction (value := code % 2) (by rfl) rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump, initialNPOracleState]
      norm_num
      rcases Nat.mod_two_eq_zero_or_one code with hcode | hcode <;>
        simp [hcode])
    hbitBits]
  exact run_halt_instruction (fuel := 0) (value := code % 2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbitBits

def balancedTraversalParityProgram : NPOracleProgram :=
  linkPrograms balancedNatSumProgram natLowBitProgram

@[simp] theorem balancedTraversalParityProgram_oracleFree :
    OracleFree balancedTraversalParityProgram :=
  oracleFree_linkPrograms balancedNatSumProgram_oracleFree
    natLowBitProgram_oracleFree

def balancedTraversalParityFuel (values : List ℕ) : ℕ :=
  linkFuel natLowBitProgram (balancedNatSumFuel values) natLowBitFuel

/-- **The repaired width ledger.**  Three entries, none of them a tagged code:
the caller's input length, the summand traversal, and the published total. -/
def balancedTraversalParityBits (inputLength : ℕ) (values : List ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) (balancedNatSumBits inputLength values)

theorem run_balancedTraversalParityProgram
    (inputLength : ℕ) (values : List ℕ) :
    runNPOracleProgram balancedTraversalParityProgram
        (balancedTraversalParityBits inputLength values)
        (balancedTraversalParityFuel values)
        (initialNPOracleState inputLength (encodeBalancedList values)) =
      some (values.sum % 2) := by
  have hpositive : 1 ≤ balancedTraversalParityBits inputLength values :=
    Nat.le_max_left _ _
  have hlength :
      natBitLength inputLength ≤ balancedTraversalParityBits inputLength values :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsumBits :
      balancedNatSumBits inputLength values ≤
        balancedTraversalParityBits inputLength values :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlength
    (run_bits_mono (run_balancedNatSumProgram inputLength values) hsumBits)
    (run_natLowBitProgram inputLength _ values.sum hpositive)

/-- **The repair, at the substrate's own contract.**  Same input code, same
output, no tagged list anywhere. -/
theorem run_balancedTraversalParityProgram_taggedParity
    (inputLength : ℕ) (values : List ℕ)
    (hvalues : ∀ value ∈ values, value ≤ 1) :
    runNPOracleProgram balancedTraversalParityProgram
        (balancedTraversalParityBits inputLength values)
        (balancedTraversalParityFuel values)
        (initialNPOracleState inputLength (encodeBalancedList values)) =
      some (taggedParity values) := by
  rw [taggedParity_eq_sum_mod_two values hvalues]
  exact run_balancedTraversalParityProgram inputLength values

end NearCubicWires.CanonicalBalancedTraversalParityProgram
