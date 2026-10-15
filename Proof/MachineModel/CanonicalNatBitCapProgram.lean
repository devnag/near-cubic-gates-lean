import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalNatCeilLogProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Executable natural-number bit-cap validation

This module validates the native natural-number predicate
`natBitLength value ≤ cap`.  A zero cap is rejected explicitly: this
repository's bit length assigns one bit even to zero, so no natural can satisfy
that cap.

## Why the stage is a ceiling logarithm and not a bit scan

The public semantics `natBitCapOutput` is stated through the low-bit
projection `bitInputPrefix cap value = value % 2 ^ cap`, because that is the
canonical statement of "the value survives its own cap".  Executing that
statement literally, however, costs a scan whose charge is
`Θ(min (value, 2 ^ cap))`: the projection program walks the selected bit
positions one at a time.  That budget is affordable inside an exponential-time
caller, but the recovery-witness validator is charged against a *polynomial*
envelope, and the bit cap sits on that critical path.

The executable stage therefore evaluates the equivalent inequality

`natBitLength value ≤ cap  ↔  Nat.clog 2 (value + 1) ≤ cap`  (for `cap ≠ 0`),

using the fixed base-two ceiling logarithm of `CanonicalNatCeilLogProgram`,
whose charge is linear in the *answer*, and the fixed native comparator of
`CanonicalBinaryArithmeticProgram`, whose charge is linear in the operand
*widths*.  A zero cap is routed to the argument `2`, whose ceiling logarithm is
one, so the comparison fails closed through the same branch-free pipeline.

The public surface — `natBitCapInput`, `natBitCapOutput`, `natBitCapProgram`,
`natBitCapFuel`, `natBitCapBits`, `run_natBitCapProgram`,
`natBitCapProgram_oracleFree` and `natBitCapOutput_ne_zero_iff` — is unchanged;
only the internal stage and its charge changed.  `natBitCapFuel_le` records the
resulting linear budget.
-/

namespace NearCubicWires.CanonicalNatBitCapProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatCeilLogProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-- Public ABI: `pair(cap, value)`. -/
def natBitCapInput (cap value : ℕ) : ℕ :=
  Nat.pair cap value

/-- The sole public semantic output. -/
def natBitCapOutput (cap value : ℕ) : ℕ :=
  if cap = 0 then
    0
  else
    nativeNatEqOutput (bitInputPrefix cap value) value

/-- The argument handed to the fixed ceiling-logarithm stage.  A zero cap takes
the fixed argument `2`, whose ceiling logarithm is one, so the downstream
comparison rejects.  This keeps the production program branch-free after
preparation while making the impossible zero-cap case fail closed. -/
private def natBitCapCeilLogArgument (cap value : ℕ) : ℕ :=
  if cap = 0 then 2 else value + 1

private def natBitCapCeilLogValue (cap value : ℕ) : ℕ :=
  Nat.clog 2 (natBitCapCeilLogArgument cap value)

private def natBitCapPreparedInput (cap value : ℕ) : ℕ :=
  Nat.pair (natBitCapCeilLogArgument cap value) cap

private def natBitCapCompareInput (cap value : ℕ) : ℕ :=
  nativeNatLeInput (natBitCapCeilLogValue cap value) cap

/-! ## Public input to ceiling-logarithm-call ABI -/

private def natBitCapPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 5 2
  , .unpairRight 0 3 3
  , .increment 3 4
  , .pair 3 2 0 8
  , .set 3 1 6
  , .increment 3 7
  , .pair 3 2 0 8
  , .halt 0
  ]

@[simp] private theorem natBitCapPrepareProgram_oracleFree :
    OracleFree natBitCapPrepareProgram := by
  rfl

private def natBitCapPrepareBits (cap value : ℕ) : ℕ :=
  max 1 <|
    max (natBitLength (natBitCapInput cap value))
      (natBitLength (natBitCapPreparedInput cap value))

private theorem run_natBitCapPrepareProgram
    (inputLength cap value : ℕ) :
    runNPOracleProgram natBitCapPrepareProgram
        (natBitCapPrepareBits cap value) 6
        (initialNPOracleState inputLength (natBitCapInput cap value)) =
      some (natBitCapPreparedInput cap value) := by
  let maximumBits := natBitCapPrepareBits cap value
  have hinput :
      natBitLength (natBitCapInput cap value) ≤ maximumBits := by
    simp [maximumBits, natBitCapPrepareBits]
  have houtput :
      natBitLength (natBitCapPreparedInput cap value) ≤ maximumBits := by
    simp [maximumBits, natBitCapPrepareBits]
  have hcap : natBitLength cap ≤ maximumBits := by
    exact (natBitLength_mono (Nat.left_le_pair cap value)).trans hinput
  have hvalue : natBitLength value ≤ maximumBits := by
    exact (natBitLength_mono (Nat.right_le_pair cap value)).trans hinput
  have hargument :
      natBitLength (natBitCapCeilLogArgument cap value) ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans houtput
    exact Nat.left_le_pair (natBitCapCeilLogArgument cap value) cap
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := natBitCapPrepareProgram)
    (maximumBits := maximumBits) (fuel := 5)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := cap) (by rfl) (by rfl)
    (by simp [initialNPOracleState, natBitCapInput]) hcap]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_branchZero_instruction
    (program := natBitCapPrepareProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 1) (register := 2) (zeroTarget := 5) (nonzeroTarget := 2)
    (by rfl) (by rfl)]
  rw [show
    (((initialNPOracleState inputLength (natBitCapInput cap value)).write
      2 cap).jump 1).registers 2 = cap by
        simp [NPOracleState.write, NPOracleState.jump]]
  by_cases hcapZero : cap = 0
  · rw [if_pos hcapZero]
    have hone : natBitLength 1 ≤ maximumBits := by
      refine (natBitLength_mono ?_).trans hargument
      simp [natBitCapCeilLogArgument, hcapZero]
    have htwo : natBitLength 2 ≤ maximumBits := by
      refine le_trans (le_of_eq ?_) hargument
      congr 1
      simp [natBitCapCeilLogArgument, hcapZero]
    have hprepared :
        natBitCapPreparedInput cap value = Nat.pair 2 cap := by
      simp [natBitCapPreparedInput, natBitCapCeilLogArgument, hcapZero]
    rw [show (4 : ℕ) = 3 + 1 by omega]
    rw [run_set_instruction
      (program := natBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 3)
      (pc := 5) (register := 3) (value := 1) (next := 6)
      (by rfl) (by rfl) hone]
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_increment_instruction
      (program := natBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 2)
      (pc := 6) (register := 3) (next := 7) (value := 2)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_pair_instruction
      (program := natBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (pc := 7) (left := 3) (right := 2) (destination := 0)
      (next := 8) (value := Nat.pair 2 cap)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump])
      (hprepared ▸ houtput)]
    rw [hprepared]
    exact run_halt_instruction
      (program := natBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 0)
      (pc := 8) (outputRegister := 0) (value := Nat.pair 2 cap)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump])
      (hprepared ▸ houtput)
  · rw [if_neg hcapZero]
    have hsuccessor : natBitLength (value + 1) ≤ maximumBits := by
      refine le_trans (le_of_eq ?_) hargument
      congr 1
      simp [natBitCapCeilLogArgument, hcapZero]
    have hprepared :
        natBitCapPreparedInput cap value = Nat.pair (value + 1) cap := by
      simp [natBitCapPreparedInput, natBitCapCeilLogArgument, hcapZero]
    rw [show (4 : ℕ) = 3 + 1 by omega]
    rw [run_unpairRight_instruction
      (program := natBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 3)
      (pc := 2) (source := 0) (destination := 3) (next := 3)
      (value := value) (by rfl) (by rfl)
      (by simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, natBitCapInput]) hvalue]
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_increment_instruction
      (program := natBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 2)
      (pc := 3) (register := 3) (next := 4) (value := value + 1)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump]) hsuccessor]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_pair_instruction
      (program := natBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 1)
      (pc := 4) (left := 3) (right := 2) (destination := 0)
      (next := 8) (value := Nat.pair (value + 1) cap)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump])
      (hprepared ▸ houtput)]
    rw [hprepared]
    exact run_halt_instruction
      (program := natBitCapPrepareProgram)
      (maximumBits := maximumBits) (fuel := 0)
      (pc := 8) (outputRegister := 0)
      (value := Nat.pair (value + 1) cap)
      (by rfl) (by rfl)
      (by simp [NPOracleState.write, NPOracleState.jump])
      (hprepared ▸ houtput)

/-! ## Linked total validator -/

private def natBitCapCeilLogStageProgram : NPOracleProgram :=
  preserveRightProgram binaryNatCeilLogProgram

private def natBitCapCeilLogStageFuel (cap value : ℕ) : ℕ :=
  preserveRightFuel <|
    binaryNatCeilLogFuel (natBitCapCeilLogArgument cap value)

private def natBitCapCeilLogStageBits (cap value : ℕ) : ℕ :=
  preserveRightBits
    (binaryNatCeilLogBits (natBitCapCeilLogArgument cap value))
    (natBitCapCeilLogArgument cap value)
    cap
    (natBitCapCeilLogValue cap value)

private theorem run_natBitCapCeilLogStageProgram
    (inputLength cap value : ℕ) :
    runNPOracleProgram natBitCapCeilLogStageProgram
        (natBitCapCeilLogStageBits cap value)
        (natBitCapCeilLogStageFuel cap value)
        (initialNPOracleState inputLength
          (natBitCapPreparedInput cap value)) =
      some (natBitCapCompareInput cap value) := by
  exact run_preserveRightProgram binaryNatCeilLogProgram inputLength
    (binaryNatCeilLogBits (natBitCapCeilLogArgument cap value))
    (binaryNatCeilLogFuel (natBitCapCeilLogArgument cap value))
    (natBitCapCeilLogArgument cap value) cap
    (natBitCapCeilLogValue cap value)
    (run_binaryNatCeilLogProgram inputLength
      (natBitCapCeilLogArgument cap value)
      (binaryNatCeilLogBits (natBitCapCeilLogArgument cap value))
      (le_refl _))

/-! ## The exact semantic boundary shared by both stage designs -/

private theorem bitInputPrefix_eq_self_iff_natBitLength_le
    (cap value : ℕ) (hcap : 0 < cap) :
    bitInputPrefix cap value = value ↔ natBitLength value ≤ cap := by
  constructor
  · intro hequal
    have hlt :
        bitInputPrefix cap value < 2 ^ cap := by
      exact Nat.mod_lt value (pow_pos (by omega : 0 < 2) cap)
    rw [hequal] at hlt
    have hlog :
        Nat.log 2 value < cap :=
      Nat.log_lt_of_lt_pow' (by omega) hlt
    unfold natBitLength
    omega
  · intro hlength
    have hlog : Nat.log 2 value < cap := by
      unfold natBitLength at hlength
      omega
    have hlt : value < 2 ^ cap :=
      Nat.lt_pow_of_log_lt (by omega) hlog
    exact Nat.mod_eq_of_lt hlt

/-- The executable inequality and the declarative bit cap agree exactly. -/
private theorem natBitCapCeilLogValue_le_iff (cap value : ℕ) :
    natBitCapCeilLogValue cap value ≤ cap ↔ natBitLength value ≤ cap := by
  by_cases hcap : cap = 0
  · have hclog : ¬ (Nat.clog 2 2 ≤ 0) := by
      rw [Nat.clog_le_iff_le_pow (by norm_num : (1 : ℕ) < 2)]
      norm_num
    have hleft : ¬ (natBitCapCeilLogValue cap value ≤ cap) := by
      simpa [natBitCapCeilLogValue, natBitCapCeilLogArgument, hcap] using
        hclog
    have hright : ¬ (natBitLength value ≤ cap) := by
      rw [hcap]
      unfold natBitLength
      omega
    simp [hleft, hright]
  · have hargument :
        natBitCapCeilLogArgument cap value = value + 1 := by
      simp [natBitCapCeilLogArgument, hcap]
    constructor
    · intro hle
      have hclog : Nat.clog 2 (value + 1) ≤ cap := by
        simpa [natBitCapCeilLogValue, hargument] using hle
      have hpow : value + 1 ≤ 2 ^ cap :=
        (Nat.clog_le_iff_le_pow (by norm_num : (1 : ℕ) < 2)).mp hclog
      have hlt : value < 2 ^ cap := by omega
      have hlog : Nat.log 2 value < cap :=
        Nat.log_lt_of_lt_pow' hcap hlt
      unfold natBitLength
      omega
    · intro hle
      have hlog : Nat.log 2 value < cap := by
        unfold natBitLength at hle
        omega
      have hlt : value < 2 ^ cap :=
        Nat.lt_pow_of_log_lt (by norm_num) hlog
      have hpow : value + 1 ≤ 2 ^ cap := by omega
      have hclog : Nat.clog 2 (value + 1) ≤ cap :=
        Nat.clog_le_of_le_pow hpow
      simpa [natBitCapCeilLogValue, hargument] using hclog

private theorem natBitCapExecutableOutput_eq (cap value : ℕ) :
    nativeNatLeOutput (natBitCapCeilLogValue cap value) cap =
      natBitCapOutput cap value := by
  have hiff := natBitCapCeilLogValue_le_iff cap value
  rw [nativeNatLeOutput_eq]
  by_cases hcap : cap = 0
  · subst hcap
    have hlength : ¬ (natBitLength value ≤ 0) := by
      unfold natBitLength
      omega
    have hleft : ¬ (natBitCapCeilLogValue 0 value ≤ 0) := by
      intro hcontra
      exact hlength (hiff.mp hcontra)
    simp [natBitCapOutput, hleft]
  · have hprefix :
        bitInputPrefix cap value = value ↔ natBitLength value ≤ cap :=
      bitInputPrefix_eq_self_iff_natBitLength_le cap value
        (Nat.pos_of_ne_zero hcap)
    by_cases hlength : natBitLength value ≤ cap
    · have hleft : natBitCapCeilLogValue cap value ≤ cap := hiff.mpr hlength
      have hequal : bitInputPrefix cap value = value := hprefix.mpr hlength
      simp [natBitCapOutput, nativeNatEqOutput, hcap, hleft, hequal]
    · have hleft : ¬ (natBitCapCeilLogValue cap value ≤ cap) := by
        intro hcontra
        exact hlength (hiff.mp hcontra)
      have hequal : ¬ (bitInputPrefix cap value = value) := by
        intro hcontra
        exact hlength (hprefix.mp hcontra)
      simp [natBitCapOutput, nativeNatEqOutput, hcap, hleft, hequal]

/-! ## The fixed program -/

/-- The fixed validator contains one preparation, one ceiling-logarithm
computation and one native comparison.  All mode-specific callers share this
program. -/
def natBitCapProgram : NPOracleProgram :=
  linkPrograms natBitCapPrepareProgram <|
    linkPrograms natBitCapCeilLogStageProgram nativeNatLeProgram

@[simp] theorem natBitCapProgram_oracleFree :
    OracleFree natBitCapProgram := by
  exact oracleFree_linkPrograms natBitCapPrepareProgram_oracleFree <|
    oracleFree_linkPrograms
      (preserveRightProgram_oracleFree binaryNatCeilLogProgram
        binaryNatCeilLogProgram_oracleFree)
      nativeNatLeProgram_oracleFree

def natBitCapFuel (cap value : ℕ) : ℕ :=
  linkFuel
    (linkPrograms natBitCapCeilLogStageProgram nativeNatLeProgram) 6 <|
      linkFuel nativeNatLeProgram
        (natBitCapCeilLogStageFuel cap value)
        (nativeNatLeFuel (natBitCapCeilLogValue cap value) cap)

def natBitCapBits (inputLength cap value : ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max (natBitCapPrepareBits cap value) <|
      max (natBitCapCeilLogStageBits cap value)
        (nativeNatLeBits (natBitCapCeilLogValue cap value) cap)

theorem run_natBitCapProgram (inputLength cap value : ℕ) :
    runNPOracleProgram natBitCapProgram
        (natBitCapBits inputLength cap value)
        (natBitCapFuel cap value)
        (initialNPOracleState inputLength (natBitCapInput cap value)) =
      some (natBitCapOutput cap value) := by
  let maximumBits := natBitCapBits inputLength cap value
  have hpositive : 1 ≤ maximumBits := by
    simp [maximumBits, natBitCapBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    simp [maximumBits, natBitCapBits]
  have hprepare : natBitCapPrepareBits cap value ≤ maximumBits := by
    simp [maximumBits, natBitCapBits]
  have hstage : natBitCapCeilLogStageBits cap value ≤ maximumBits := by
    simp [maximumBits, natBitCapBits]
  have hcompare :
      nativeNatLeBits (natBitCapCeilLogValue cap value) cap ≤
        maximumBits := by
    simp [maximumBits, natBitCapBits]
  have hprepareRun :
      runNPOracleProgram natBitCapPrepareProgram maximumBits 6
          (initialNPOracleState inputLength (natBitCapInput cap value)) =
        some (natBitCapPreparedInput cap value) :=
    run_bits_mono
      (run_natBitCapPrepareProgram inputLength cap value) hprepare
  have hstageRun :
      runNPOracleProgram natBitCapCeilLogStageProgram maximumBits
          (natBitCapCeilLogStageFuel cap value)
          (initialNPOracleState inputLength
            (natBitCapPreparedInput cap value)) =
        some (natBitCapCompareInput cap value) :=
    run_bits_mono
      (run_natBitCapCeilLogStageProgram inputLength cap value) hstage
  have hcompareRun :
      runNPOracleProgram nativeNatLeProgram maximumBits
          (nativeNatLeFuel (natBitCapCeilLogValue cap value) cap)
          (initialNPOracleState inputLength
            (natBitCapCompareInput cap value)) =
        some (natBitCapOutput cap value) := by
    rw [← natBitCapExecutableOutput_eq cap value]
    exact run_bits_mono
      (run_nativeNatLeProgram inputLength
        (natBitCapCeilLogValue cap value) cap)
      hcompare
  have htail :=
    run_linkPrograms hpositive hlength hstageRun hcompareRun
  have hrun :=
    run_linkPrograms hpositive hlength hprepareRun htail
  simpa only [natBitCapProgram, natBitCapFuel] using hrun

/-! ## Exact semantic boundary -/

@[simp] theorem natBitCapOutput_ne_zero_iff (cap value : ℕ) :
    natBitCapOutput cap value ≠ 0 ↔ natBitLength value ≤ cap := by
  by_cases hcap : cap = 0
  · subst cap
    simp [natBitCapOutput, natBitLength]
  · have hpositive : 0 < cap := Nat.pos_of_ne_zero hcap
    simp only [natBitCapOutput, if_neg hcap,
      nativeNatEqOutput_ne_zero_iff]
    exact bitInputPrefix_eq_self_iff_natBitLength_le cap value hpositive

/-! ## The polynomial charge

The whole point of the ceiling-logarithm stage: the bit-cap check is charged
linearly in the *widths* of its two operands, never in their magnitudes. -/

/-- The request-independent part of the bit-cap charge: two linker overheads,
the preparation charge and the constant part of the ceiling-logarithm loop. -/
def natBitCapFuelOverhead : ℕ :=
  linkFuel
    (linkPrograms natBitCapCeilLogStageProgram nativeNatLeProgram) 6 <|
      linkFuel nativeNatLeProgram 10 0

private theorem natBitCapFuel_eq (cap value : ℕ) :
    natBitCapFuel cap value =
      natBitCapFuelOverhead + 4 * natBitCapCeilLogValue cap value +
        nativeNatLeFuel (natBitCapCeilLogValue cap value) cap := by
  simp only [natBitCapFuel, natBitCapFuelOverhead, natBitCapCeilLogStageFuel,
    natBitCapCeilLogValue, preserveRightFuel, binaryNatCeilLogFuel, linkFuel]
  omega

private theorem natBitCapCeilLogValue_le (cap value : ℕ) :
    natBitCapCeilLogValue cap value ≤ natBitLength value := by
  have hpositive : 1 ≤ natBitLength value := by
    unfold natBitLength
    omega
  by_cases hcap : cap = 0
  · have hclog : Nat.clog 2 2 ≤ 1 :=
      Nat.clog_le_of_le_pow (by norm_num)
    simp only [natBitCapCeilLogValue, natBitCapCeilLogArgument, if_pos hcap]
    omega
  · have hbound : value < 2 ^ (Nat.log 2 value + 1) := by
      simpa [Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (b := 2) (by omega) value
    have hpow : value + 1 ≤ 2 ^ natBitLength value := by
      unfold natBitLength
      omega
    simp only [natBitCapCeilLogValue, natBitCapCeilLogArgument, if_neg hcap]
    exact Nat.clog_le_of_le_pow hpow

/-- **The bit-cap charge is linear in the operand widths.**  This is the fact
the recovery-witness validator's polynomial envelope consumes: no term of
`natBitCapFuel` grows with `value` or with `2 ^ cap`. -/
theorem natBitCapFuel_le (cap value : ℕ) :
    natBitCapFuel cap value ≤
      natBitCapFuelOverhead +
        40 * (natBitLength value + natBitLength cap + 1) := by
  have hfuel := natBitCapFuel_eq cap value
  have hclog := natBitCapCeilLogValue_le cap value
  have hcomparator :=
    nativeNatLeFuel_le (natBitCapCeilLogValue cap value) cap
  have hpair :=
    CanonicalBinary.pairCodeBits_le (natBitCapCeilLogValue cap value) cap
  have hnarrow :
      natBitLength (natBitCapCeilLogValue cap value) ≤
        natBitLength value + 1 := by
    have hsucc := natBitLength_le_succ (natBitCapCeilLogValue cap value)
    omega
  have hmax :
      max (natBitLength (natBitCapCeilLogValue cap value))
          (natBitLength cap) ≤
        natBitLength value + natBitLength cap + 1 := by
    refine max_le ?_ ?_
    · omega
    · omega
  have hbits :
      nativeNatLeBits (natBitCapCeilLogValue cap value) cap ≤
        2 * (natBitLength value + natBitLength cap + 1) := by
    have hcode :
        natBitLength
            (Nat.pair (natBitCapCeilLogValue cap value) cap) ≤
          2 * (natBitLength value + natBitLength cap + 1) := by
      omega
    simpa [nativeNatLeBits, nativeNatLeInput] using hcode
  have hcapPositive : 1 ≤ natBitLength cap := by
    unfold natBitLength
    omega
  omega

end NearCubicWires.CanonicalNatBitCapProgram
