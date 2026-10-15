import Proof.Circuits.ValidatorPolynomialDomination

namespace NearCubicWires.ValidatorStageEnvelopes

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## §0 Width utilities

The binary width of a projection is the width of the projected code, and the
width of a pair is at most twice the larger component width.  These are the
only two facts the stage walks need about codes. -/

private theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right hle) 1

private theorem one_le_natBitLength (value : ℕ) : 1 ≤ natBitLength value := by
  unfold natBitLength
  omega

/-- Width of a left projection. -/
private theorem natBitLength_unpair_left (code : ℕ) :
    natBitLength (Nat.unpair code).1 ≤ natBitLength code :=
  natBitLength_mono (Nat.unpair_left_le code)

/-- Width of a right projection. -/
private theorem natBitLength_unpair_right (code : ℕ) :
    natBitLength (Nat.unpair code).2 ≤ natBitLength code :=
  natBitLength_mono (Nat.unpair_right_le code)

/-- The domination judgement transported along a width bound. -/
theorem polyBounded_natBitLength_of_le
    {value bound measure coefficient degree : ℕ}
    (hbound : PolyBounded (natBitLength bound) measure coefficient degree)
    (hle : value ≤ bound) :
    PolyBounded (natBitLength value) measure coefficient degree :=
  hbound.mono (natBitLength_mono hle)

/-- Width of one pairing node. -/
theorem polyBounded_natBitLength_pair
    {left right measure leftCoefficient rightCoefficient degree : ℕ}
    (hleft : PolyBounded (natBitLength left) measure leftCoefficient degree)
    (hright : PolyBounded (natBitLength right) measure rightCoefficient degree) :
    PolyBounded (natBitLength (Nat.pair left right)) measure
      (2 * max leftCoefficient rightCoefficient) degree := by
  have hmax := hleft.max hright
  have hscaled := hmax.const_mul (factor := 2)
  exact hscaled.mono (pairCodeBits_le left right)

/-! ## §1 The native call and the native contextual call

`nativeCallFuel` is one `balancedCallFuel` at the *singleton* request list,
wrapped in two linkers; `nativeContextCallFuel` adds a framing adapter and the
context-preserving wrapper.  The request count is the closed numeral `1`, so
neither node raises the degree: this is the only place in the validator's cone
where a balanced call is *not* degree-raising, and it is why the oracle stage
costs exactly the degree of the circuit validator it calls. -/

/-- The two-instruction unwrap tail of `nativeCallProgram`.  The linked
program's own tail is `private` to `CanonicalNativeCallProgram`, so its shape
is restated here and checked against the module's definition by
`nativeCallFuel_eq` below: nothing is assumed about it. -/
private def nativeCallUnwrapShape : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .halt 0
  ]

/-- The private balanced sub-charge of `nativeCallFuel`, exposed by
definitional unfolding.  `callee` stays a variable, so no register span of a
composed program is ever evaluated. -/
private theorem nativeCallFuel_eq
    (callee : NPOracleProgram) (calleeFuel calleeInputLength requestCode : ℕ) :
    nativeCallFuel callee calleeFuel calleeInputLength requestCode =
      linkFuel
        (linkPrograms (balancedCallProgram callee) nativeCallUnwrapShape) 3
        (linkFuel nativeCallUnwrapShape
          (balancedCallFuel callee (fun _ => calleeFuel)
            [nativeInputRequest calleeInputLength requestCode]) 2) :=
  rfl

/-- Closed program-shape overhead of one native call. -/
def nativeCallOverhead (callee : NPOracleProgram) : ℕ :=
  programRegisterSpan
      (linkPrograms (balancedCallProgram callee) nativeCallUnwrapShape) + 5 +
    3 +
    (programRegisterSpan nativeCallUnwrapShape + 5 +
      (37 + ((balancedCallLayout callee).calleeSpan + 73)) + 2)

private theorem le_nativeCallLedger
    (outerSpan unwrapSpan calleeSpan calleeFuel : ℕ) :
    outerSpan + 5 + 3 +
        (unwrapSpan + 5 + (37 + 1 * (calleeSpan + 73 + calleeFuel)) + 2) ≤
      outerSpan + 5 + 3 +
        (unwrapSpan + 5 + (37 + (calleeSpan + 73)) + 2) + calleeFuel := by
  omega

/-- **Exact ledger of one native call.**  A closed program-shape overhead plus
one copy of the callee's own charge: the singleton request list contributes no
degree. -/
theorem nativeCallFuel_le
    (callee : NPOracleProgram) (calleeFuel calleeInputLength requestCode : ℕ) :
    nativeCallFuel callee calleeFuel calleeInputLength requestCode ≤
      nativeCallOverhead callee + calleeFuel := by
  have hbalanced :
      balancedCallFuel callee (fun _ => calleeFuel)
          [nativeInputRequest calleeInputLength requestCode] ≤
        37 + [nativeInputRequest calleeInputLength requestCode].length *
          ((balancedCallLayout callee).calleeSpan + 73 + calleeFuel) :=
    balancedCallFuel_le callee (fun _ => calleeFuel)
      [nativeInputRequest calleeInputLength requestCode] calleeFuel
      (by intro request _; exact le_rfl)
  have hlength :
      [nativeInputRequest calleeInputLength requestCode].length = 1 := rfl
  rw [hlength] at hbalanced
  rw [nativeCallFuel_eq]
  simp only [linkFuel, nativeCallOverhead]
  have hledger :=
    le_nativeCallLedger
      (programRegisterSpan
        (linkPrograms (balancedCallProgram callee) nativeCallUnwrapShape))
      (programRegisterSpan nativeCallUnwrapShape)
      ((balancedCallLayout callee).calleeSpan) calleeFuel
  omega

/-- Closed program-shape overhead of one native contextual call. -/
def nativeContextCallOverhead (callee : NPOracleProgram) : ℕ :=
  programRegisterSpan (preserveRightProgram (nativeCallProgram callee)) + 5 +
    6 + (nativeCallOverhead callee + 4)

/-- **Exact ledger of one native contextual call.** -/
theorem nativeContextCallFuel_le
    (callee : NPOracleProgram) (calleeFuel calleeInputLength requestCode : ℕ) :
    nativeContextCallFuel callee calleeFuel calleeInputLength requestCode ≤
      nativeContextCallOverhead callee + calleeFuel := by
  have hinner :=
    nativeCallFuel_le callee calleeFuel calleeInputLength requestCode
  simp only [nativeContextCallFuel, nativeContextCallOverhead,
    preserveRightFuel, linkFuel]
  omega

/-- Degree-preserving domination for a native contextual call. -/
theorem nativeContextCallFuel_polyBounded
    {callee : NPOracleProgram}
    {calleeFuel calleeInputLength requestCode measure coefficient degree : ℕ}
    (hcallee : PolyBounded calleeFuel measure coefficient degree) :
    PolyBounded
      (nativeContextCallFuel callee calleeFuel calleeInputLength requestCode)
      measure (nativeContextCallOverhead callee + coefficient) degree :=
  ((polyBounded_const (nativeContextCallOverhead callee) measure
    degree).add hcallee).mono
    (nativeContextCallFuel_le callee calleeFuel calleeInputLength requestCode)

/-- The size cap read out of a handoff is a projection of the handoff. -/
theorem handoffOracleSizeCap_le (handoff : ℕ) :
    handoffOracleSizeCap handoff ≤ handoff := by
  simp only [handoffOracleSizeCap, handoffLimitsCode]
  refine (Nat.unpair_left_le _).trans ?_
  refine (Nat.unpair_right_le _).trans ?_
  refine (Nat.unpair_right_le _).trans ?_
  refine (Nat.unpair_right_le _).trans ?_
  refine (Nat.unpair_right_le _).trans ?_
  exact Nat.unpair_right_le _

/-- The compared node count is a projection of the circuit validator's own
output. -/
theorem recoveryOracleBoundValue_le (handoff : ℕ) :
    recoveryOracleBoundValue handoff ≤
      recoveryOracleValidationResult handoff := by
  simp only [recoveryOracleBoundValue]
  split
  · exact Nat.zero_le _
  · simp only [recoveryOracleNodeCount]
    exact Nat.unpair_right_le _

theorem recoveryOracleBoundCap_le (handoff : ℕ) :
    recoveryOracleBoundCap handoff ≤ handoff := by
  simp only [recoveryOracleBoundCap]
  split
  · exact Nat.zero_le _
  · exact handoffOracleSizeCap_le handoff

/-- **The shared bound check, dominated.**  Its fuel is linear in the width of
the compared pair, so two width certificates suffice and the degree is
preserved. -/
theorem recoveryBoundedContextCheckFuel_polyBounded
    {value cap measure valueCoefficient capCoefficient degree : ℕ}
    (hvalue : PolyBounded (natBitLength value) measure valueCoefficient degree)
    (hcap : PolyBounded (natBitLength cap) measure capCoefficient degree) :
    PolyBounded (recoveryBoundedContextCheckFuel value cap) measure
      (36 * max valueCoefficient capCoefficient + 24) degree := by
  have hpair := polyBounded_natBitLength_pair hvalue hcap
  have hscaled := hpair.const_mul (factor := 18)
  have htotal := hscaled.add (polyBounded_const 24 measure degree)
  have hcoefficient :
      18 * (2 * max valueCoefficient capCoefficient) + 24 =
        36 * max valueCoefficient capCoefficient + 24 := by ring
  rw [hcoefficient] at htotal
  refine htotal.mono ?_
  have hleaf := recoveryBoundedContextCheckFuel_le value cap
  have hinput : nativeNatLeBits value cap = natBitLength (Nat.pair value cap) :=
    rfl
  rw [hinput] at hleaf
  exact hleaf

/-- **The oracle call, dominated.**  One native contextual call into the
Boolean-circuit validator: degree-preserving, because its request list is a
singleton. -/
theorem recoveryOracleCallFuel_polyBounded
    {handoff measure circuitCoefficient degree : ℕ}
    (hcircuit :
      PolyBounded
        (booleanCircuitValidationFuel (handoffOracleArity handoff)
          (handoffOracleCode handoff)) measure circuitCoefficient degree) :
    PolyBounded (recoveryOracleCallFuel handoff) measure
      (nativeContextCallOverhead booleanCircuitValidationProgram +
        circuitCoefficient) degree := by
  have hdefinition :
      recoveryOracleCallFuel handoff =
        nativeContextCallFuel booleanCircuitValidationProgram
          (booleanCircuitValidationFuel (handoffOracleArity handoff)
            (handoffOracleCode handoff))
          (handoffOracleArity handoff) (handoffOracleCode handoff) := rfl
  exact (nativeContextCallFuel_polyBounded hcircuit).mono
    (Nat.le_of_eq hdefinition)

theorem recoveryOracleValidationFuel_polyBounded
    {handoff measure circuitCoefficient resultCoefficient handoffCoefficient
      degree : ℕ}
    (hcircuit :
      PolyBounded
        (booleanCircuitValidationFuel (handoffOracleArity handoff)
          (handoffOracleCode handoff)) measure circuitCoefficient degree)
    (hresult :
      PolyBounded (natBitLength (recoveryOracleValidationResult handoff))
        measure resultCoefficient degree)
    (hhandoff :
      PolyBounded (natBitLength handoff) measure handoffCoefficient degree) :
    PolyBounded (recoveryOracleValidationFuel handoff) measure
      (programRegisterSpan
          (linkPrograms recoveryOracleCallProgram <|
            linkPrograms recoveryOracleBoundLoweringProgram
              recoveryBoundedContextCheckProgram) + 5 +
          recoveryOracleCallLoweringFuel +
        (programRegisterSpan
            (linkPrograms recoveryOracleBoundLoweringProgram
              recoveryBoundedContextCheckProgram) + 5 +
            (nativeContextCallOverhead booleanCircuitValidationProgram +
              circuitCoefficient) +
          (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
              recoveryOracleBoundLoweringFuel +
            (36 * max resultCoefficient handoffCoefficient + 24))))
      degree := by
  have hcheck :
      PolyBounded
        (recoveryBoundedContextCheckFuel (recoveryOracleBoundValue handoff)
          (recoveryOracleBoundCap handoff)) measure
        (36 * max resultCoefficient handoffCoefficient + 24) degree :=
    recoveryBoundedContextCheckFuel_polyBounded
      (polyBounded_natBitLength_of_le hresult
        (recoveryOracleBoundValue_le handoff))
      (polyBounded_natBitLength_of_le hhandoff
        (recoveryOracleBoundCap_le handoff))
  have htail :
      PolyBounded (recoveryOracleValidationTailFuel handoff) measure
        (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
            recoveryOracleBoundLoweringFuel +
          (36 * max resultCoefficient handoffCoefficient + 24)) degree := by
    rw [recoveryOracleValidationTailFuel]
    exact linkFuel_polyBounded
      (polyBounded_const recoveryOracleBoundLoweringFuel measure degree) hcheck
  have hcallTail :
      PolyBounded (recoveryOracleValidationCallTailFuel handoff) measure
        (programRegisterSpan
            (linkPrograms recoveryOracleBoundLoweringProgram
              recoveryBoundedContextCheckProgram) + 5 +
            (nativeContextCallOverhead booleanCircuitValidationProgram +
              circuitCoefficient) +
          (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
              recoveryOracleBoundLoweringFuel +
            (36 * max resultCoefficient handoffCoefficient + 24))) degree := by
    rw [recoveryOracleValidationCallTailFuel]
    exact linkFuel_polyBounded (recoveryOracleCallFuel_polyBounded hcircuit)
      htail
  rw [recoveryOracleValidationFuel]
  exact linkFuel_polyBounded
    (polyBounded_const recoveryOracleCallLoweringFuel measure degree) hcallTail

/-- The width parameter of the oracle stage: the wider of the handoff record
and the Boolean-circuit validator's result. -/
def recoveryOracleStageWidth (handoff : ℕ) : ℕ :=
  max (natBitLength (recoveryOracleValidationResult handoff))
    (natBitLength handoff)

theorem one_le_recoveryOracleStageWidth (handoff : ℕ) :
    1 ≤ recoveryOracleStageWidth handoff :=
  (one_le_natBitLength _).trans (le_max_right _ _)

private theorem natBitLength_pair_le_double
    {left right bound : ℕ}
    (hleft : natBitLength left ≤ bound)
    (hright : natBitLength right ≤ bound) :
    natBitLength (Nat.pair left right) ≤ 2 * bound := by
  have hpair := pairCodeBits_le left right
  omega

private theorem natBitLength_max_le
    {left right bound : ℕ}
    (hleft : natBitLength left ≤ bound)
    (hright : natBitLength right ≤ bound) :
    natBitLength (max left right) ≤ bound := by
  rcases Nat.le_total left right with hle | hle
  · rw [Nat.max_eq_right hle]
    exact hright
  · rw [Nat.max_eq_left hle]
    exact hleft

/-- The handoff's own projections never widen it. -/
private theorem handoff_projection_widths (handoff : ℕ) :
    natBitLength (Nat.unpair handoff).2 ≤ natBitLength handoff ∧
      natBitLength (Nat.unpair (Nat.unpair handoff).2).2 ≤
        natBitLength handoff := by
  refine ⟨natBitLength_unpair_right handoff, ?_⟩
  exact (natBitLength_unpair_right _).trans
    (natBitLength_unpair_right handoff)

/-- The lowered oracle-call request is the widest value the lowering stage
materializes. -/
private theorem recoveryOracleCallLoweringValues_le (handoff : ℕ) :
    recoveryOracleCallLoweringBits handoff ≤
      natBitLength (recoveryOracleCallInput handoff) := by
  have hcallInput :
      recoveryOracleCallInput handoff =
        Nat.pair (handoffOracleCode handoff)
          (Nat.pair (handoffOracleArity handoff) handoff) := rfl
  have hretained :
      Nat.pair (handoffOracleArity handoff) handoff ≤
        recoveryOracleCallInput handoff := by
    rw [hcallInput]
    exact Nat.right_le_pair _ _
  have hhandoff : handoff ≤ recoveryOracleCallInput handoff :=
    (Nat.right_le_pair _ _).trans hretained
  have hproject :
      ∀ code : ℕ, code ≤ handoff → code ≤ recoveryOracleCallInput handoff :=
    fun _ hcode => hcode.trans hhandoff
  have htail₀ : (Nat.unpair handoff).2 ≤ handoff := Nat.unpair_right_le _
  have htail₁ : (Nat.unpair (Nat.unpair handoff).2).2 ≤ handoff :=
    (Nat.unpair_right_le _).trans htail₀
  have horacleCode :
      (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).1 ≤ handoff :=
    (Nat.unpair_left_le _).trans htail₁
  have htail₂ :
      (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2 ≤ handoff :=
    (Nat.unpair_right_le _).trans htail₁
  have hlimits :
      (Nat.unpair
        (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2).2 ≤ handoff :=
    (Nat.unpair_right_le _).trans htail₂
  have harity :
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair (Nat.unpair handoff).2).2).2).2).1 ≤ handoff :=
    (Nat.unpair_left_le _).trans hlimits
  have harityPair :
      Nat.pair
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair (Nat.unpair handoff).2).2).2).2).1 handoff ≤
        recoveryOracleCallInput handoff := by
    have harityCode :
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair (Nat.unpair handoff).2).2).2).2).1 =
          handoffOracleArity handoff := rfl
    rw [harityCode]
    exact hretained
  have hledger :
      recoveryOracleCallLoweringBits handoff =
        natBitLength
          ([ handoff
           , (Nat.unpair handoff).2
           , (Nat.unpair (Nat.unpair handoff).2).2
           , (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).1
           , (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2
           , (Nat.unpair
               (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2).2
           , (Nat.unpair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair (Nat.unpair handoff).2).2).2).2).1
           , Nat.pair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair
                     (Nat.unpair (Nat.unpair handoff).2).2).2).2).1 handoff
           , recoveryOracleCallInput handoff
           ].foldr max 0) := rfl
  rw [hledger]
  refine natBitLength_mono ?_
  simp only [List.foldr_cons, List.foldr_nil]
  have hproject₀ := hproject _ htail₀
  have hproject₁ := hproject _ htail₁
  have hprojectOracle := hproject _ horacleCode
  have hproject₂ := hproject _ htail₂
  have hprojectLimits := hproject _ hlimits
  have hprojectArity := hproject _ harity
  omega

theorem recoveryOracleCallLoweringBits_le (handoff : ℕ) :
    recoveryOracleCallLoweringBits handoff ≤
      4 * recoveryOracleStageWidth handoff := by
  have hhandoff :
      natBitLength handoff ≤ recoveryOracleStageWidth handoff :=
    le_max_right _ _
  have harity :
      natBitLength (handoffOracleArity handoff) ≤
        recoveryOracleStageWidth handoff := by
    refine natBitLength_mono ?_ |>.trans hhandoff
    simp only [handoffOracleArity, handoffLimitsCode]
    refine (Nat.unpair_left_le _).trans ?_
    refine (Nat.unpair_right_le _).trans ?_
    refine (Nat.unpair_right_le _).trans ?_
    refine (Nat.unpair_right_le _).trans ?_
    exact Nat.unpair_right_le _
  have hcode :
      natBitLength (handoffOracleCode handoff) ≤
        recoveryOracleStageWidth handoff := by
    refine natBitLength_mono ?_ |>.trans hhandoff
    simp only [handoffOracleCode]
    refine (Nat.unpair_left_le _).trans ?_
    refine (Nat.unpair_right_le _).trans ?_
    exact Nat.unpair_right_le _
  have hinner :=
    natBitLength_pair_le_double harity hhandoff
  have houter :
      natBitLength (recoveryOracleCallInput handoff) ≤
        2 * (2 * recoveryOracleStageWidth handoff) := by
    have hcallInput :
        recoveryOracleCallInput handoff =
          Nat.pair (handoffOracleCode handoff)
            (Nat.pair (handoffOracleArity handoff) handoff) := rfl
    rw [hcallInput]
    exact natBitLength_pair_le_double (by omega) hinner
  have hledger := recoveryOracleCallLoweringValues_le handoff
  omega

private theorem recoveryOracleBoundLoweringBits_le_pairs (handoff : ℕ) :
    recoveryOracleBoundLoweringBits handoff ≤
      max
        (natBitLength
          (Nat.pair
            (nativeNatLeInput (Nat.unpair
              (recoveryOracleValidationResult handoff)).2
              (handoffOracleSizeCap handoff)) handoff))
        (natBitLength (recoveryOracleCallOutput handoff)) := by
  have hcallOutput :
      recoveryOracleCallOutput handoff =
        Nat.pair (recoveryOracleValidationResult handoff)
          (Nat.pair (handoffOracleArity handoff) handoff) := rfl
  have hresult :
      recoveryOracleValidationResult handoff ≤
        recoveryOracleCallOutput handoff := by
    rw [hcallOutput]
    exact Nat.left_le_pair _ _
  have hretained :
      Nat.pair (handoffOracleArity handoff) handoff ≤
        recoveryOracleCallOutput handoff := by
    rw [hcallOutput]
    exact Nat.right_le_pair _ _
  have hhandoff : handoff ≤ recoveryOracleCallOutput handoff :=
    (Nat.right_le_pair _ _).trans hretained
  have hcount :
      (Nat.unpair (recoveryOracleValidationResult handoff)).2 ≤
        recoveryOracleCallOutput handoff :=
    (Nat.unpair_right_le _).trans hresult
  have htail₀ : (Nat.unpair handoff).2 ≤ handoff := Nat.unpair_right_le _
  have htail₁ : (Nat.unpair (Nat.unpair handoff).2).2 ≤ handoff :=
    (Nat.unpair_right_le _).trans htail₀
  have htail₂ :
      (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2 ≤ handoff :=
    (Nat.unpair_right_le _).trans htail₁
  have hlimits :
      (Nat.unpair
        (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2).2 ≤ handoff :=
    (Nat.unpair_right_le _).trans htail₂
  have hlimitsTail :
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair (Nat.unpair handoff).2).2).2).2).2 ≤ handoff :=
    (Nat.unpair_right_le _).trans hlimits
  have hsizeCap :
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair
              (Nat.unpair (Nat.unpair handoff).2).2).2).2).2).1 ≤ handoff :=
    (Nat.unpair_left_le _).trans hlimitsTail
  have hrequest :
      nativeNatLeInput
          (Nat.unpair (recoveryOracleValidationResult handoff)).2
          (handoffOracleSizeCap handoff) ≤
        Nat.pair
          (nativeNatLeInput
            (Nat.unpair (recoveryOracleValidationResult handoff)).2
            (handoffOracleSizeCap handoff)) handoff :=
    Nat.left_le_pair _ _
  have hledger :
      recoveryOracleBoundLoweringBits handoff =
        natBitLength
          ([ recoveryOracleCallOutput handoff
           , recoveryOracleValidationResult handoff
           , Nat.pair (handoffOracleArity handoff) handoff
           , handoff
           , (Nat.unpair (recoveryOracleValidationResult handoff)).2
           , (Nat.unpair handoff).2
           , (Nat.unpair (Nat.unpair handoff).2).2
           , (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2
           , (Nat.unpair
               (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2).2
           , (Nat.unpair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair (Nat.unpair handoff).2).2).2).2).2
           , (Nat.unpair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair
                     (Nat.unpair (Nat.unpair handoff).2).2).2).2).2).1
           , nativeNatLeInput
               (Nat.unpair (recoveryOracleValidationResult handoff)).2
               (handoffOracleSizeCap handoff)
           , Nat.pair
               (nativeNatLeInput
                 (Nat.unpair (recoveryOracleValidationResult handoff)).2
                 (handoffOracleSizeCap handoff)) handoff
           , 0
           ].foldr max 0) := rfl
  have hvalues :
      ([ recoveryOracleCallOutput handoff
       , recoveryOracleValidationResult handoff
       , Nat.pair (handoffOracleArity handoff) handoff
       , handoff
       , (Nat.unpair (recoveryOracleValidationResult handoff)).2
       , (Nat.unpair handoff).2
       , (Nat.unpair (Nat.unpair handoff).2).2
       , (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2
       , (Nat.unpair
           (Nat.unpair (Nat.unpair (Nat.unpair handoff).2).2).2).2
       , (Nat.unpair
           (Nat.unpair
             (Nat.unpair
               (Nat.unpair (Nat.unpair handoff).2).2).2).2).2
       , (Nat.unpair
           (Nat.unpair
             (Nat.unpair
               (Nat.unpair
                 (Nat.unpair (Nat.unpair handoff).2).2).2).2).2).1
       , nativeNatLeInput
           (Nat.unpair (recoveryOracleValidationResult handoff)).2
           (handoffOracleSizeCap handoff)
       , Nat.pair
           (nativeNatLeInput
             (Nat.unpair (recoveryOracleValidationResult handoff)).2
             (handoffOracleSizeCap handoff)) handoff
       , 0
       ].foldr max 0) ≤
        max
          (Nat.pair
            (nativeNatLeInput
              (Nat.unpair (recoveryOracleValidationResult handoff)).2
              (handoffOracleSizeCap handoff)) handoff)
          (recoveryOracleCallOutput handoff) := by
    simp only [List.foldr_cons, List.foldr_nil]
    omega
  rw [hledger]
  refine (natBitLength_mono hvalues).trans ?_
  exact natBitLength_max_le (le_max_left _ _) (le_max_right _ _)

private theorem recoveryOracleStageWidth_result (handoff : ℕ) :
    natBitLength (recoveryOracleValidationResult handoff) ≤
      recoveryOracleStageWidth handoff := le_max_left _ _

private theorem recoveryOracleStageWidth_handoff (handoff : ℕ) :
    natBitLength handoff ≤ recoveryOracleStageWidth handoff :=
  le_max_right _ _

theorem recoveryOracleBoundLoweringBits_le (handoff : ℕ) :
    recoveryOracleBoundLoweringBits handoff ≤
      4 * recoveryOracleStageWidth handoff := by
  have hhandoff := recoveryOracleStageWidth_handoff handoff
  have hresult := recoveryOracleStageWidth_result handoff
  have hcount :
      natBitLength (Nat.unpair (recoveryOracleValidationResult handoff)).2 ≤
        recoveryOracleStageWidth handoff :=
    (natBitLength_unpair_right _).trans hresult
  have hsizeCap :
      natBitLength (handoffOracleSizeCap handoff) ≤
        recoveryOracleStageWidth handoff :=
    (natBitLength_mono (handoffOracleSizeCap_le handoff)).trans hhandoff
  have harity :
      natBitLength (handoffOracleArity handoff) ≤
        recoveryOracleStageWidth handoff := by
    refine (natBitLength_mono ?_).trans hhandoff
    simp only [handoffOracleArity, handoffLimitsCode]
    refine (Nat.unpair_left_le _).trans ?_
    refine (Nat.unpair_right_le _).trans ?_
    refine (Nat.unpair_right_le _).trans ?_
    refine (Nat.unpair_right_le _).trans ?_
    exact Nat.unpair_right_le _
  have hrequest :
      natBitLength
          (nativeNatLeInput
            (Nat.unpair (recoveryOracleValidationResult handoff)).2
            (handoffOracleSizeCap handoff)) ≤
        2 * recoveryOracleStageWidth handoff :=
    natBitLength_pair_le_double hcount hsizeCap
  have hrequestPair :
      natBitLength
          (Nat.pair
            (nativeNatLeInput
              (Nat.unpair (recoveryOracleValidationResult handoff)).2
              (handoffOracleSizeCap handoff)) handoff) ≤
        2 * (2 * recoveryOracleStageWidth handoff) :=
    natBitLength_pair_le_double hrequest (by omega)
  have hretained :
      natBitLength (Nat.pair (handoffOracleArity handoff) handoff) ≤
        2 * recoveryOracleStageWidth handoff :=
    natBitLength_pair_le_double harity hhandoff
  have hcallOutput :
      natBitLength (recoveryOracleCallOutput handoff) ≤
        2 * (2 * recoveryOracleStageWidth handoff) := by
    have hshape :
        recoveryOracleCallOutput handoff =
          Nat.pair (recoveryOracleValidationResult handoff)
            (Nat.pair (handoffOracleArity handoff) handoff) := rfl
    rw [hshape]
    exact natBitLength_pair_le_double (by omega) hretained
  have hpairs := recoveryOracleBoundLoweringBits_le_pairs handoff
  omega

theorem recoveryOracleBoundContext_le (handoff : ℕ) :
    recoveryOracleBoundContext handoff ≤ handoff := by
  simp only [recoveryOracleBoundContext]
  split
  · exact Nat.zero_le _
  · exact le_rfl

private theorem natBitLength_nativeNatLeOutput (value cap : ℕ) :
    natBitLength (nativeNatLeOutput value cap) ≤ 1 := by
  have hle : nativeNatLeOutput value cap ≤ 1 := by
    simp only [nativeNatLeOutput]
    exact Bool.toNat_le _
  have hone : natBitLength 1 = 1 := by
    simp only [natBitLength, Nat.log_one_right]
  exact (natBitLength_mono hle).trans (Nat.le_of_eq hone)

/-- **The shared bound check's register requirement.**  Its every register is a
pair of the compared node count, the trusted size cap, the retained context and
one Boolean flag, so the stage width bounds it. -/
theorem recoveryBoundedContextCheckBits_le (inputLength handoff : ℕ) :
    recoveryBoundedContextCheckBits inputLength
        (recoveryOracleBoundValue handoff) (recoveryOracleBoundCap handoff)
        (recoveryOracleBoundContext handoff) ≤
      max (natBitLength inputLength) (4 * recoveryOracleStageWidth handoff) := by
  set value := recoveryOracleBoundValue handoff with hvalue
  set cap := recoveryOracleBoundCap handoff with hcap
  set context := recoveryOracleBoundContext handoff with hcontext
  have hwidthValue :
      natBitLength value ≤ recoveryOracleStageWidth handoff :=
    (natBitLength_mono (recoveryOracleBoundValue_le handoff)).trans
      (recoveryOracleStageWidth_result handoff)
  have hwidthCap : natBitLength cap ≤ recoveryOracleStageWidth handoff :=
    (natBitLength_mono (recoveryOracleBoundCap_le handoff)).trans
      (recoveryOracleStageWidth_handoff handoff)
  have hwidthContext :
      natBitLength context ≤ recoveryOracleStageWidth handoff :=
    (natBitLength_mono (recoveryOracleBoundContext_le handoff)).trans
      (recoveryOracleStageWidth_handoff handoff)
  have hpositive := one_le_recoveryOracleStageWidth handoff
  have hcompared :
      natBitLength (Nat.pair value cap) ≤
        2 * recoveryOracleStageWidth handoff :=
    natBitLength_pair_le_double hwidthValue hwidthCap
  have hcomparedContext :
      natBitLength (Nat.pair (Nat.pair value cap) context) ≤
        2 * (2 * recoveryOracleStageWidth handoff) :=
    natBitLength_pair_le_double hcompared (by omega)
  have hflag := natBitLength_nativeNatLeOutput value cap
  have hflagContext :
      natBitLength (Nat.pair (nativeNatLeOutput value cap) context) ≤
        2 * recoveryOracleStageWidth handoff :=
    natBitLength_pair_le_double (by omega) hwidthContext
  have hledger :
      recoveryBoundedContextCheckBits inputLength value cap context =
        max (natBitLength inputLength)
          (max
            (max (natBitLength (Nat.pair value cap))
              (max (natBitLength (Nat.pair (Nat.pair value cap) context))
                (natBitLength (Nat.pair (nativeNatLeOutput value cap) context))))
            (natBitLength (Nat.pair (nativeNatLeOutput value cap) context))) :=
    rfl
  rw [hledger]
  omega

theorem recoveryOracleValidationBits_polyBounded
    {inputLength handoff measure lengthCoefficient widthCoefficient
      callCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hwidth :
      PolyBounded (recoveryOracleStageWidth handoff) measure widthCoefficient
        degree)
    (hcall :
      PolyBounded (recoveryOracleCallBits inputLength handoff) measure
        callCoefficient degree) :
    PolyBounded (recoveryOracleValidationBits inputLength handoff) measure
      (max (max lengthCoefficient (4 * widthCoefficient)) callCoefficient)
      degree := by
  set coefficient :=
    max (max lengthCoefficient (4 * widthCoefficient)) callCoefficient
    with hcoefficient
  have hscaled :
      PolyBounded (4 * recoveryOracleStageWidth handoff) measure
        (4 * widthCoefficient) degree := hwidth.const_mul 4
  have hlengthAt : PolyBounded (natBitLength inputLength) measure coefficient
      degree := hlength.coefficient_mono (by omega)
  have hloweringAt :
      PolyBounded (recoveryOracleCallLoweringBits handoff) measure coefficient
        degree :=
    (hscaled.mono (recoveryOracleCallLoweringBits_le handoff)).coefficient_mono
      (by omega)
  have hcallAt :
      PolyBounded (recoveryOracleCallBits inputLength handoff) measure
        coefficient degree := hcall.coefficient_mono (by omega)
  have hboundAt :
      PolyBounded (recoveryOracleBoundLoweringBits handoff) measure coefficient
        degree :=
    (hscaled.mono (recoveryOracleBoundLoweringBits_le handoff)).coefficient_mono
      (by omega)
  have hcheckAt :
      PolyBounded
        (recoveryBoundedContextCheckBits inputLength
          (recoveryOracleBoundValue handoff) (recoveryOracleBoundCap handoff)
          (recoveryOracleBoundContext handoff)) measure coefficient degree :=
    ((hlength.max hscaled).mono
      (recoveryBoundedContextCheckBits_le inputLength handoff)).coefficient_mono
      (by omega)
  change recoveryOracleValidationBits inputLength handoff ≤
    coefficient * (measure + 1) ^ degree
  rw [recoveryOracleValidationBits]
  exact max_le hlengthAt (max_le hloweringAt (max_le hcallAt
    (max_le hboundAt hcheckAt)))

/-! ## §4 The structural prefix's register requirement

`recoveryValidatorStructuralPrefixBits` is a three-way maximum over the public
input width, the nested-handoff ledger and the width of the handoff record.
Every register the prefix materializes is a projection of the raw witness code,
the serialized policy record, or a pairing of at most four of them, so the whole
stage is bounded — unconditionally — by a fixed multiple of one width
parameter.  This is the ingredient §4 of the domination module identified as
not being an executable stage's own charge. -/

/-- The width parameter of the validator's structural prefix: the wider of the
raw witness code and the serialized policy record. -/
def recoveryValidatorPrefixWidth
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength raw) (natBitLength (encodeRecoveryWitnessLimits limits))

theorem one_le_recoveryValidatorPrefixWidth
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    1 ≤ recoveryValidatorPrefixWidth limits raw :=
  (one_le_natBitLength _).trans (le_max_left _ _)

/-- The outer envelope's public output is one of its own registers. -/
theorem recoveryEnvelopeOutput_le (raw : ℕ) :
    recoveryEnvelopeOutput raw ≤ recoveryEnvelopeRegisterBound raw := by
  simp only [recoveryEnvelopeOutput, recoveryEnvelopeRegisterBound]
  split
  · rename_i envelope _
    cases envelope.mode
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact Nat.zero_le _

private theorem natBitLength_recoveryEnvelopeOutput_le
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    natBitLength (recoveryEnvelopeOutput raw) ≤
      6 * recoveryValidatorPrefixWidth limits raw := by
  have hbound :
      natBitLength (recoveryEnvelopeOutput raw) ≤ recoveryEnvelopeBits raw :=
    natBitLength_mono (recoveryEnvelopeOutput_le raw)
  have hlinear := recoveryEnvelopeBits_le_linear raw
  have hraw :
      natBitLength raw ≤ recoveryValidatorPrefixWidth limits raw :=
    le_max_left _ _
  have hpositive := one_le_recoveryValidatorPrefixWidth limits raw
  omega

/-- **The handoff trace's register width.**  Every entry of the trace is a
projection of the raw code, the serialized policy, or a pairing of at most four
of them. -/
theorem recoveryValidatorHandoffBits_le
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryValidatorHandoffBits limits raw ≤
      16 * recoveryValidatorPrefixWidth limits raw := by
  set width := recoveryValidatorPrefixWidth limits raw with hwidth
  set limitsCode := encodeRecoveryWitnessLimits limits with hlimitsCode
  have hraw : natBitLength raw ≤ width := le_max_left _ _
  have hlimits : natBitLength limitsCode ≤ width := le_max_right _ _
  have hpositive : 1 ≤ width := one_le_recoveryValidatorPrefixWidth limits raw
  have henvelope :
      natBitLength (recoveryEnvelopeOutput raw) ≤ 6 * width :=
    natBitLength_recoveryEnvelopeOutput_le limits raw
  have htail₀ : (Nat.unpair raw).2 ≤ raw := Nat.unpair_right_le _
  have htaggedTail : (Nat.unpair (Nat.unpair raw).2).2 ≤ raw :=
    (Nat.unpair_right_le _).trans htail₀
  have htail₁ :
      (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2 ≤ raw :=
    (Nat.unpair_right_le _).trans htaggedTail
  have horacleCode :
      (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1 ≤ raw :=
    (Nat.unpair_left_le _).trans htail₁
  have htaggedTailTwo :
      (Nat.unpair
        (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).2 ≤ raw :=
    (Nat.unpair_right_le _).trans htail₁
  have htail₂ :
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).2).2 ≤ raw :=
    (Nat.unpair_right_le _).trans htaggedTailTwo
  have hsumCode :
      (Nat.unpair
        (Nat.unpair
          (Nat.unpair
            (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1 ≤ raw :=
    (Nat.unpair_left_le _).trans htail₂
  have hsumAndLimits :
      natBitLength
          (Nat.pair
            (Nat.unpair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
            limitsCode) ≤ 2 * width :=
    natBitLength_pair_le_double
      ((natBitLength_mono hsumCode).trans hraw) hlimits
  have horacleAndRest :
      natBitLength
          (Nat.pair
            (Nat.unpair
              (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
            (Nat.pair
              (Nat.unpair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair
                      (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
              limitsCode)) ≤ 2 * (2 * width) :=
    natBitLength_pair_le_double
      (((natBitLength_mono horacleCode).trans hraw).trans (by omega))
      hsumAndLimits
  have hrawAndRest :
      natBitLength
          (Nat.pair raw
            (Nat.pair
              (Nat.unpair
                (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
              (Nat.pair
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair
                      (Nat.unpair
                        (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
                limitsCode))) ≤ 2 * (2 * (2 * width)) :=
    natBitLength_pair_le_double (by omega) horacleAndRest
  have haccepted :
      natBitLength
          (Nat.pair (Nat.unpair (recoveryEnvelopeOutput raw)).1
            (Nat.pair raw
              (Nat.pair
                (Nat.unpair
                  (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
                (Nat.pair
                  (Nat.unpair
                    (Nat.unpair
                      (Nat.unpair
                        (Nat.unpair
                          (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
                  limitsCode)))) ≤ 2 * (2 * (2 * (2 * width))) := by
    refine natBitLength_pair_le_double ?_ (by omega)
    exact ((natBitLength_unpair_left _).trans henvelope).trans (by omega)
  have henvelopeAndLimits :
      natBitLength (Nat.pair (recoveryEnvelopeOutput raw) limitsCode) ≤
        2 * (6 * width) :=
    natBitLength_pair_le_double henvelope (by omega)
  have hledger :
      recoveryValidatorHandoffRegisters limits raw =
        ([ Nat.pair (recoveryEnvelopeOutput raw) limitsCode
         , recoveryEnvelopeOutput raw
         , limitsCode
         , (Nat.unpair (recoveryEnvelopeOutput raw)).1
         , raw
         , (Nat.unpair raw).2
         , (Nat.unpair (Nat.unpair raw).2).2
         , (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2
         , (Nat.unpair
             (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
         , (Nat.unpair
             (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).2
         , (Nat.unpair
             (Nat.unpair
               (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).2).2
         , (Nat.unpair
             (Nat.unpair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
         , Nat.pair
             (Nat.unpair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair
                     (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
             limitsCode
         , Nat.pair
             (Nat.unpair
               (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
             (Nat.pair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair
                     (Nat.unpair
                       (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
               limitsCode)
         , Nat.pair raw
             (Nat.pair
               (Nat.unpair
                 (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
               (Nat.pair
                 (Nat.unpair
                   (Nat.unpair
                     (Nat.unpair
                       (Nat.unpair
                         (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
                 limitsCode))
         , Nat.pair (Nat.unpair (recoveryEnvelopeOutput raw)).1
             (Nat.pair raw
               (Nat.pair
                 (Nat.unpair
                   (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
                 (Nat.pair
                   (Nat.unpair
                     (Nat.unpair
                       (Nat.unpair
                         (Nat.unpair
                           (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
                   limitsCode)))
         ].foldr max 0) := rfl
  have hprojections :
      natBitLength (Nat.unpair raw).2 ≤ width ∧
        natBitLength (Nat.unpair (Nat.unpair raw).2).2 ≤ width ∧
          natBitLength
            (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2 ≤ width ∧
            natBitLength
              (Nat.unpair
                (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1 ≤ width ∧
              natBitLength
                (Nat.unpair
                  (Nat.unpair
                    (Nat.unpair (Nat.unpair raw).2).2).2).2 ≤ width ∧
                natBitLength
                  (Nat.unpair
                    (Nat.unpair
                      (Nat.unpair
                        (Nat.unpair
                          (Nat.unpair raw).2).2).2).2).2 ≤ width ∧
                  natBitLength
                    (Nat.unpair
                      (Nat.unpair
                        (Nat.unpair
                          (Nat.unpair
                            (Nat.unpair
                              (Nat.unpair raw).2).2).2).2).2).1 ≤ width :=
    ⟨(natBitLength_mono htail₀).trans hraw,
      (natBitLength_mono htaggedTail).trans hraw,
      (natBitLength_mono htail₁).trans hraw,
      (natBitLength_mono horacleCode).trans hraw,
      (natBitLength_mono htaggedTailTwo).trans hraw,
      (natBitLength_mono htail₂).trans hraw,
      (natBitLength_mono hsumCode).trans hraw⟩
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hprojections
  have henvelopeLeft :
      natBitLength (Nat.unpair (recoveryEnvelopeOutput raw)).1 ≤ 6 * width :=
    (natBitLength_unpair_left _).trans henvelope
  simp only [recoveryValidatorHandoffBits, hledger, List.foldr_cons,
    List.foldr_nil]
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  have hzero : natBitLength 0 = 1 := by
    simp only [natBitLength, Nat.log_zero_right]
  omega

/-- The handoff record is one of the handoff trace's registers. -/
theorem recoveryValidatorHandoffOutput_le
    (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryValidatorHandoffOutput limits raw ≤
      recoveryValidatorHandoffRegisters limits raw := by
  have hledger :
      recoveryValidatorHandoffOutput limits raw =
        (if recoveryEnvelopeOutput raw = 0 then 0
          else
            Nat.pair (Nat.unpair (recoveryEnvelopeOutput raw)).1
              (Nat.pair raw
                (Nat.pair
                  (Nat.unpair
                    (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
                  (Nat.pair
                    (Nat.unpair
                      (Nat.unpair
                        (Nat.unpair
                          (Nat.unpair
                            (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
                    (encodeRecoveryWitnessLimits limits))))) := rfl
  have hregisters :
      recoveryValidatorHandoffRegisters limits raw =
        ([ Nat.pair (recoveryEnvelopeOutput raw)
             (encodeRecoveryWitnessLimits limits)
         , recoveryEnvelopeOutput raw
         , encodeRecoveryWitnessLimits limits
         , (Nat.unpair (recoveryEnvelopeOutput raw)).1
         , raw
         , (Nat.unpair raw).2
         , (Nat.unpair (Nat.unpair raw).2).2
         , (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2
         , (Nat.unpair
             (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
         , (Nat.unpair
             (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).2
         , (Nat.unpair
             (Nat.unpair
               (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).2).2
         , (Nat.unpair
             (Nat.unpair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
         , Nat.pair
             (Nat.unpair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair
                     (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
             (encodeRecoveryWitnessLimits limits)
         , Nat.pair
             (Nat.unpair
               (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
             (Nat.pair
               (Nat.unpair
                 (Nat.unpair
                   (Nat.unpair
                     (Nat.unpair
                       (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
               (encodeRecoveryWitnessLimits limits))
         , Nat.pair raw
             (Nat.pair
               (Nat.unpair
                 (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
               (Nat.pair
                 (Nat.unpair
                   (Nat.unpair
                     (Nat.unpair
                       (Nat.unpair
                         (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
                 (encodeRecoveryWitnessLimits limits)))
         , Nat.pair (Nat.unpair (recoveryEnvelopeOutput raw)).1
             (Nat.pair raw
               (Nat.pair
                 (Nat.unpair
                   (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).2).1
                 (Nat.pair
                   (Nat.unpair
                     (Nat.unpair
                       (Nat.unpair
                         (Nat.unpair
                           (Nat.unpair (Nat.unpair raw).2).2).2).2).2).1
                   (encodeRecoveryWitnessLimits limits))))
         ].foldr max 0) := rfl
  rw [hledger, hregisters]
  simp only [List.foldr_cons, List.foldr_nil]
  split
  · exact Nat.zero_le _
  · refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    exact le_max_left _ _

/-- **The structural prefix's register requirement, unconditionally.**  Only
the public input width and one width parameter survive. -/
theorem recoveryValidatorStructuralPrefixBits_le
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryValidatorStructuralPrefixBits inputLength limits raw ≤
      max (natBitLength inputLength)
        (16 * recoveryValidatorPrefixWidth limits raw) := by
  set width := recoveryValidatorPrefixWidth limits raw with hwidth
  set limitsCode := encodeRecoveryWitnessLimits limits with hlimitsCode
  have hraw : natBitLength raw ≤ width := le_max_left _ _
  have hlimits : natBitLength limitsCode ≤ width := le_max_right _ _
  have hpositive : 1 ≤ width := one_le_recoveryValidatorPrefixWidth limits raw
  have hhandoffTrace := recoveryValidatorHandoffBits_le limits raw
  have hhandoffOutput :
      natBitLength (recoveryValidatorHandoffOutput limits raw) ≤ 16 * width :=
    (natBitLength_mono (recoveryValidatorHandoffOutput_le limits raw)).trans
      hhandoffTrace
  have hswap : recoveryValidatorSwapBits limits raw ≤ 2 * width := by
    have hinput :
        recoveryWitnessValidatorInput limits raw = Nat.pair limitsCode raw :=
      rfl
    simp only [recoveryValidatorSwapBits, hinput, ← hlimitsCode]
    have hleft := natBitLength_pair_le_double hlimits hraw
    have hright := natBitLength_pair_le_double hraw hlimits
    omega
  have henvelopeOutput :
      natBitLength (recoveryEnvelopeOutput raw) ≤ 6 * width :=
    natBitLength_recoveryEnvelopeOutput_le limits raw
  have henvelopeBits : recoveryEnvelopeBits raw ≤ 2 * width + 4 := by
    have hlinear := recoveryEnvelopeBits_le_linear raw
    omega
  have hpreserve :
      preserveRightBits (recoveryEnvelopeBits raw) raw limitsCode
          (recoveryEnvelopeOutput raw) ≤ 16 * width := by
    simp only [preserveRightBits]
    have hpairRaw := natBitLength_pair_le_double hraw hlimits
    have hpairOutput :=
      natBitLength_pair_le_double henvelopeOutput
        (show natBitLength limitsCode ≤ 6 * width by omega)
    omega
  have henvelopeStage :
      recoveryValidatorEnvelopeBits inputLength limits raw ≤
        max (natBitLength inputLength) (16 * width) := by
    simp only [recoveryValidatorEnvelopeBits, ← hlimitsCode]
    omega
  have hnested :
      recoveryValidatorNestedHandoffBits inputLength limits raw ≤
        max (natBitLength inputLength) (16 * width) := by
    simp only [recoveryValidatorNestedHandoffBits]
    omega
  simp only [recoveryValidatorStructuralPrefixBits]
  omega

/-- **The structural prefix, dominated.** -/
theorem recoveryValidatorStructuralPrefixBits_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure lengthCoefficient widthCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hwidth :
      PolyBounded (recoveryValidatorPrefixWidth limits raw) measure
        widthCoefficient degree) :
    PolyBounded (recoveryValidatorStructuralPrefixBits inputLength limits raw)
      measure (max lengthCoefficient (16 * widthCoefficient)) degree :=
  (hlength.max (hwidth.const_mul 16)).mono
    (recoveryValidatorStructuralPrefixBits_le inputLength limits raw)

/-! ## §5 The legal-sum envelope, the dominant stage

`recoveryLegalSumEnvelopeFuel` is a nine-node `linkFuel` chain over ten
sub-stage charges, and `recoveryLegalSumEnvelopeBits` is the matching eleven-way
maximum.  Six of the ten charges — and six of the nine linked programs — are
`private` to `CanonicalRecoveryValidatorProgram`, so a *named* walk of the chain
is not available outside that module.  What is carried here instead is the
chain's algebra, in the exact shape the definition has, plus the reductions for
the sub-stages that are public.

`legalSumChainFuel_polyBounded` is the nine-node instance of
`linkFuel_polyBounded`: a uniform envelope for the ten charges is an envelope
for the chain, at the same degree, with the coefficient
`legalSumEnvelopeCoefficient`.  It is stated over *variables*, so it applies to
the real definition by unification without any private name being written. -/

/-- The coefficient a nine-node linker chain produces from nine program spans
and one uniform stage coefficient.  Stated over variables: the nine spans are
closed natural numbers over composed programs, and this expression is never
evaluated. -/
def legalSumEnvelopeCoefficient
    (firstSpan secondSpan thirdSpan fourthSpan fifthSpan sixthSpan
      seventhSpan eighthSpan ninthSpan stage : ℕ) : ℕ :=
  firstSpan + 5 + stage +
    (secondSpan + 5 + stage +
      (thirdSpan + 5 + stage +
        (fourthSpan + 5 + stage +
          (fifthSpan + 5 + stage +
            (sixthSpan + 5 + stage +
              (seventhSpan + 5 + stage +
                (eighthSpan + 5 + stage +
                  (ninthSpan + 5 + stage + stage))))))))

/-- **The nine-node chain, dominated.**  Exactly the shape
`recoveryLegalSumEnvelopeFuel` has. -/
theorem legalSumChainFuel_polyBounded
    {first second third fourth fifth sixth seventh eighth ninth :
      NPOracleProgram}
    {syntaxFuel boundFuel coefficientLoweringFuel coefficientStageFuel
      circuitLoweringFuel circuitStageFuel bitCapLoweringFuel bitCapStageFuel
      massFuel resourceTailFuel measure stage degree : ℕ}
    (hsyntax : PolyBounded syntaxFuel measure stage degree)
    (hbound : PolyBounded boundFuel measure stage degree)
    (hcoefficientLowering :
      PolyBounded coefficientLoweringFuel measure stage degree)
    (hcoefficientStage : PolyBounded coefficientStageFuel measure stage degree)
    (hcircuitLowering : PolyBounded circuitLoweringFuel measure stage degree)
    (hcircuitStage : PolyBounded circuitStageFuel measure stage degree)
    (hbitCapLowering : PolyBounded bitCapLoweringFuel measure stage degree)
    (hbitCapStage : PolyBounded bitCapStageFuel measure stage degree)
    (hmass : PolyBounded massFuel measure stage degree)
    (hresourceTail : PolyBounded resourceTailFuel measure stage degree) :
    PolyBounded
      (linkFuel first syntaxFuel <|
        linkFuel second boundFuel <|
          linkFuel third coefficientLoweringFuel <|
            linkFuel fourth coefficientStageFuel <|
              linkFuel fifth circuitLoweringFuel <|
                linkFuel sixth circuitStageFuel <|
                  linkFuel seventh bitCapLoweringFuel <|
                    linkFuel eighth bitCapStageFuel <|
                      linkFuel ninth massFuel resourceTailFuel)
      measure
      (legalSumEnvelopeCoefficient (programRegisterSpan first)
        (programRegisterSpan second) (programRegisterSpan third)
        (programRegisterSpan fourth) (programRegisterSpan fifth)
        (programRegisterSpan sixth) (programRegisterSpan seventh)
        (programRegisterSpan eighth) (programRegisterSpan ninth) stage)
      degree :=
  linkFuel_polyBounded hsyntax <|
    linkFuel_polyBounded hbound <|
      linkFuel_polyBounded hcoefficientLowering <|
        linkFuel_polyBounded hcoefficientStage <|
          linkFuel_polyBounded hcircuitLowering <|
            linkFuel_polyBounded hcircuitStage <|
              linkFuel_polyBounded hbitCapLowering <|
                linkFuel_polyBounded hbitCapStage <|
                  linkFuel_polyBounded hmass hresourceTail

/-- The eleven-way maximum the width side of the chain is, dominated. -/
theorem legalSumChainBits_polyBounded
    {length syntaxBits boundBits coefficientLoweringBits coefficientStageBits
      circuitLoweringBits circuitStageBits bitCapLoweringBits bitCapStageBits
      massBits resourceTailBits measure stage degree : ℕ}
    (hlength : PolyBounded length measure stage degree)
    (hsyntax : PolyBounded syntaxBits measure stage degree)
    (hbound : PolyBounded boundBits measure stage degree)
    (hcoefficientLowering :
      PolyBounded coefficientLoweringBits measure stage degree)
    (hcoefficientStage : PolyBounded coefficientStageBits measure stage degree)
    (hcircuitLowering : PolyBounded circuitLoweringBits measure stage degree)
    (hcircuitStage : PolyBounded circuitStageBits measure stage degree)
    (hbitCapLowering : PolyBounded bitCapLoweringBits measure stage degree)
    (hbitCapStage : PolyBounded bitCapStageBits measure stage degree)
    (hmass : PolyBounded massBits measure stage degree)
    (hresourceTail : PolyBounded resourceTailBits measure stage degree) :
    PolyBounded
      (max length <|
        max syntaxBits <|
          max boundBits <|
            max coefficientLoweringBits <|
              max coefficientStageBits <|
                max circuitLoweringBits <|
                  max circuitStageBits <|
                    max bitCapLoweringBits <|
                      max bitCapStageBits <|
                        max massBits resourceTailBits)
      measure stage degree :=
  max_le hlength <| max_le hsyntax <| max_le hbound <|
    max_le hcoefficientLowering <| max_le hcoefficientStage <|
      max_le hcircuitLowering <| max_le hcircuitStage <|
        max_le hbitCapLowering <| max_le hbitCapStage <|
          max_le hmass hresourceTail

/-! ### The public sub-stages of the legal-sum chain

Two of the ten charges are closed numerals; two more are a
context-preserving wrapper around a native call, so §1 applies and both are
degree-preserving over their own list callee. -/

/-- **The term-circuit stage, dominated.**  One native call into the term
circuit list validator, so the stage's degree is the callee's degree. -/
theorem recoveryLegalTermCircuitStageFuel_polyBounded
    {inputLength handoff measure calleeCoefficient degree : ℕ}
    (hcallee :
      PolyBounded
        (recoveryLegalTermCircuitListFuel
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff)) measure
        calleeCoefficient degree) :
    PolyBounded (recoveryLegalTermCircuitStageFuel inputLength handoff) measure
      (nativeCallOverhead recoveryLegalTermCircuitListProgram +
        calleeCoefficient + 4) degree := by
  have hcall :
      PolyBounded
        (nativeCallFuel recoveryLegalTermCircuitListProgram
          (recoveryLegalTermCircuitListFuel
            (recoveryLegalTermCircuitContext handoff)
            (recoveryLegalTermCoefficientMappedCode inputLength handoff))
          (recoveryLegalTermCircuitContext handoff)
          (recoveryLegalTermCoefficientMappedCode inputLength handoff)) measure
        (nativeCallOverhead recoveryLegalTermCircuitListProgram +
          calleeCoefficient) degree :=
    ((polyBounded_const (nativeCallOverhead recoveryLegalTermCircuitListProgram)
      measure degree).add hcallee).mono (nativeCallFuel_le _ _ _ _)
  exact preserveRightFuel_polyBounded hcall

/-- **The term-coefficient stage, dominated.**  A context-preserving wrapper
around the coefficient list validator. -/
theorem recoveryLegalTermCoefficientStageFuel_polyBounded
    {inputLength handoff measure calleeCoefficient degree : ℕ}
    (hcallee :
      PolyBounded
        (recoveryLegalTermCoefficientListFuel inputLength
          (recoveryLegalTermCoefficientTermsCode handoff)) measure
        calleeCoefficient degree) :
    PolyBounded (recoveryLegalTermCoefficientStageFuel inputLength handoff)
      measure (calleeCoefficient + 4) degree :=
  preserveRightFuel_polyBounded hcallee

/-- The mode/raw repackaging stage never widens its handoff by more than one
pairing. -/
theorem recoveryValidatorModeRawBits_le (inputLength handoff : ℕ) :
    recoveryValidatorModeRawBits inputLength handoff ≤
      max (natBitLength inputLength) (2 * natBitLength handoff) := by
  have hleft : natBitLength (Nat.unpair handoff).1 ≤ natBitLength handoff :=
    natBitLength_unpair_left handoff
  have hright : natBitLength (Nat.unpair handoff).2 ≤ natBitLength handoff :=
    natBitLength_unpair_right handoff
  have hraw :
      natBitLength (Nat.unpair (Nat.unpair handoff).2).1 ≤
        natBitLength handoff :=
    (natBitLength_unpair_left _).trans hright
  have houtput :
      natBitLength (recoveryValidatorModeRawOutput handoff) ≤
        2 * natBitLength handoff := by
    have hshape :
        recoveryValidatorModeRawOutput handoff =
          Nat.pair (Nat.unpair handoff).1
            (Nat.unpair (Nat.unpair handoff).2).1 := rfl
    rw [hshape]
    exact natBitLength_pair_le_double hleft hraw
  have hpositive := one_le_natBitLength handoff
  have hledger :
      recoveryValidatorModeRawBits inputLength handoff =
        natBitLength
          ([ inputLength
           , handoff
           , (Nat.unpair handoff).1
           , (Nat.unpair handoff).2
           , (Nat.unpair (Nat.unpair handoff).2).1
           , recoveryValidatorModeRawOutput handoff
           ].foldr max 0) := rfl
  rw [hledger]
  simp only [List.foldr_cons, List.foldr_nil]
  refine natBitLength_max_le (le_max_left _ _) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  refine natBitLength_max_le (by omega) ?_
  have hzero : natBitLength 0 = 1 := by
    simp only [natBitLength, Nat.log_zero_right]
  omega

theorem recoveryValidatorMaximumStageFuel_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure circuitCoefficient resultCoefficient handoffCoefficient
      envelopeCoefficient degree : ℕ}
    (hcircuit :
      PolyBounded
        (booleanCircuitValidationFuel
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput limits raw))
          (handoffOracleCode
            (recoveryValidatorStructuralPrefixOutput limits raw))) measure
        circuitCoefficient degree)
    (hresult :
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput limits raw))) measure
        resultCoefficient degree)
    (hhandoff :
      PolyBounded
        (natBitLength (recoveryValidatorStructuralPrefixOutput limits raw))
        measure handoffCoefficient degree)
    (henvelope :
      PolyBounded
        (recoveryLegalSumEnvelopeFuel inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) measure
        envelopeCoefficient degree) :
    PolyBounded (recoveryValidatorMaximumStageFuel inputLength limits raw)
      measure
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (programRegisterSpan
              (linkPrograms recoveryOracleCallProgram <|
                linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
              recoveryOracleCallLoweringFuel +
            (programRegisterSpan
                (linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
                (nativeContextCallOverhead booleanCircuitValidationProgram +
                  circuitCoefficient) +
              (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
                  recoveryOracleBoundLoweringFuel +
                (36 * max resultCoefficient handoffCoefficient + 24)))) <|
          max envelopeCoefficient recoveryValidatorModeRawFuel)
      degree := by
  have hstructural :
      PolyBounded recoveryValidatorStructuralPrefixFuel measure
        recoveryValidatorStructuralPrefixFuel degree :=
    polyBounded_const _ _ _
  have horacle :=
    recoveryOracleValidationFuel_polyBounded hcircuit hresult hhandoff
  have hmodeRaw :
      PolyBounded recoveryValidatorModeRawFuel measure
        recoveryValidatorModeRawFuel degree := polyBounded_const _ _ _
  exact hstructural.max (horacle.max (henvelope.max hmodeRaw))

theorem recoveryValidatorMaximumStageBits_polyBounded
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure lengthCoefficient prefixCoefficient stageCoefficient
      callCoefficient envelopeCoefficient modeCoefficient degree : ℕ}
    (hlength :
      PolyBounded (natBitLength inputLength) measure lengthCoefficient degree)
    (hprefix :
      PolyBounded (recoveryValidatorPrefixWidth limits raw) measure
        prefixCoefficient degree)
    (hstage :
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput limits raw)) measure
        stageCoefficient degree)
    (hcall :
      PolyBounded
        (recoveryOracleCallBits inputLength
          (recoveryValidatorStructuralPrefixOutput limits raw)) measure
        callCoefficient degree)
    (henvelope :
      PolyBounded
        (recoveryLegalSumEnvelopeBits inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) measure
        envelopeCoefficient degree)
    (hmode :
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
        measure modeCoefficient degree) :
    PolyBounded (recoveryValidatorMaximumStageBits inputLength limits raw)
      measure
      (max lengthCoefficient <|
        max (max lengthCoefficient (16 * prefixCoefficient)) <|
          max (max (max lengthCoefficient (4 * stageCoefficient))
            callCoefficient) <|
            max envelopeCoefficient
              (max lengthCoefficient (2 * modeCoefficient)))
      degree := by
  have hprefixBits :=
    recoveryValidatorStructuralPrefixBits_polyBounded hlength hprefix
  have horacleBits :=
    recoveryOracleValidationBits_polyBounded hlength hstage hcall
  have hmodeBits :
      PolyBounded
        (recoveryValidatorModeRawBits inputLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
        measure (max lengthCoefficient (2 * modeCoefficient)) degree :=
    (hlength.max (hmode.const_mul 2)).mono
      (recoveryValidatorModeRawBits_le inputLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
  exact hlength.max (hprefixBits.max (horacleBits.max
    (henvelope.max hmodeBits)))

/-- The fuel-side stage coefficient produced by §6 at a uniform residual
envelope. -/
theorem recoveryValidatorMaximumStageFuel_polyBounded_uniform
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure frontier stageCoefficient degree : ℕ}
    (hcoefficient :
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (programRegisterSpan
              (linkPrograms recoveryOracleCallProgram <|
                linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
              recoveryOracleCallLoweringFuel +
            (programRegisterSpan
                (linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
                (nativeContextCallOverhead booleanCircuitValidationProgram +
                  frontier) +
              (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
                  recoveryOracleBoundLoweringFuel +
                (36 * max frontier frontier + 24)))) <|
          max frontier recoveryValidatorModeRawFuel) ≤ stageCoefficient)
    (hcircuit :
      PolyBounded
        (booleanCircuitValidationFuel
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput limits raw))
          (handoffOracleCode
            (recoveryValidatorStructuralPrefixOutput limits raw))) measure
        frontier degree)
    (hresult :
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput limits raw))) measure
        frontier degree)
    (hhandoff :
      PolyBounded
        (natBitLength (recoveryValidatorStructuralPrefixOutput limits raw))
        measure frontier degree)
    (henvelope :
      PolyBounded
        (recoveryLegalSumEnvelopeFuel inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) measure frontier
        degree) :
    PolyBounded (recoveryValidatorMaximumStageFuel inputLength limits raw)
      measure stageCoefficient degree :=
  (recoveryValidatorMaximumStageFuel_polyBounded hcircuit hresult hhandoff
    henvelope).coefficient_mono hcoefficient

/-- The width-side stage coefficient produced by §6 at a uniform residual
envelope. -/
theorem recoveryValidatorMaximumStageBits_polyBounded_uniform
    {inputLength : ℕ} {limits : RecoveryWitnessLimits}
    {raw measure frontier stageCoefficient degree : ℕ}
    (hcoefficient :
      (max frontier <|
        max (max frontier (16 * frontier)) <|
          max (max (max frontier (4 * frontier)) frontier) <|
            max frontier (max frontier (2 * frontier))) ≤ stageCoefficient)
    (hlength :
      PolyBounded (natBitLength inputLength) measure frontier degree)
    (hprefix :
      PolyBounded (recoveryValidatorPrefixWidth limits raw) measure frontier
        degree)
    (hstage :
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput limits raw)) measure
        frontier degree)
    (hcall :
      PolyBounded
        (recoveryOracleCallBits inputLength
          (recoveryValidatorStructuralPrefixOutput limits raw)) measure
        frontier degree)
    (henvelope :
      PolyBounded
        (recoveryLegalSumEnvelopeBits inputLength
          (recoveryValidatorOraclePrefixOutput limits raw)) measure frontier
        degree)
    (hmode :
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
        measure frontier degree) :
    PolyBounded (recoveryValidatorMaximumStageBits inputLength limits raw)
      measure stageCoefficient degree :=
  (recoveryValidatorMaximumStageBits_polyBounded hlength hprefix hstage hcall
    henvelope hmode).coefficient_mono hcoefficient

theorem hvalidatorFuel_of_frontier
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (frontier stageCoefficient degree : ℕ)
    (hdegree : degree ≤ recoveryVerifierDegree)
    (hcoefficient :
      (max recoveryValidatorStructuralPrefixFuel <|
        max
          (programRegisterSpan
              (linkPrograms recoveryOracleCallProgram <|
                linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
              recoveryOracleCallLoweringFuel +
            (programRegisterSpan
                (linkPrograms recoveryOracleBoundLoweringProgram
                  recoveryBoundedContextCheckProgram) + 5 +
                (nativeContextCallOverhead booleanCircuitValidationProgram +
                  frontier) +
              (programRegisterSpan recoveryBoundedContextCheckProgram + 5 +
                  recoveryOracleBoundLoweringFuel +
                (36 * max frontier frontier + 24)))) <|
          max frontier recoveryValidatorModeRawFuel) ≤ stageCoefficient)
    (hcircuit : ∀ request : WeakVerifierRequest,
      PolyBounded
        (booleanCircuitValidationFuel
          (handoffOracleArity
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness)))
          (handoffOracleCode
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness))))
        request.measure frontier degree)
    (hresult : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryOracleValidationResult
            (recoveryValidatorStructuralPrefixOutput
              (limitsOf request.inputArity) (encodeBitInput request.witness))))
        request.measure frontier degree)
    (hhandoff : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier degree)
    (henvelope : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeFuel (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput (limitsOf request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (request : WeakVerifierRequest) :
    recoveryWitnessValidatorFuel (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget
        (programRegisterSpan recoveryValidatorModeRawProgram + 5 +
          (programRegisterSpan recoveryLegalSumEnvelopeProgram + 5 +
            (programRegisterSpan recoveryOracleValidationProgram + 5 +
              stageCoefficient + stageCoefficient) +
            stageCoefficient) +
          stageCoefficient)
        recoveryVerifierDegree request.measure :=
  hvalidatorFuel_of_stageFuel limitsOf stageCoefficient degree hdegree
    (fun request =>
      recoveryValidatorMaximumStageFuel_polyBounded_uniform hcoefficient
        (hcircuit request) (hresult request) (hhandoff request)
        (henvelope request))
    request

theorem hvalidatorBits_of_frontier
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (frontier stageCoefficient degree : ℕ)
    (hdegree : degree ≤ recoveryVerifierDegree)
    (hcoefficient :
      (max frontier <|
        max (max frontier (16 * frontier)) <|
          max (max (max frontier (4 * frontier)) frontier) <|
            max frontier (max frontier (2 * frontier))) ≤ stageCoefficient)
    (hlength : ∀ request : WeakVerifierRequest,
      PolyBounded (natBitLength (WeakVerifierRequest.length request))
        request.measure frontier degree)
    (hprefix : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryValidatorPrefixWidth (limitsOf request.inputArity)
          (encodeBitInput request.witness)) request.measure frontier degree)
    (hstage : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleStageWidth
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hcall : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryOracleCallBits (WeakVerifierRequest.length request)
          (recoveryValidatorStructuralPrefixOutput
            (limitsOf request.inputArity) (encodeBitInput request.witness)))
        request.measure frontier degree)
    (henvelope : ∀ request : WeakVerifierRequest,
      PolyBounded
        (recoveryLegalSumEnvelopeBits (WeakVerifierRequest.length request)
          (recoveryValidatorOraclePrefixOutput (limitsOf request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (hmode : ∀ request : WeakVerifierRequest,
      PolyBounded
        (natBitLength
          (recoveryValidatorLegalSumPrefixOutput
            (WeakVerifierRequest.length request) (limitsOf request.inputArity)
            (encodeBitInput request.witness)))
        request.measure frontier degree)
    (request : WeakVerifierRequest) :
    recoveryWitnessValidatorBits (WeakVerifierRequest.length request)
        (limitsOf request.inputArity) (encodeBitInput request.witness) ≤
      polynomialBudget stageCoefficient recoveryVerifierDegree
        request.measure :=
  hvalidatorBits_of_stageBits limitsOf stageCoefficient degree hdegree
    (fun request =>
      recoveryValidatorMaximumStageBits_polyBounded_uniform hcoefficient
        (hlength request) (hprefix request) (hstage request) (hcall request)
        (henvelope request) (hmode request))
    request

/-- The public input length is measure-linear. -/
theorem polyBounded_requestLengthWidth (request : WeakVerifierRequest) :
    PolyBounded (natBitLength (WeakVerifierRequest.length request))
      request.measure 4 1 := by
  have hcode := weakVerifierRequest_codeBits_le request
  have hlength :
      WeakVerifierRequest.length request ≤ WeakVerifierRequest.code request := by
    simp only [WeakVerifierRequest.length, WeakVerifierRequest.code]
    exact Nat.left_le_pair _ _
  have hwidth :
      natBitLength (WeakVerifierRequest.length request) ≤
        natBitLength (WeakVerifierRequest.code request) :=
    natBitLength_mono hlength
  change natBitLength (WeakVerifierRequest.length request) ≤
    4 * (request.measure + 1) ^ 1
  rw [pow_one]
  omega

/-- The raw witness code is measure-linear: this is the degree-`1` anchor of
the whole stage walk. -/
theorem polyBounded_witnessWidth (request : WeakVerifierRequest) :
    PolyBounded (natBitLength (encodeBitInput request.witness))
      request.measure 4 1 := by
  have hcode := weakVerifierRequest_codeBits_le request
  have hwitness :
      encodeBitInput request.witness ≤ WeakVerifierRequest.code request := by
    simp only [WeakVerifierRequest.code]
    exact (Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)
  have hwidth :
      natBitLength (encodeBitInput request.witness) ≤
        natBitLength (WeakVerifierRequest.code request) :=
    natBitLength_mono hwitness
  change natBitLength (encodeBitInput request.witness) ≤
    4 * (request.measure + 1) ^ 1
  rw [pow_one]
  omega

/-- **The structural prefix's width parameter, anchored.**  Only the serialized
policy record's width is left, and §4 of the domination module bounds it for the
computable limits family. -/
theorem polyBounded_recoveryValidatorPrefixWidth
    {limits : RecoveryWitnessLimits} {policyCoefficient : ℕ}
    (request : WeakVerifierRequest)
    (hpolicy :
      PolyBounded (natBitLength (encodeRecoveryWitnessLimits limits))
        request.measure policyCoefficient 1) :
    PolyBounded
      (recoveryValidatorPrefixWidth limits (encodeBitInput request.witness))
      request.measure (max 4 policyCoefficient) 1 :=
  (polyBounded_witnessWidth request).max hpolicy

end NearCubicWires.ValidatorStageEnvelopes
