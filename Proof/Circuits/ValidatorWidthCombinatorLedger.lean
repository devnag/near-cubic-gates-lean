import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorOracleCallWidth

/-!
# The tree's canonical combinator width ledger

`ValidatorOracleCallWidth` §1 opened this ledger with the native contextual
call.  Every remaining validator width obligation is a maximum over the same
handful of shapes, so this module states each shape **once**, over variables:
no register span, no decoded magnitude, no counted collection appears in any
statement here.

* §1 the two primitives — a pairing doubles a width bound, and a `foldr max`
  over a width cone is the cone's bound.

* §2 the wrapper shapes: `swapPairBits`, `preserveRightBits`, `pairedCallBits`,
  `forkCallBits`.

* §3 the iterated pairing `pairIter`, which is the tagged tuple's width.

Every entry is stated as `… ≤ max <callee widths> (k * bound)` with `k` a closed
numeral, so a consumer discharges it by exhibiting one width cone and reading
off the callee.
-/

namespace NearCubicWires.ValidatorWidthCombinatorLedger

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorLeafWidthCore

open private forkTaggedInputBits forkFirstChoiceBits forkSecondChoiceBits
  forkPairedBits from Proof.Circuits.CanonicalForkCall

open private nativeNatEqRequestBits nativeNatEqCompareInput
  nativeNatEqCompareBits nativeNatEqCoreBits nativeNatEqGateBits from
  Proof.MachineModel.CanonicalNativeEqualityProgram

open private nativeCallBits_le from Proof.Circuits.ValidatorOracleCallWidth

/-! ## §1 The two primitives -/

/-- **A pairing doubles a width bound.**  The one rule every other entry in
this ledger is built from. -/
theorem natBitLength_pair_le_two_mul {left right bound : ℕ}
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound) :
    natBitLength (Nat.pair left right) ≤ 2 * bound := by
  have hbound := pairCodeBits_le left right
  omega

/-- **A width cone's `foldr max` is the cone's bound.**  Every `…Bits` in the
tree that is written as a maximum over an explicit list of trace values has
this shape. -/
theorem foldr_max_map_natBitLength_le {values : List ℕ} {init bound : ℕ}
    (hinit : init ≤ bound)
    (hvalues : ∀ value ∈ values, natBitLength value ≤ bound) :
    (values.map natBitLength).foldr max init ≤ bound := by
  induction values with
  | nil => simpa using hinit
  | cons head rest ih =>
      have hhead : natBitLength head ≤ bound := hvalues head (by simp)
      have hrest : ∀ value ∈ rest, natBitLength value ≤ bound := by
        intro value hvalue
        exact hvalues value (by simp [hvalue])
      have htail := ih hrest
      simp only [List.map_cons, List.foldr_cons]
      omega

/-! ## §2 The wrapper shapes -/

/-- **The swap adapter's width.** -/
theorem swapPairBits_le {left right bound : ℕ}
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound) :
    swapPairBits left right ≤ 2 * bound := by
  have hforward := natBitLength_pair_le_two_mul hleft hright
  have hbackward := natBitLength_pair_le_two_mul hright hleft
  simp only [swapPairBits]
  omega

/-- **The context-preserving wrapper's width.**  The callee's own width, or
twice the widest datum it carries past. -/
theorem preserveRightBits_le {sourceBits left right output bound : ℕ}
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound)
    (houtput : natBitLength output ≤ bound) :
    preserveRightBits sourceBits left right output ≤
      max sourceBits (2 * bound) := by
  have hinput := natBitLength_pair_le_two_mul hleft hright
  have hexit := natBitLength_pair_le_two_mul houtput hright
  simp only [preserveRightBits]
  omega

/-- **The paired call's width.**  Two callee widths and one cone. -/
theorem pairedCallBits_le
    {inputLength leftBits rightBits left right leftOutput rightOutput
      bound : ℕ}
    (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound)
    (hleftOutput : natBitLength leftOutput ≤ bound)
    (hrightOutput : natBitLength rightOutput ≤ bound) :
    pairedCallBits inputLength leftBits rightBits left right leftOutput
        rightOutput ≤ max (max leftBits rightBits) (2 * bound) := by
  have hfirst :=
    preserveRightBits_le (sourceBits := leftBits) hleft hright hleftOutput
  have hsecond :=
    preserveRightBits_le (sourceBits := rightBits) hright hleftOutput
      hrightOutput
  have hswapLeft := swapPairBits_le hleftOutput hright
  have hswapRight := swapPairBits_le hrightOutput hleftOutput
  simp only [pairedCallBits]
  omega

/-- **The fork call's width.**  Two callee widths and four copies of the
cone: the fork tags its input twice and pairs the two tagged copies. -/
theorem forkCallBits_le
    {inputLength raw firstBits secondBits firstOutput secondOutput bound : ℕ}
    (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hraw : natBitLength raw ≤ bound)
    (hfirstOutput : natBitLength firstOutput ≤ bound)
    (hsecondOutput : natBitLength secondOutput ≤ bound) :
    forkCallBits inputLength raw firstBits secondBits firstOutput
        secondOutput ≤ max (max firstBits secondBits) (4 * bound) := by
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hfirstTag : natBitLength (Nat.pair 0 raw) ≤ 2 * bound :=
    natBitLength_pair_le_two_mul (by omega) hraw
  have hsecondTag : natBitLength (Nat.pair 1 raw) ≤ 2 * bound :=
    natBitLength_pair_le_two_mul (by omega) hraw
  have htagged : natBitLength (forkTaggedInput raw) ≤ 4 * bound := by
    have hpair := natBitLength_pair_le_two_mul hfirstTag hsecondTag
    simp only [forkTaggedInput]
    omega
  have hinput : forkTaggedInputBits raw ≤ 4 * bound := by
    simp only [forkTaggedInputBits]
    omega
  have hfirstRequest :
      natBitLength (Nat.pair inputLength (Nat.pair 0 raw)) ≤ 2 * (2 * bound) :=
    natBitLength_pair_le_two_mul (by omega) hfirstTag
  have hsecondRequest :
      natBitLength (Nat.pair inputLength (Nat.pair 1 raw)) ≤ 2 * (2 * bound) :=
    natBitLength_pair_le_two_mul (by omega) hsecondTag
  have hfirstChoice :
      forkFirstChoiceBits inputLength raw firstBits firstOutput ≤
        max firstBits (4 * bound) := by
    simp only [forkFirstChoiceBits]
    omega
  have hsecondChoice :
      forkSecondChoiceBits inputLength raw secondBits secondOutput ≤
        max secondBits (4 * bound) := by
    simp only [forkSecondChoiceBits]
    omega
  have hpaired :=
    pairedCallBits_le
      (inputLength := inputLength)
      (leftBits := forkFirstChoiceBits inputLength raw firstBits firstOutput)
      (rightBits := forkSecondChoiceBits inputLength raw secondBits secondOutput)
      (left := Nat.pair 0 raw) (right := Nat.pair 1 raw)
      (leftOutput := firstOutput) (rightOutput := secondOutput)
      (bound := 2 * bound) (by omega) (by omega) hfirstTag hsecondTag
      (by omega) (by omega)
  have hforkPaired :
      forkPairedBits inputLength raw firstBits secondBits firstOutput
          secondOutput ≤ max (max firstBits secondBits) (4 * bound) := by
    simp only [forkPairedBits]
    omega
  simp only [forkCallBits]
  omega

/-! ## §3 The iterated pairing -/

/-- **The iterated pairing's width.**  `pairIter` is the tagged tuple's
encoding shape: `depth` doublings of the seed's width. -/
theorem natBitLength_pairIter_le (depth value : ℕ) :
    natBitLength (pairIter depth value) ≤ 2 ^ depth * natBitLength value := by
  induction depth generalizing value with
  | zero => simp
  | succ depth ih =>
      have hstep := ih (Nat.pair value value)
      have hpair := pairCodeBits_le value value
      have hmonotone :
          2 ^ depth * natBitLength (Nat.pair value value) ≤
            2 ^ depth * (2 * natBitLength value) := by
        exact Nat.mul_le_mul_left _ (by omega)
      have hrewrite :
          2 ^ depth * (2 * natBitLength value) =
            2 ^ (depth + 1) * natBitLength value := by
        rw [pow_succ]
        ring
      rw [pairIter_succ]
      omega

/-- The width of a maximum is the maximum of the widths. -/
theorem natBitLength_max_le (left right : ℕ) :
    natBitLength (max left right) ≤
      max (natBitLength left) (natBitLength right) := by
  rcases le_total left right with hle | hle
  · have := ValidatorLeafWidthCore.natBitLength_mono hle
    simp only [max_eq_right hle]
    omega
  · have := ValidatorLeafWidthCore.natBitLength_mono hle
    simp only [max_eq_left hle]
    omega

/-- **The tagged tuple's width.**  One `pairIter` at depth `arity + 1`. -/
theorem taggedTupleBits_le {inputLength arity raw bound : ℕ}
    (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (harity : natBitLength arity ≤ bound)
    (hraw : natBitLength raw ≤ bound) :
    taggedTupleBits inputLength arity raw ≤ 2 ^ (arity + 1) * bound := by
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hinner : natBitLength (max 1 (max inputLength (max arity raw))) ≤ bound := by
    have h₁ := natBitLength_max_le arity raw
    have h₂ := natBitLength_max_le inputLength (max arity raw)
    have h₃ := natBitLength_max_le 1 (max inputLength (max arity raw))
    omega
  have hiter :=
    natBitLength_pairIter_le (arity + 1) (max 1 (max inputLength (max arity raw)))
  have hscale :
      2 ^ (arity + 1) *
          natBitLength (max 1 (max inputLength (max arity raw))) ≤
        2 ^ (arity + 1) * bound :=
    Nat.mul_le_mul_left _ hinner
  simp only [taggedTupleBits]
  omega

/-- **The native comparison's width.** -/
theorem nativeNatLeBits_le {left right bound : ℕ}
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound) :
    nativeNatLeBits left right ≤ 2 * bound := by
  simp only [nativeNatLeBits, nativeNatLeInput]
  exact natBitLength_pair_le_two_mul hleft hright

/-- The comparator's Boolean answer is one bit wide. -/
theorem natBitLength_nativeNatLeOutput_le (left right : ℕ) :
    natBitLength (nativeNatLeOutput left right) ≤ 1 := by
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  rw [nativeNatLeOutput_eq]
  rcases Nat.decLe left right with hle | hle <;> simp_all

/-- **The native equality's width.**  Two comparator calls under a paired
call, so four copies of the cone. -/
theorem nativeNatEqBits_le {inputLength left right bound : ℕ}
    (hpositive : 1 ≤ bound)
    (hlength : natBitLength inputLength ≤ bound)
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound) :
    nativeNatEqBits inputLength left right ≤ 4 * bound := by
  have hforward : natBitLength (nativeNatLeInput left right) ≤ 2 * bound :=
    natBitLength_pair_le_two_mul hleft hright
  have hbackward : natBitLength (nativeNatLeInput right left) ≤ 2 * bound :=
    natBitLength_pair_le_two_mul hright hleft
  have hrequest : nativeNatEqRequestBits left right ≤ 4 * bound := by
    have hinput : natBitLength (nativeNatEqInput left right) ≤ 2 * bound :=
      natBitLength_pair_le_two_mul hleft hright
    have hcompare :
        natBitLength (nativeNatEqCompareInput left right) ≤ 2 * (2 * bound) := by
      simp only [nativeNatEqCompareInput]
      exact natBitLength_pair_le_two_mul hforward hbackward
    simp only [nativeNatEqRequestBits]
    omega
  have hleftFlag := natBitLength_nativeNatLeOutput_le left right
  have hrightFlag := natBitLength_nativeNatLeOutput_le right left
  have hcompare :=
    pairedCallBits_le (inputLength := inputLength)
      (leftBits := nativeNatLeBits left right)
      (rightBits := nativeNatLeBits right left)
      (left := nativeNatLeInput left right)
      (right := nativeNatLeInput right left)
      (leftOutput := nativeNatLeOutput left right)
      (rightOutput := nativeNatLeOutput right left) (bound := 2 * bound)
      (by omega) (by omega) hforward hbackward (by omega) (by omega)
  have hleftBits := nativeNatLeBits_le hleft hright
  have hrightBits := nativeNatLeBits_le hright hleft
  have hgate :
      nativeNatEqGateBits (nativeNatLeOutput left right)
          (nativeNatLeOutput right left) ≤ 4 * bound := by
    have hpair :=
      natBitLength_pair_le_two_mul (bound := bound) (by omega) (by omega)
        (left := nativeNatLeOutput left right)
        (right := nativeNatLeOutput right left)
    simp only [nativeNatEqGateBits]
    omega
  have hcore :
      nativeNatEqCoreBits inputLength left right ≤ 4 * bound := by
    simp only [nativeNatEqCoreBits, nativeNatEqCompareBits]
    omega
  simp only [nativeNatEqBits]
  omega

/-- **The binary strict comparator's width.** -/
theorem binaryNatLtBits_le {left right bound : ℕ}
    (_hpositive : 1 ≤ bound)
    (hleft : natBitLength left ≤ bound) (hright : natBitLength right ≤ bound) :
    binaryNatLtBits left right ≤ 2 * bound + 2 := by
  have hsucc : natBitLength (left + 1) ≤ natBitLength left + 1 := by
    have hmono : Nat.log 2 left ≤ Nat.log 2 (left + 1) :=
      Nat.log_mono_right (by omega)
    have hbound : Nat.log 2 (left + 1) ≤ Nat.log 2 left + 1 := by
      rcases Nat.eq_zero_or_pos left with rfl | hpos
      · norm_num
      · have hlt : left + 1 < 2 ^ (Nat.log 2 left + 1 + 1) := by
          have := Nat.lt_pow_succ_log_self (b := 2) (by omega) left
          have hpow : (2 : ℕ) ^ (Nat.log 2 left + 1) <
              2 ^ (Nat.log 2 left + 1 + 1) := by
            exact Nat.pow_lt_pow_right (by omega) (by omega)
          omega
        exact Nat.le_of_lt_succ
          (Nat.log_lt_of_lt_pow (by omega) hlt)
    simp only [natBitLength]
    omega
  have hle := nativeNatLeBits_le (bound := bound + 1)
    (left := left + 1) (right := right) (by omega) (by omega)
  simp only [binaryNatLtBits]
  omega

/-- **The native strict comparison request's width.**  A native call whose
callee is the binary comparator; both close at four copies of the cone. -/
theorem nativeLtRequestBits_le {outerInputLength request bound : ℕ}
    (hpositive : 1 ≤ bound)
    (houter : natBitLength outerInputLength ≤ bound)
    (hrequest : natBitLength request ≤ bound) :
    nativeLtRequestBits outerInputLength request ≤ 4 * bound := by
  have hleft : natBitLength (Nat.unpair request).2 ≤ bound :=
    le_trans
      (ValidatorLeafWidthCore.natBitLength_mono (Nat.unpair_right_le request))
      hrequest
  have hright : natBitLength (Nat.unpair request).1 ≤ bound :=
    le_trans
      (ValidatorLeafWidthCore.natBitLength_mono (Nat.unpair_left_le request))
      hrequest
  have hzero : natBitLength 0 = 1 := natBitLength_zero
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hflag :
      natBitLength
          (decide ((Nat.unpair request).2 < (Nat.unpair request).1)).toNat ≤
        bound := by
    rcases Nat.decLt (Nat.unpair request).2 (Nat.unpair request).1 with hlt | hlt <;>
      simp_all
  have hcallee :=
    binaryNatLtBits_le (bound := bound) hpositive hleft hright
  have hcall :=
    nativeCallBits_le outerInputLength (Nat.unpair request).1
      (Nat.unpair request).2
      (decide ((Nat.unpair request).2 < (Nat.unpair request).1)).toNat
      (binaryNatLtBits (Nat.unpair request).2 (Nat.unpair request).1) bound
      hpositive houter hright hleft hflag
  simp only [nativeLtRequestBits]
  omega

end NearCubicWires.ValidatorWidthCombinatorLedger
