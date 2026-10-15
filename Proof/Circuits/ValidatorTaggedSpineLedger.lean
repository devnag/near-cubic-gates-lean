import Proof.MachineModel.CanonicalTaggedNatListValidationProgram
import Proof.Circuits.ValidatorCircuitStageWidths

/-!
# The tagged spine's width ledger

`ValidatorCircuitStageWidths` §3 left the Boolean circuit validator with exactly
two fuel charges, and named the single missing ledger each of them needs.  The
first — `booleanCircuitPreparationFuel`, through the node batch and the node
validator, down to `taggedListValidationFuel` — needs a fact that exists nowhere
in the tree:

> a `Nat.unpair` projection is **half** as wide as the code it is taken from.

`ValidatorLeafWidthCore` §6 proves the pairing side of this
(`two_mul_natBitLength_max_le_natBitLength_pair`: a pairing at least *doubles*
the width) and spends it on the structural parse's height.  The projection side
is the same fact read through `Nat.pair_unpair`, and it is what every
`Nat.unpair`-recursive charge in the tagged cone is paid from.  §1 states it as
a standalone ledger, in both projections and in both the coarse (monotone) and
the sharp (halving) form.

* §1 the `Nat.unpair` width ledger.

* §2 spends it on `taggedListValidationFuel`, the tagged spine's structural
  walk: its recursion peels **two** pairings per step, so the width drops by a
  factor of four and the whole walk is *width-linear* — in fact logarithmic, but
  linear is what the domination algebra consumes.

* §3 supplies the matching *counting* ledger for the tagged codec, which nothing
  in the tree published either: a decoded tagged record has at most
  `natBitLength code − 1` fields, and every one of them is no wider than the
  code.  These are the two facts the batch's counted call over
  `taggedNatFieldCodes` is charged against — the exact analogue, for the tagged
  codec, of what `ValidatorLeafWidthCore` §2 and §4 are for the balanced one.
-/

namespace NearCubicWires.ValidatorTaggedSpineLedger

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTaggedListValidationProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.ValidatorLeafWidthCore

/-! ## §1 The `Nat.unpair` width ledger

`Nat.pair_unpair` turns `ValidatorLeafWidthCore` §6's pairing rule into a
statement about the projections: since the pairing of the two halves *is* the
code, each half is at most half as wide, up to the one bit the rule loses. -/

/-- A projection is no wider than the code — the coarse form. -/
theorem natBitLength_unpair_fst_le (code : ℕ) :
    natBitLength (Nat.unpair code).1 ≤ natBitLength code :=
  natBitLength_mono (Nat.unpair_left_le code)

theorem natBitLength_unpair_snd_le (code : ℕ) :
    natBitLength (Nat.unpair code).2 ≤ natBitLength code :=
  natBitLength_mono (Nat.unpair_right_le code)

/-- **The halving ledger.**  A projection is at most *half* as wide as the code,
because the pairing that rebuilds the code doubles the wider half's width. -/
theorem two_mul_natBitLength_unpair_max_le (code : ℕ) :
    2 * natBitLength (max (Nat.unpair code).1 (Nat.unpair code).2) ≤
      natBitLength code + 1 := by
  have hpair :=
    two_mul_natBitLength_max_le_natBitLength_pair (Nat.unpair code).1
      (Nat.unpair code).2
  rwa [Nat.pair_unpair] at hpair

theorem two_mul_natBitLength_unpair_fst_le (code : ℕ) :
    2 * natBitLength (Nat.unpair code).1 ≤ natBitLength code + 1 := by
  have hmax := two_mul_natBitLength_unpair_max_le code
  have hproject :
      natBitLength (Nat.unpair code).1 ≤
        natBitLength (max (Nat.unpair code).1 (Nat.unpair code).2) :=
    natBitLength_mono (le_max_left _ _)
  omega

theorem two_mul_natBitLength_unpair_snd_le (code : ℕ) :
    2 * natBitLength (Nat.unpair code).2 ≤ natBitLength code + 1 := by
  have hmax := two_mul_natBitLength_unpair_max_le code
  have hproject :
      natBitLength (Nat.unpair code).2 ≤
        natBitLength (max (Nat.unpair code).1 (Nat.unpair code).2) :=
    natBitLength_mono (le_max_right _ _)
  omega

/-! ## §2 The tagged spine's structural walk

`taggedListValidationFuel` recurses on `code ↦ (Nat.unpair (Nat.unpair code).2).2`
and charges seven per cell.  Two projections per step means a factor of four in
the width per step, so the depth is logarithmic and the charge is well inside
width-linear.  The only delicate point is the shortest cell: a code whose tag
projection is `1` is at least `2`, so its width is at least `2`, and that is
what keeps the very first step inside the budget. -/

private theorem taggedListValidationFuel_zero :
    taggedListValidationFuel 0 = 3 := by
  rw [taggedListValidationFuel]
  simp

/-- **The tagged spine's ledger.**  Width-linear, from the halving step. -/
theorem taggedListValidationFuel_le (code : ℕ) :
    taggedListValidationFuel code ≤ 7 * natBitLength code + 7 := by
  induction code using Nat.strong_induction_on with
  | h code inductionHypothesis =>
      have hwidth := one_le_natBitLength code
      rw [taggedListValidationFuel]
      split
      · omega
      · dsimp only
        split
        · omega
        · split
          · rename_i htag
            have hsum : (Nat.unpair code).1 + (Nat.unpair code).2 ≤ code :=
              Nat.unpair_add_le code
            rcases Nat.eq_zero_or_pos (Nat.unpair code).2 with
              hpayload | hpayload
            · have htail : (Nat.unpair (Nat.unpair code).2).2 = 0 := by
                rw [hpayload, Nat.unpair_zero]
                rfl
              rw [htail, taggedListValidationFuel_zero]
              omega
            · have hinner := Nat.unpair_right_le (Nat.unpair code).2
              have hlt : (Nat.unpair (Nat.unpair code).2).2 < code := by omega
              have hrec := inductionHypothesis _ hlt
              have hcodeWidth : 2 ≤ natBitLength code :=
                two_le_natBitLength (by omega)
              have houter := two_mul_natBitLength_unpair_snd_le code
              have hinnerHalf :=
                two_mul_natBitLength_unpair_snd_le (Nat.unpair code).2
              have htailWidth :=
                one_le_natBitLength (Nat.unpair (Nat.unpair code).2).2
              omega
          · omega

/-! ## §3 The tagged codec's counting ledger

The balanced codec has both halves of its ledger published — the decoded list's
length (`ValidatorLeafWidthCore` §2) and the decoded atoms' widths (§4).  The
tagged codec has neither.  Both follow from the same two facts as §2: a cell is
a pairing of the payload with the tail, and `decodeTaggedList` only accepts
codes it re-encodes exactly. -/

private theorem two_le_pair_one (value : ℕ) : 2 ≤ Nat.pair 1 value := by
  have hpair :
      Nat.pair 1 value =
        if 1 < value then value * value + 1 else 1 * 1 + 1 + value := rfl
  rcases Nat.lt_or_ge 1 value with hlt | hge
  · have hge2 : 2 ≤ value := hlt
    have hsquare : 2 * 2 ≤ value * value := Nat.mul_le_mul hge2 hge2
    rw [hpair, if_pos hlt]
    omega
  · rw [hpair, if_neg (by omega : ¬ 1 < value)]
    omega

theorem le_of_mem_encodeTaggedList :
    ∀ (values : List ℕ) (value : ℕ), value ∈ values →
      value ≤ encodeTaggedList values := by
  intro values
  induction values with
  | nil =>
      intro value hvalue
      simp at hvalue
  | cons head rest inductionHypothesis =>
      intro value hvalue
      have hcell :
          Nat.pair head (encodeTaggedList rest) ≤
            encodeTaggedList (head :: rest) :=
        Nat.right_le_pair 1 (Nat.pair head (encodeTaggedList rest))
      have hhead : head ≤ Nat.pair head (encodeTaggedList rest) :=
        Nat.left_le_pair _ _
      have htail :
          encodeTaggedList rest ≤ Nat.pair head (encodeTaggedList rest) :=
        Nat.right_le_pair _ _
      rcases List.mem_cons.mp hvalue with rfl | hrest
      · omega
      · have hmember := inductionHypothesis value hrest
        omega

/-- **The tagged counting ledger.**  A tagged record with `n` fields is at least
`n + 1` bits wide: each cell is two pairings, and a pairing doubles. -/
theorem encodeTaggedList_length_succ_le (values : List ℕ) :
    values.length + 1 ≤ natBitLength (encodeTaggedList values) := by
  induction values with
  | nil =>
      have hzero : encodeTaggedList ([] : List ℕ) = 0 := rfl
      rw [hzero, natBitLength_zero]
      simp
  | cons head rest inductionHypothesis =>
      have hcode :
          encodeTaggedList (head :: rest) =
            Nat.pair 1 (Nat.pair head (encodeTaggedList rest)) := rfl
      have houter :
          2 * natBitLength
              (max 1 (Nat.pair head (encodeTaggedList rest))) ≤
            natBitLength (encodeTaggedList (head :: rest)) + 1 := by
        rw [hcode]
        exact two_mul_natBitLength_max_le_natBitLength_pair 1
          (Nat.pair head (encodeTaggedList rest))
      have houterProject :
          natBitLength (Nat.pair head (encodeTaggedList rest)) ≤
            natBitLength (max 1 (Nat.pair head (encodeTaggedList rest))) :=
        natBitLength_mono (le_max_right _ _)
      have hinner :=
        two_mul_natBitLength_max_le_natBitLength_pair head
          (encodeTaggedList rest)
      have hinnerProject :
          natBitLength (encodeTaggedList rest) ≤
            natBitLength (max head (encodeTaggedList rest)) :=
        natBitLength_mono (le_max_right _ _)
      have htailWidth := one_le_natBitLength (encodeTaggedList rest)
      have hcellTwo : 2 ≤ encodeTaggedList (head :: rest) := by
        rw [hcode]
        exact two_le_pair_one _
      have hcellWidth : 2 ≤ natBitLength (encodeTaggedList (head :: rest)) :=
        two_le_natBitLength hcellTwo
      simp only [List.length_cons]
      omega

/-! ### At the validator's own field decoder -/

/-- **Every validated tagged field is no wider than the record.** -/
theorem natBitLength_le_of_mem_taggedNatFieldCodes {raw field : ℕ}
    (hfield : field ∈ taggedNatFieldCodes raw) :
    natBitLength field ≤ natBitLength raw := by
  unfold taggedNatFieldCodes at hfield
  cases hdecode : decodeTaggedList raw with
  | none =>
      rw [hdecode] at hfield
      simp at hfield
  | some values =>
      have hcode : encodeTaggedList values = raw :=
        encodeTaggedList_of_decode hdecode
      rw [hdecode] at hfield
      have hmember : field ∈ values := by
        simpa only [Option.getD_some] using hfield
      have hle := le_of_mem_encodeTaggedList values field hmember
      rw [hcode] at hle
      exact natBitLength_mono hle

/-- **The validated field count is capped by the record's width.**  This is the
tagged codec's analogue of `ValidatorLeafWidthCore`'s
`rawBalancedTraversalTree_atoms_length_succ_le`. -/
theorem taggedNatFieldCodes_length_succ_le (raw : ℕ) :
    (taggedNatFieldCodes raw).length + 1 ≤ natBitLength raw := by
  unfold taggedNatFieldCodes
  cases hdecode : decodeTaggedList raw with
  | none =>
      have hwidth := one_le_natBitLength raw
      simp only [Option.getD_none, List.length_nil]
      omega
  | some values =>
      have hcode : encodeTaggedList values = raw :=
        encodeTaggedList_of_decode hdecode
      have hlength := encodeTaggedList_length_succ_le values
      rw [hcode] at hlength
      simpa only [Option.getD_some] using hlength

/-- The validated field outputs are counted by the same ledger. -/
theorem taggedNatFieldOutputs_length_succ_le (raw : ℕ) :
    (taggedNatFieldOutputs raw).length + 1 ≤ natBitLength raw := by
  have hlength := taggedNatFieldCodes_length_succ_le raw
  simpa only [taggedNatFieldOutputs, List.length_map] using hlength

end NearCubicWires.ValidatorTaggedSpineLedger
