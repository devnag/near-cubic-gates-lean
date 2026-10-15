import Proof.Foundations.ExecutableInterfaces

/-!
# Exact-width padding for projection PCPs

The source projection PCP may expose fewer random bits than the width frozen by
the recovery machine.  This module embeds its address space into the zero
suffix face of the larger cube and ignores the additional random bits.  The
construction preserves every acceptance decision and the exact acceptance
fraction; it does not appeal to a statistical approximation.
-/

namespace NearCubicWires.ProjectionPCPPadding

open NearCubicWires
open NearCubicWires.SourceInterfaces

def prefixBits {native padded : ℕ} (hwidth : native ≤ padded)
    (bits : BitInput padded) : BitInput native :=
  fun index => bits (Fin.castLE hwidth index)

def suffixBits {native padded : ℕ} (hwidth : native ≤ padded)
    (bits : BitInput padded) : BitInput (padded - native) :=
  fun index =>
    bits ⟨native + index.val, by omega⟩

def joinBits {native padded : ℕ} (hwidth : native ≤ padded)
    (nativeBits : BitInput native) (extraBits : BitInput (padded - native)) :
    BitInput padded :=
  fun index =>
    if hindex : index.val < native then
      nativeBits ⟨index.val, hindex⟩
    else
      extraBits ⟨index.val - native, by omega⟩

@[simp] theorem prefixBits_joinBits
    {native padded : ℕ} (hwidth : native ≤ padded)
    (nativeBits : BitInput native) (extraBits : BitInput (padded - native)) :
    prefixBits hwidth (joinBits hwidth nativeBits extraBits) = nativeBits := by
  funext index
  simp [prefixBits, joinBits, Fin.castLE]

@[simp] theorem suffixBits_joinBits
    {native padded : ℕ} (hwidth : native ≤ padded)
    (nativeBits : BitInput native) (extraBits : BitInput (padded - native)) :
    suffixBits hwidth (joinBits hwidth nativeBits extraBits) = extraBits := by
  funext index
  simp [suffixBits, joinBits]

@[simp] theorem joinBits_prefixBits_suffixBits
    {native padded : ℕ} (hwidth : native ≤ padded)
    (bits : BitInput padded) :
    joinBits hwidth (prefixBits hwidth bits) (suffixBits hwidth bits) = bits := by
  funext index
  by_cases hindex : index.val < native
  · simp [joinBits, prefixBits, hindex, Fin.castLE]
  · simp only [joinBits, suffixBits, hindex, ↓reduceDIte]
    congr 1
    apply Fin.ext
    change native + (index.val - native) = index.val
    omega

/-- Splitting a padded random string into its native prefix and ignored suffix
is an equivalence.  This equivalence is also the counting argument used below:
every native random string has exactly the same number of padded extensions. -/
def bitInputSplitEquiv {native padded : ℕ} (hwidth : native ≤ padded) :
    BitInput padded ≃ BitInput native × BitInput (padded - native) where
  toFun bits := (prefixBits hwidth bits, suffixBits hwidth bits)
  invFun parts := joinBits hwidth parts.1 parts.2
  left_inv := joinBits_prefixBits_suffixBits hwidth
  right_inv := by
    intro parts
    rcases parts with ⟨nativeBits, extraBits⟩
    simp

def liftProjectedRandomBit {native padded : ℕ}
    (hwidth : native ≤ padded) :
    ProjectedRandomBit native → ProjectedRandomBit padded
  | .bit index => .bit (Fin.castLE hwidth index)
  | .negatedBit index => .negatedBit (Fin.castLE hwidth index)
  | .constant value => .constant value

@[simp] theorem liftProjectedRandomBit_eval
    {native padded : ℕ} (hwidth : native ≤ padded)
    (projection : ProjectedRandomBit native) (randomness : BitInput padded) :
    (liftProjectedRandomBit hwidth projection).eval randomness =
      projection.eval (prefixBits hwidth randomness) := by
  cases projection <;> rfl

/-- The semantic exact-width padding.  Native query-address bits are retained
in the low coordinates; every new high address bit is the constant zero. -/
def padProjectionPCP
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n) :
    ProjectionPCP machine timeBound where
  nativeWidth := paddedWidth
  queryCount := pcp.queryCount
  queryAddressBits := fun {n} input query bit =>
    if hbit : bit.val < pcp.nativeWidth n then
      liftProjectedRandomBit (hwidth n)
        (pcp.queryAddressBits input query ⟨bit.val, hbit⟩)
    else
      .constant false
  decision := fun {n} input randomness =>
    pcp.decision input (prefixBits (hwidth n) randomness)
  constructionSteps := pcp.constructionSteps

@[simp] theorem padProjectionPCP_nativeWidth
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n) (n : ℕ) :
    (padProjectionPCP pcp paddedWidth hwidth).nativeWidth n =
      paddedWidth n := rfl

@[simp] theorem padProjectionPCP_queryCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n) (n : ℕ) :
    (padProjectionPCP pcp paddedWidth hwidth).queryCount n =
      pcp.queryCount n := rfl

@[simp] theorem padProjectionPCP_decision
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n) (randomness : BitInput (paddedWidth n)) :
    (padProjectionPCP pcp paddedWidth hwidth).decision input randomness =
      pcp.decision input (prefixBits (hwidth n) randomness) := rfl

private theorem sum_low_coordinates
    {native padded : ℕ} (hwidth : native ≤ padded) (term : Fin native → ℕ) :
    (∑ index : Fin padded,
        if hindex : index.val < native then
          term ⟨index.val, hindex⟩
        else 0) =
      ∑ index : Fin native, term index := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      have ih' := ih (Nat.le_add_right native extra)
      rw [show native + (extra + 1) = (native + extra) + 1 by omega]
      rw [Fin.sum_univ_castSucc]
      have hhead :
          (∑ index : Fin (native + extra),
              if hindex : index.castSucc.val < native then
                term ⟨index.castSucc.val, hindex⟩
              else 0) =
            ∑ index : Fin native, term index := by
        simpa only [Fin.val_castSucc] using ih'
      rw [hhead]
      simp

private theorem padded_address_sum
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n) (randomness : BitInput (paddedWidth n))
    (query : Fin (pcp.queryCount n)) :
    (∑ bit : Fin (paddedWidth n),
        if
          (padProjectionPCP pcp paddedWidth hwidth).queryAddressBits
              input query bit |>.eval randomness
        then 2 ^ bit.val
        else 0) =
      ∑ bit : Fin (pcp.nativeWidth n),
        if (pcp.queryAddressBits input query bit).eval
            (prefixBits (hwidth n) randomness)
        then 2 ^ bit.val
        else 0 := by
  calc
    _ =
        ∑ bit : Fin (paddedWidth n),
          if hbit : bit.val < pcp.nativeWidth n then
            if (pcp.queryAddressBits input query ⟨bit.val, hbit⟩).eval
                (prefixBits (hwidth n) randomness)
            then 2 ^ bit.val
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro bit _
      by_cases hbit : bit.val < pcp.nativeWidth n
      · simp [padProjectionPCP, hbit, liftProjectedRandomBit_eval]
      · simp only [padProjectionPCP, hbit, ↓reduceDIte]
        rfl
    _ = _ :=
      sum_low_coordinates (hwidth n)
        (fun bit =>
          if (pcp.queryAddressBits input query bit).eval
              (prefixBits (hwidth n) randomness)
          then 2 ^ bit.val
          else 0)

private theorem binaryWeightedSum_lt {width : ℕ} (bits : BitInput width) :
    (∑ bit : Fin width, if bits bit then 2 ^ bit.val else 0) < 2 ^ width := by
  induction width with
  | zero =>
      simp
  | succ width ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have ih' := ih (fun bit => bits bit.castSucc)
      by_cases hlast : bits (Fin.last width)
      · simp [hlast, pow_succ]
        omega
      · simp [hlast, pow_succ]
        omega

theorem padProjectionPCP_queryAddress_val
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n) (randomness : BitInput (paddedWidth n))
    (query : Fin (pcp.queryCount n)) :
    ((padProjectionPCP pcp paddedWidth hwidth).queryAddress
        input randomness query).val =
      (pcp.queryAddress input
        (prefixBits (hwidth n) randomness) query).val := by
  unfold ProjectionPCP.queryAddress binaryAddress
  change
    ((∑ bit : Fin (paddedWidth n),
          if
            (padProjectionPCP pcp paddedWidth hwidth).queryAddressBits
                input
                  (show
                    Fin ((padProjectionPCP pcp paddedWidth hwidth).queryCount n)
                    from query)
                  bit |>.eval randomness
          then 2 ^ bit.val
          else 0) % 2 ^ paddedWidth n) =
      ((∑ bit : Fin (pcp.nativeWidth n),
          if (pcp.queryAddressBits input query bit).eval
              (prefixBits (hwidth n) randomness)
          then 2 ^ bit.val
          else 0) % 2 ^ pcp.nativeWidth n)
  have haddressSum :
      (∑ bit : Fin (paddedWidth n),
          if
            (padProjectionPCP pcp paddedWidth hwidth).queryAddressBits
                input
                  (show
                    Fin ((padProjectionPCP pcp paddedWidth hwidth).queryCount n)
                    from query)
                  bit |>.eval randomness
          then 2 ^ bit.val
          else 0) =
        ∑ bit : Fin (pcp.nativeWidth n),
          if (pcp.queryAddressBits input query bit).eval
              (prefixBits (hwidth n) randomness)
          then 2 ^ bit.val
          else 0 := by
    convert padded_address_sum pcp paddedWidth hwidth
      input randomness query using 1
  rw [haddressSum]
  have hpow :
      2 ^ pcp.nativeWidth n ≤ 2 ^ paddedWidth n :=
    Nat.pow_le_pow_right (by omega) (hwidth n)
  have hnativeSum :
      (∑ bit : Fin (pcp.nativeWidth n),
          if (pcp.queryAddressBits input query bit).eval
              (prefixBits (hwidth n) randomness)
          then 2 ^ bit.val
          else 0) < 2 ^ pcp.nativeWidth n := by
    let bits : BitInput (pcp.nativeWidth n) :=
      fun bit => (pcp.queryAddressBits input query bit).eval
        (prefixBits (hwidth n) randomness)
    change (∑ bit : Fin (pcp.nativeWidth n),
      if bits bit then 2 ^ bit.val else 0) < 2 ^ pcp.nativeWidth n
    exact binaryWeightedSum_lt bits
  rw [Nat.mod_eq_of_lt (hnativeSum.trans_le hpow),
    Nat.mod_eq_of_lt hnativeSum]

def restrictPaddedProof
    {native padded : ℕ} (hwidth : native ≤ padded)
    (proof : BitInput (2 ^ padded)) : BitInput (2 ^ native) :=
  fun address =>
    proof (Fin.castLE (Nat.pow_le_pow_right (by omega) hwidth) address)

def extendNativeProof
    {native padded : ℕ} (_hwidth : native ≤ padded)
    (proof : BitInput (2 ^ native)) : BitInput (2 ^ padded) :=
  fun address =>
    if haddress : address.val < 2 ^ native then
      proof ⟨address.val, haddress⟩
    else false

@[simp] theorem restrictPaddedProof_extendNativeProof
    {native padded : ℕ} (hwidth : native ≤ padded)
    (proof : BitInput (2 ^ native)) :
    restrictPaddedProof hwidth (extendNativeProof hwidth proof) = proof := by
  funext address
  simp [restrictPaddedProof, extendNativeProof, Fin.castLE]

theorem padProjectionPCP_accepts
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n)
    (proof : BitInput (2 ^ paddedWidth n))
    (randomness : BitInput (paddedWidth n)) :
    (padProjectionPCP pcp paddedWidth hwidth).accepts
        input proof randomness =
      pcp.accepts input
        (restrictPaddedProof (hwidth n) proof)
        (prefixBits (hwidth n) randomness) := by
  unfold ProjectionPCP.accepts
  rw [padProjectionPCP_decision]
  congr 1
  funext query
  unfold restrictPaddedProof
  congr 1
  apply Fin.ext
  exact padProjectionPCP_queryAddress_val
    pcp paddedWidth hwidth input randomness query

theorem padProjectionPCP_accepts_extended
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n)
    (proof : BitInput (2 ^ pcp.nativeWidth n))
    (randomness : BitInput (paddedWidth n)) :
    (padProjectionPCP pcp paddedWidth hwidth).accepts
        input (extendNativeProof (hwidth n) proof) randomness =
      pcp.accepts input proof (prefixBits (hwidth n) randomness) := by
  rw [padProjectionPCP_accepts]
  simp

private abbrev acceptedRandomness
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (proof : BitInput (2 ^ pcp.nativeWidth n)) :=
  { randomness : BitInput (pcp.nativeWidth n) //
      pcp.accepts input proof randomness }

private def paddedAcceptedEquiv
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n)
    (proof : BitInput (2 ^ paddedWidth n)) :
    acceptedRandomness (padProjectionPCP pcp paddedWidth hwidth) input proof ≃
      acceptedRandomness pcp input
          (restrictPaddedProof (hwidth n) proof) ×
        BitInput (paddedWidth n - pcp.nativeWidth n) where
  toFun randomness :=
    (⟨prefixBits (hwidth n) randomness.1, by
      rw [← padProjectionPCP_accepts pcp paddedWidth hwidth]
      exact randomness.2⟩,
      suffixBits (hwidth n) randomness.1)
  invFun parts :=
    ⟨joinBits (hwidth n) parts.1.1 parts.2, by
      rw [padProjectionPCP_accepts]
      simpa using parts.1.2⟩
  left_inv := by
    intro randomness
    apply Subtype.ext
    exact joinBits_prefixBits_suffixBits (hwidth n) randomness.1
  right_inv := by
    intro parts
    apply Prod.ext
    · apply Subtype.ext
      exact prefixBits_joinBits (hwidth n) parts.1.1 parts.2
    · exact suffixBits_joinBits (hwidth n) parts.1.1 parts.2

theorem padProjectionPCP_acceptanceFraction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n)
    (proof : BitInput (2 ^ paddedWidth n)) :
    (padProjectionPCP pcp paddedWidth hwidth).acceptanceFraction input proof =
      pcp.acceptanceFraction input
        (restrictPaddedProof (hwidth n) proof) := by
  classical
  unfold ProjectionPCP.acceptanceFraction
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  rw [Fintype.card_congr
    (paddedAcceptedEquiv pcp paddedWidth hwidth input proof)]
  rw [Fintype.card_prod]
  have hdenominator :
      Fintype.card
          (BitInput
            ((padProjectionPCP pcp paddedWidth hwidth).nativeWidth n)) =
        Fintype.card
          (BitInput (pcp.nativeWidth n) ×
            BitInput
              ((padProjectionPCP pcp paddedWidth hwidth).nativeWidth n -
                pcp.nativeWidth n)) :=
    Fintype.card_congr
      (bitInputSplitEquiv
        (show
          pcp.nativeWidth n ≤
            (padProjectionPCP pcp paddedWidth hwidth).nativeWidth n
          from hwidth n))
  rw [hdenominator, Fintype.card_prod]
  have hsuffixCard :
      Fintype.card
          (BitInput (paddedWidth n - pcp.nativeWidth n)) =
        Fintype.card
          (BitInput
            ((padProjectionPCP pcp paddedWidth hwidth).nativeWidth n -
              pcp.nativeWidth n)) := by
    apply Fintype.card_congr
    exact Equiv.cast (by rfl)
  rw [hsuffixCard]
  have hsuffix :
      (0 : ℝ) <
        Fintype.card
          (BitInput
            ((padProjectionPCP pcp paddedWidth hwidth).nativeWidth n -
              pcp.nativeWidth n)) := by
    exact_mod_cast Fintype.card_pos
  push_cast
  field_simp

theorem padProjectionPCP_complete
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n)
    (hcomplete :
      ∃ proof, ∀ randomness, pcp.accepts input proof randomness) :
    ∃ proof, ∀ randomness,
      (padProjectionPCP pcp paddedWidth hwidth).accepts
        input proof randomness := by
  rcases hcomplete with ⟨proof, hproof⟩
  refine ⟨extendNativeProof (hwidth n) proof, ?_⟩
  intro randomness
  rw [padProjectionPCP_accepts_extended]
  exact hproof _

theorem padProjectionPCP_sound
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n) (soundness : ℝ)
    (hsound :
      ∀ proof, pcp.acceptanceFraction input proof ≤ soundness) :
    ∀ proof,
      (padProjectionPCP pcp paddedWidth hwidth).acceptanceFraction input proof ≤
        soundness := by
  intro proof
  rw [padProjectionPCP_acceptanceFraction]
  exact hsound _

end NearCubicWires.ProjectionPCPPadding
