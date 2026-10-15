import Proof.Wire_3_5.FinalPassMask

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Lists Finset

/-! ## The decoder is the indicator of its bits' value -/

/-- The value `Σ_h G_h 2^h` of `ℓ` bits. -/
def decodeVal : (ℓ : ℕ) → (Fin ℓ → ZMod 2) → ℕ
  | 0, _ => 0
  | ℓ + 1, G => (G 0).val + 2 * decodeVal ℓ (fun h => G h.succ)

theorem zmod2_val_le_one (x : ZMod 2) : x.val ≤ 1 := by
  have := ZMod.val_lt x; omega

theorem decodeVal_lt : ∀ (ℓ : ℕ) (G : Fin ℓ → ZMod 2), decodeVal ℓ G < 2 ^ ℓ
  | 0, _ => by simp [decodeVal]
  | ℓ + 1, G => by
    have ih := decodeVal_lt ℓ (fun h => G h.succ)
    have := zmod2_val_le_one (G 0)
    simp only [decodeVal, pow_succ]
    omega

theorem testBit_decodeVal : ∀ (ℓ : ℕ) (G : Fin ℓ → ZMod 2) (h : Fin ℓ),
    (decodeVal ℓ G).testBit h = decide (G h = 1)
  | 0, _, h => h.elim0
  | ℓ + 1, G, h => by
    have hv := zmod2_val_le_one (G 0)
    cases h using Fin.cases with
    | zero =>
      simp only [decodeVal, Fin.val_zero, Nat.testBit_zero]
      rcases zmod2_eq_zero_or_one (G 0) with h0 | h1
      · rw [h0]; simp
      · have h1v : (1 : ZMod 2).val = 1 := rfl
        rw [h1, h1v]; simp
    | succ h =>
      simp only [decodeVal, Fin.val_succ, Nat.testBit_succ]
      have : ((G 0).val + 2 * decodeVal ℓ (fun h => G h.succ)) / 2 = decodeVal ℓ (fun h => G h.succ) := by omega
      rw [this]
      exact testBit_decodeVal ℓ (fun h => G h.succ) h

theorem residueDecoder_eq_indicator (ℓ : ℕ) (W : ℤ) (G : Fin ℓ → ZMod 2) (d : ℤ) :
    residueDecoder ℓ W G d = if d = (decodeVal ℓ G : ℤ) - W then 1 else 0 := by
  have hstar : residueDecoder ℓ W G ((decodeVal ℓ G : ℤ) - W) = 1 := by
    unfold residueDecoder
    have hlt := decodeVal_lt ℓ G
    have hW : (decodeVal ℓ G : ℤ) - W + W = decodeVal ℓ G := by ring
    rw [if_pos ⟨by rw [hW]; positivity, by rw [hW]; exact_mod_cast hlt⟩]
    apply Finset.prod_eq_one
    intro h _
    rw [hW, Int.toNat_natCast, testBit_decodeVal]
    rcases zmod2_eq_zero_or_one (G h) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  split_ifs with hd
  · rw [hd]; exact hstar
  · rcases zmod2_eq_zero_or_one (residueDecoder ℓ W G d) with h0 | h1
    · exact h0
    · exact absurd (residueDecoder_atMostOneHot ℓ W G d _ h1 hstar) hd

/-! ## Following the reconstructed state -/

def followStep (M : ℕ) (d : ℤ) : Option ℕ → Option ℕ
  | none => none
  | some t => if t ≤ M ∧ 0 ≤ 2 * (t : ℤ) + d then some (2 * (t : ℤ) + d).toNat else none

/-- The followed state from `P_J = e_0` through the decoded residues of levels `J−1, …, 0`. -/
def followAll (M : ℕ) : List ℤ → Option ℕ
  | [] => some 0
  | d :: rest => followStep M d (followAll M rest)

theorem followStep_pos {M : ℕ} {d : ℤ} {t : ℕ} (h1 : t ≤ M) (h2 : 0 ≤ 2 * (t : ℤ) + d) :
    followStep M d (some t) = some (2 * (t : ℤ) + d).toNat := by
  simp [followStep, h1, h2]

theorem followStep_neg {M : ℕ} {d : ℤ} {t : ℕ} (h : ¬(t ≤ M ∧ 0 ≤ 2 * (t : ℤ) + d)) :
    followStep M d (some t) = none := by
  simp only [followStep]
  rw [if_neg h]

/-- One step of the recurrence against a (possibly empty) one-hot child. -/
theorem stepSum (M : ℕ) (d : ℤ) (s : ℕ) (o : Option ℕ) :
    (∑ x ∈ range (M + 1), (if o = some x then (1 : ZMod 2) else 0) * if (s : ℤ) - 2 * x = d then 1 else 0) =
      if followStep M d o = some s then 1 else 0 := by
  cases o with
  | none => simp [followStep]
  | some t0 =>
    simp only [Option.some.injEq]
    by_cases htM : t0 ≤ M
    · rw [Finset.sum_eq_single t0 (fun t _ ht => by simp [Ne.symm ht])
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
      simp only [if_true, one_mul]
      by_cases h2 : 0 ≤ 2 * (t0 : ℤ) + d
      · simp only [followStep_pos htM h2, Option.some.injEq]
        by_cases hs : (s : ℤ) - 2 * t0 = d
        · rw [if_pos hs, if_pos (by omega)]
        · rw [if_neg hs, if_neg (by omega)]
      · have hn : ¬((s : ℤ) - 2 * t0 = d) := by omega
        simp only [followStep_neg (fun h => h2 h.2), hn, if_false, reduceCtorEq]
    · rw [Finset.sum_eq_zero (fun t ht => by
          have : t ≠ t0 := by simp at ht; omega
          simp [Ne.symm this])]
      simp only [followStep_neg (fun h => htM h.1), reduceCtorEq, if_false]

/-- **The recurrence of one-hot decoders is the indicator of the followed state.** -/
theorem recurAll_indicator (M : ℕ) (ds : List ℤ) (s : ℕ) :
    recurAll M (ds.map fun d (x : ℤ) => if x = d then (1 : ZMod 2) else 0) s =
      if followAll M ds = some s then 1 else 0 := by
  induction ds generalizing s with
  | nil =>
    simp only [List.map_nil, recurAll, followAll, Option.some.injEq]
    by_cases hs : s = 0
    · simp [hs]
    · simp [hs, Ne.symm hs]
  | cons d rest ih =>
    simp only [List.map_cons, recurAll, recurStep, ih, followAll]
    exact stepSum M d s (followAll M rest)

/-! ## The repaired list's report -/

namespace ListFast
variable (D : ListData)

/-- The decoded residue of level `j`: `d_j = val(G_{j,·}) − W_j`. -/
def decoded (j : ℕ) (Z : List Bool) : ℤ := (decodeVal (D.ell j) (D.decoderBits j Z) : ℤ) - D.W j

/-- The followed state of the list at the input `Z`. -/
def followed (Z : List Bool) : Option ℕ := followAll D.M ((List.range D.J).map fun j => decoded D j Z)

/-- **The fast report**: the followed state if it is in `[0, M]`, else `0` (the repair). -/
def listReportFast (Z : List Bool) : ℕ :=
  match followed D Z with
  | some v => if v ≤ D.M then v else 0
  | none => 0

theorem levelDecoder_eq (j : ℕ) (Z : List Bool) :
    D.levelDecoder j Z = fun d => if d = decoded D j Z then 1 else 0 := by
  funext d
  unfold ListData.levelDecoder decoded
  exact residueDecoder_eq_indicator _ _ _ d

theorem listStates_eq (Z : List Bool) :
    D.listStates Z = repair D.M (fun s => if followed D Z = some s then 1 else 0) := by
  unfold ListData.listStates followed
  congr 1
  funext s
  rw [← recurAll_indicator, List.map_map]
  congr 2
  funext j
  exact levelDecoder_eq D j Z

theorem fast_le (Z : List Bool) : listReportFast D Z ≤ D.M := by
  unfold listReportFast
  split
  · split_ifs with h <;> omega
  · omega

theorem listReport_eq_fast (Z : List Bool) : D.listReport Z = listReportFast D Z := by
  symm
  apply (D.listStates_eq_one_iff Z _ (fast_le D Z)).mp
  rw [listStates_eq]
  unfold repair listReportFast
  cases hF : followed D Z with
  | none =>
    simp only [if_true, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero]
  | some v =>
    by_cases hvM : v ≤ D.M
    · by_cases hv0 : v = 0
      · subst hv0
        simp only [Option.some.injEq]
        rw [Finset.sum_eq_zero (fun s hs => by
          have : s ≠ 0 := (Finset.mem_erase.mp hs).1
          simp [Ne.symm this])]
        simp
      · simp only [hvM, if_true, hv0, if_false]
    · simp only [hvM, if_false, if_true, Option.some.injEq]
      rw [Finset.sum_eq_zero (fun s hs => by
        have : s ≤ D.M := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hs).2)
        have hne : v ≠ s := by omega
        simp [hne])]
      simp

end ListFast

end NearCubicWires.WireExponent3_5.FinalPass
