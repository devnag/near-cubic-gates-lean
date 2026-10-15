import Proof.Gates.Succinct.TimeWord
import Proof.Gates.Outer.Interface

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicGates.Close.Outer

/-! ## The table of a description -/

theorem testBit_point (ν : ℕ) (i : Fin (2 ^ ν)) (j : ℕ) (hj : ν ≤ j) : (i : ℕ).testBit j = false :=
  Nat.testBit_eq_false_of_lt (i.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) hj))

theorem hc_pos (x : ℕ) (hx : 1 ≤ x) : 1 ≤ hc x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [hc_succ]; omega

/-- **The body computes `tt_N(B)` on `⟨B⟩_ν`** (paper lem:succinct-verifier, stage (3)). -/
theorem bodyTable_srcWord (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) (hν : 1 ≤ ν) (hfit : SrcFits G ν B) :
    bodyTable G (srcWord G ν B) = List.ofFn (ttN ν B) := by
  have hlen : (srcWord G ν B).length = ν ^ (G + 2) := srcWord_length G ν B hfit
  have hroot : rootOf G (srcWord G ν B).length = ν := by rw [hlen]; exact rootOf_pow G ν
  unfold bodyTable ttWord
  rw [hroot]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn]
  set n := (srcWord G ν B).length with hn
  have hs : B.nodes.length + 5 ≤ 2 ^ hc n := by
    have h1 := descriptor_length_ge B
    have h2 : (PCPPNative.descriptor B).length ≤ n := by rw [hlen]; exact hfit
    have h3 := lt_two_pow_hc n
    omega
  have hpt : ∀ j, hc ν < natBitLength j → (i : ℕ).testBit j = false := by
    intro j hj
    apply testBit_point ν ⟨i, by simpa using h1⟩ j
    have hp := hc_pos ν hν
    have hj0 : j ≠ 0 := by intro h; subst h; simp [natBitLength] at hj; omega
    have hlog : hc ν ≤ Nat.log 2 j := by unfold natBitLength at hj; omega
    have h3 : 2 ^ hc ν ≤ j := (Nat.pow_le_pow_right (by norm_num) hlog).trans (Nat.pow_log_le_self 2 hj0)
    have h4 := lt_two_pow_hc ν
    omega
  unfold srcWord srcDescriptor
  rw [evalModel_descriptor B _ (hc n) (hc ν) (fun j => (i : ℕ).testBit j) hs hpt]
  unfold ttN
  congr 1
  funext j
  unfold pointOf
  split_ifs with hj
  · rfl
  · exact testBit_point ν ⟨i, by simpa using h1⟩ j (by omega)

/-! ## Acceptance and the witness prefix -/

section
variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (G : ℕ)

theorem verifierV_accepts_iff (u y : List Bool) :
    (verifierV H G).accepts u y ↔
      H.verifier.accepts (bodyTable G u) (prefixBits y (H.time (2 ^ rootOf G u.length))) := by
  obtain ⟨r, hr, hacc⟩ := verifierV_run H G u y
  constructor
  · rintro ⟨f, r', hr', ha⟩
    have := UAcceptanceCarrier.run_receipt_unique (verifierV H G).machine _ f _ r' r hr' hr
    rw [this] at ha; exact hacc.mp ha
  · intro h; exact ⟨_, r, hr, hacc.mpr h⟩

theorem prefixBits_ofFn {T : ℕ} (w : BitInput T) (m : ℕ) :
    prefixBits (List.ofFn w) m = List.ofFn (fun i : Fin m => (List.ofFn w).getD i.val false) := rfl

end

/-! ## The theorem -/

theorem succinctVerifier_exists {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (G : ℕ) :
    Nonempty (SuccinctVerifier H G) := by
  obtain ⟨cG, hcG1, hcG⟩ := exists_cG G H.coefficient k
  let T : ℕ → ℕ := fun n => cG * 2 ^ ((k + 2) * rootOf G n)
  have hT : ∀ n, bodyCost G H.coefficient k n + 1 + H.time (2 ^ rootOf G n) ≤ T n := fun n => (hcG n).1
  have hTL : ∀ ν, T (instLength G ν) = cG * 2 ^ ((k + 2) * ν) := by
    intro ν; simp only [T, instLength, rootOf_pow]
  have hcG0 : cG ≠ 0 := by omega
  let K := 16 * (k + 2) + 16 * cG.bits.length + 20
  have hword : (fun ν => (cG * 2 ^ ((k + 2) * ν)).bits) = (fun ν => (T (instLength G ν)).bits) := by
    funext ν; rw [hTL]
  refine ⟨{
    V := verifierV H G
    T := T
    atLeast := fun n => (hcG n).2
    runs := ?runs
    onset := 1
    language := ?lang
    timeCoefficient := cG + K
    timeBound := ?tb
    timeExp := 1
    timeWord := hword ▸ (timeWordFn (k + 2) cG hcG0).enlargeBudget (fun ν => Nat.mul_le_mul_right _ (by omega)) }⟩
  case runs =>
    intro n x y
    obtain ⟨r, hr, _⟩ := verifierV_run H G (List.ofFn x) y
    rw [List.length_ofFn] at hr
    refine ⟨r, ?_⟩
    have := run_moreFuel _ _ (T n - (bodyCost G H.coefficient k n + 1 + H.time (2 ^ rootOf G n))) _ r hr
    rwa [Nat.add_sub_of_le (hT n)] at this
  case tb =>
    intro ν _
    rw [hTL, pow_mul, ← pow_mul, Nat.mul_comm (k + 2) ν, pow_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  case lang =>
    intro ν m B _ hν _ hfit
    have hofn := ofFn_srcBits G ν B hfit
    have htab := bodyTable_srcWord G ν B hν hfit
    have hlen : (srcWord G ν B).length = instLength G ν := srcWord_length G ν B hfit
    have hroot : rootOf G (srcWord G ν B).length = ν := by rw [hlen]; exact rootOf_pow G ν
    have hHT : H.time (2 ^ ν) ≤ T (instLength G ν) := by
      have := hT (instLength G ν)
      rw [← hlen, hroot] at this; rw [← hlen]; omega
    constructor
    · rintro ⟨w, hw⟩
      rw [hofn, verifierV_accepts_iff, htab, hroot] at hw
      exact ⟨fun i => (List.ofFn w).getD i.val false, hw⟩
    · rintro ⟨w', hw'⟩
      refine ⟨fun i => if h : i.val < H.time (2 ^ ν) then w' ⟨i.val, h⟩ else false, ?_⟩
      rw [hofn, verifierV_accepts_iff, htab, hroot]
      convert hw' using 2
      apply List.ext_getElem (by simp [prefixBits_length])
      intro i h1 h2
      simp only [prefixBits, List.getElem_ofFn, List.getD_eq_getElem?_getD]
      have hi : i < T (instLength G ν) := by simp at h2; omega
      rw [List.getElem?_eq_getElem (by simpa using hi)]
      simp only [Option.getD_some, List.getElem_ofFn]
      rw [dif_pos (by simpa using h2)]

end NearCubicGates.Close.Succinct
