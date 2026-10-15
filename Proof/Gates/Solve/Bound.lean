import Proof.Gates.Solve.Fin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (intWord listWord)
open NearCubicGates.Close.Interfaces.Formats (SysReq sysWord)

theorem sub_flatMap {α β : Type} (f : α → List β) : ∀ {l : List α} {a : α}, a ∈ l → (f a).Sublist (l.flatMap f)
  | [], _, h => by simp at h
  | b :: l, a, h => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sub_flatMap f h).trans (List.sublist_append_right _ _)

theorem len_le_flatMap {α β : Type} (f : α → List β) (hf : ∀ a, 1 ≤ (f a).length) :
    ∀ l : List α, l.length ≤ (l.flatMap f).length
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := hf a; have := len_le_flatMap f hf l; omega

theorem lt_pow_natWord (x : ℕ) : x < 2 ^ (natWord x).length := by
  rw [natWord_len]
  have h1 : x < 2 ^ natBitLength x := by unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) x
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem lt_of_sub {x : ℕ} {w : List Bool} (h : (natWord x).Sublist w) : x < 2 ^ w.length :=
  lt_of_lt_of_le (lt_pow_natWord x) (Nat.pow_le_pow_right (by norm_num) h.length_le)

theorem natWord_pos (x : ℕ) : 1 ≤ (natWord x).length := by rw [natWord_len]; omega

/-- The row field of `sysWord`. -/
def rowF (row : ℕ × List ℕ × ℕ) : List Bool := natWord row.1 ++ listWord natWord row.2.1 ++ natWord row.2.2

theorem sysWord_split (s : SysReq) : sysWord s =
    (natWord s.pts.length ++ s.pts.flatMap (listWord intWord)) ++ (natWord s.rows.length ++ s.rows.flatMap rowF) :=
  rfl

theorem reqBound_of (s : SysReq) : ReqBound s (sysWord s).length := by
  have hP : (s.pts.flatMap (listWord intWord)).Sublist (sysWord s) := by
    rw [sysWord_split]; exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)
  have hR : (s.rows.flatMap rowF).Sublist (sysWord s) := by
    rw [sysWord_split]; exact (List.sublist_append_right _ _).trans (List.sublist_append_right _ _)
  refine ⟨fun u hu => ?_, fun row hrow => ?_⟩
  · have hu' : (listWord intWord u).Sublist (sysWord s) := (sub_flatMap _ hu).trans hP
    have hf : (u.flatMap intWord).Sublist (sysWord s) := (List.sublist_append_right _ _).trans hu'
    refine ⟨le_trans (len_le_flatMap intWord (fun z => by
      unfold intWord; rw [List.length_append]; have := natWord_pos z.natAbs; omega) u) hf.length_le,
      fun z hz => lt_of_sub (((List.sublist_append_right _ _).trans (sub_flatMap intWord hz)).trans hf)⟩
  · have hr : (rowF row).Sublist (sysWord s) := (sub_flatMap _ hrow).trans hR
    have hl : (listWord natWord row.2.1).Sublist (sysWord s) :=
      ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _)).trans hr
    have hfl : (row.2.1.flatMap natWord).Sublist (sysWord s) := (List.sublist_append_right _ _).trans hl
    refine ⟨lt_of_sub (((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)).trans hr),
      fun x hx => lt_of_sub ((sub_flatMap natWord hx).trans hfl),
      le_trans (len_le_flatMap natWord natWord_pos _) hfl.length_le,
      lt_of_sub ((List.sublist_append_right _ _).trans hr)⟩

theorem sysWord_pos (s : SysReq) : 1 ≤ (sysWord s).length := by
  rw [sysWord_split]; simp only [List.length_append]; have := natWord_pos s.pts.length; omega

theorem amat_abs {s : SysReq} {ℓ : ℕ} (hrb : ReqBound s ℓ) (i j : ℕ) : |amat s i j| ≤ (2 ^ ℓ : ℤ) := by
  have h1 : (1 : ℤ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  unfold amat
  split_ifs with hi hj hk
  · unfold coef; split_ifs <;> simp [h1]
  · have hmem : s.rows.getD i (0, [], 0) ∈ s.rows := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    have := (hrb.rows _ hmem).2.2.2
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast this.le
  · simp [h1]
  · simp

/-- The Bareiss bound. -/
def bdOf (n ℓ : ℕ) : ℕ := (n + 1).factorial * (2 ^ ℓ) ^ (n + 1)

theorem bdOf_mono {k n : ℕ} (h : k ≤ n) (ℓ : ℕ) : bdOf k ℓ ≤ bdOf n ℓ := by
  unfold bdOf
  exact Nat.mul_le_mul (Nat.factorial_le (by omega)) (Nat.pow_le_pow_right (by positivity) (by omega))

theorem bareiss_bd {s : SysReq} {ℓ : ℕ} (hrb : ReqBound s ℓ) {k n : ℕ} (hk : k ≤ n) :
    (∀ i j, ((run s.rows.length ⟨amat s, 1⟩ k).a i j).natAbs ≤ bdOf n ℓ) ∧
      ((run s.rows.length ⟨amat s, 1⟩ k).D).natAbs ≤ bdOf n ℓ := by
  have hb := run_bound (amat s) s.rows.length (2 ^ ℓ) (one_le_pow₀ (by norm_num)) (amat_abs hrb) k
  have hc : ((k + 1).factorial : ℤ) * (2 ^ ℓ) ^ (k + 1) = (bdOf k ℓ : ℤ) := by unfold bdOf; push_cast; ring
  have hm := bdOf_mono hk ℓ
  refine ⟨fun i j => ?_, ?_⟩
  · have := hb.1 i j
    rw [hc, Int.abs_eq_natAbs] at this
    have : ((run s.rows.length ⟨amat s, 1⟩ k).a i j).natAbs ≤ bdOf k ℓ := by exact_mod_cast this
    omega
  · have := hb.2
    rw [hc, Int.abs_eq_natAbs] at this
    have : ((run s.rows.length ⟨amat s, 1⟩ k).D).natAbs ≤ bdOf k ℓ := by exact_mod_cast this
    omega

theorem bdOf_pos (n ℓ : ℕ) : 1 ≤ bdOf n ℓ := by
  unfold bdOf; exact Nat.one_le_iff_ne_zero.mpr (by positivity)

theorem bd_width {n ℓ : ℕ} (hn : n ≤ ℓ) : 2 * bdOf n ℓ * bdOf n ℓ + 1 < 2 ^ wOf ℓ := by
  have h1 : bdOf n ℓ ≤ (2 ^ ℓ) ^ (ℓ + 1) * (2 ^ ℓ) ^ (ℓ + 1) := by
    unfold bdOf
    refine Nat.mul_le_mul ?_ (Nat.pow_le_pow_right (by positivity) (by omega))
    calc (n + 1).factorial ≤ (ℓ + 1).factorial := Nat.factorial_le (by omega)
      _ ≤ (ℓ + 1) ^ (ℓ + 1) := Nat.factorial_le_pow _
      _ ≤ (2 ^ ℓ) ^ (ℓ + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self _
  have h2 : (2 ^ ℓ) ^ (ℓ + 1) * (2 ^ ℓ) ^ (ℓ + 1) = 2 ^ (2 * (ℓ * (ℓ + 1))) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  rw [h2] at h1
  have h3 : 2 * bdOf n ℓ * bdOf n ℓ ≤ 2 * 2 ^ (2 * (ℓ * (ℓ + 1))) * 2 ^ (2 * (ℓ * (ℓ + 1))) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h1
  have h4 : 2 * 2 ^ (2 * (ℓ * (ℓ + 1))) * 2 ^ (2 * (ℓ * (ℓ + 1))) = 2 ^ (4 * (ℓ * (ℓ + 1)) + 1) := by
    rw [← pow_succ', ← pow_add]; ring_nf
  rw [h4] at h3
  have h8 : 2 ^ (4 * (ℓ * (ℓ + 1)) + 2) ≤ 2 ^ wOf ℓ := Nat.pow_le_pow_right (by norm_num) (by unfold wOf; nlinarith)
  have hB : 2 ^ (4 * (ℓ * (ℓ + 1)) + 2) = 2 * 2 ^ (4 * (ℓ * (ℓ + 1)) + 1) := by rw [pow_succ]; ring
  have hA : 2 ≤ 2 ^ (4 * (ℓ * (ℓ + 1)) + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  set X := 2 * bdOf n ℓ * bdOf n ℓ
  set A := 2 ^ (4 * (ℓ * (ℓ + 1)) + 1)
  set B := 2 ^ (4 * (ℓ * (ℓ + 1)) + 2)
  omega

end NearCubicGates.Close.Solve
