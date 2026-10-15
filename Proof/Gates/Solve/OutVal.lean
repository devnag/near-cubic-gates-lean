import Proof.Gates.Solve.Print

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (ratWord intWord listWord)
open NearCubicGates.Close.Interfaces.Formats (solveWord SysReq)

/-- The sign bit of `−y/D`. -/
def negB (y D : ℤ) : ℕ := if y ≠ 0 ∧ (y < 0 ↔ D < 0) then 1 else 0

/-- The printed words of one unknown `−y/D`. -/
def entW (y D : ℤ) : List Bool :=
  natWord (negB y D) ++ natWord (y.natAbs / Nat.gcd D.natAbs y.natAbs) ++
    natWord (D.natAbs / Nat.gcd D.natAbs y.natAbs)

theorem ratWord_eq (y D : ℤ) (hD : D ≠ 0) : ratWord (-(y : ℚ) / D) = entW y D := by
  set g := Nat.gcd D.natAbs y.natAbs with hg
  have hD0 : 0 < D.natAbs := Int.natAbs_pos.mpr hD
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hD0
  obtain ⟨a, ha⟩ : ∃ a, a = y.natAbs / g := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = D.natAbs / g := ⟨_, rfl⟩
  have hya : y.natAbs = a * g := by rw [ha]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
  have hDb : D.natAbs = b * g := by rw [hb]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [h0, Nat.zero_mul] at hDb; omega
    · exact h0
  have hcop : Nat.Coprime a b := by rw [ha, hb]; exact (Nat.coprime_div_gcd_div_gcd hg0).symm
  have hyc : |y| = (a : ℤ) * g := by rw [← Int.natCast_natAbs]; exact_mod_cast hya
  have hDc : |D| = (b : ℤ) * g := by rw [← Int.natCast_natAbs]; exact_mod_cast hDb
  set ε : ℤ := if negB y D = 1 then -1 else 1 with hε
  have key : -y * (b : ℤ) = ε * a * D := by
    rcases lt_trichotomy y 0 with hy | hy | hy <;> rcases lt_trichotomy D 0 with hD' | hD' | hD'
    · have e1 : negB y D = 1 := by unfold negB; rw [if_pos ⟨hy.ne, iff_of_true hy hD'⟩]
      rw [hε, e1, if_pos rfl]
      rw [abs_of_neg hy] at hyc; rw [abs_of_neg hD'] at hDc
      have ey : y = -(a * g) := by linarith
      have eD : D = -(b * g) := by linarith
      rw [ey, eD]; ring
    · exact absurd hD' hD
    · have e1 : negB y D = 0 := by unfold negB; rw [if_neg (by intro ⟨_, h2⟩; exact absurd (h2.mp hy) (by omega))]
      rw [hε, e1, if_neg (by decide)]
      rw [abs_of_neg hy] at hyc; rw [abs_of_pos hD'] at hDc
      have ey : y = -(a * g) := by linarith
      have eD : D = b * g := by linarith
      rw [ey, eD]; ring
    · have e1 : negB y D = 0 := by unfold negB; rw [if_neg (by intro ⟨h1, _⟩; exact h1 hy)]
      rw [hε, e1, if_neg (by decide)]
      subst hy
      have : a = 0 := by simp at hya; rcases hya with h | h <;> omega
      subst this; simp
    · exact absurd hD' hD
    · have e1 : negB y D = 0 := by unfold negB; rw [if_neg (by intro ⟨h1, _⟩; exact h1 hy)]
      rw [hε, e1, if_neg (by decide)]
      subst hy
      have : a = 0 := by simp at hya; rcases hya with h | h <;> omega
      subst this; simp
    · have e1 : negB y D = 0 := by unfold negB; rw [if_neg (by intro ⟨_, h2⟩; exact absurd (h2.mpr hD') (by omega))]
      rw [hε, e1, if_neg (by decide)]
      rw [abs_of_pos hy] at hyc; rw [abs_of_neg hD'] at hDc
      have ey : y = a * g := by linarith
      have eD : D = -(b * g) := by linarith
      rw [ey, eD]; ring
    · exact absurd hD' hD
    · have e1 : negB y D = 1 := by
        unfold negB; rw [if_pos ⟨hy.ne', iff_of_false (by omega) (by omega)⟩]
      rw [hε, e1, if_pos rfl]
      rw [abs_of_pos hy] at hyc; rw [abs_of_pos hD'] at hDc
      have ey : y = a * g := by linarith
      have eD : D = b * g := by linarith
      rw [ey, eD]; ring
  have hq : (-(y : ℚ) / D) = ((ε * a : ℤ) : ℚ) / ((b : ℤ) : ℚ) := by
    rw [div_eq_div_iff (by exact_mod_cast hD) (by exact_mod_cast hb0.ne')]
    exact_mod_cast key
  have hεa : (ε * (a : ℤ)).natAbs = a := by
    rw [Int.natAbs_mul, hε]; split_ifs <;> simp
  have hcop' : Nat.Coprime (ε * (a : ℤ)).natAbs ((b : ℤ)).natAbs := by
    rw [hεa, Int.natAbs_natCast]; exact hcop
  have hnum : (-(y : ℚ) / D).num = ε * a := by
    rw [hq]; exact Rat.num_div_eq_of_coprime (by exact_mod_cast hb0) hcop'
  have hden : (-(y : ℚ) / D).den = b := by
    have := Rat.den_div_eq_of_coprime (a := ε * a) (b := (b : ℤ)) (by exact_mod_cast hb0) hcop'
    rw [← hq] at this; exact_mod_cast this
  have hsg : (if ε * (a : ℤ) < 0 then 1 else 0) = negB y D := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · have : negB y D = 0 := by
        unfold negB; rw [if_neg]; intro ⟨h1, _⟩
        rw [ha0, Nat.zero_mul] at hya; exact h1 (Int.natAbs_eq_zero.mp hya)
      rw [this, ha0]; simp
    · have hneg : negB y D = 0 ∨ negB y D = 1 := by unfold negB; split_ifs <;> simp
      rcases hneg with h0 | h1
      · rw [h0, hε, h0]; simp
      · rw [h1, hε, h1]; simp [ha0]
  unfold ratWord intWord entW
  rw [hnum, hden, hεa, hsg, ← hg, ← ha, ← hb]

/-- **The output word** in the printed terms. -/
theorem solveWord_eq (s : SysReq) : solveWord (solve s) =
    if ∃ i < s.rows.length, (final s).a i s.pts.length ≠ 0 then natWord 0
    else natWord 1 ++ natWord s.pts.length ++
      (List.range s.pts.length).flatMap (fun v => entW ((final s).a (s.rows.length + v) s.pts.length) (final s).D) := by
  obtain ⟨k, R, C, hI, -⟩ := run_inv (amat s) s.rows.length s.pts.length
  have hD : (final s).D ≠ 0 := hI.ne
  unfold solve
  split_ifs with hall hb hb
  · exfalso
    obtain ⟨i, hi, hne⟩ := hb
    rw [List.all_eq_true] at hall
    have := hall i (List.mem_range.mpr hi)
    simp at this; exact hne this
  · simp only [solveWord, listWord, List.length_map, List.length_range, List.append_assoc]
    congr 2
    rw [List.flatMap_map]
    congr 1
    funext v
    exact ratWord_eq _ _ hD
  · rfl
  · exfalso
    apply hall
    rw [List.all_eq_true]
    intro i hi
    have := List.mem_range.mp hi
    simp only [beq_iff_eq]
    by_contra hne
    exact hb ⟨i, this, hne⟩

end NearCubicGates.Close.Solve
