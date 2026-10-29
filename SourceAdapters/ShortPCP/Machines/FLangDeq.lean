import SourceAdapters.ShortPCP.Machines.FLangDeg

/-!
# Single-run time, machine layer 16: `D_{RS,=}`

`Time.dEqFF degreeTestF κ B O r ans` (BCGT13 §12.3.1, Algorithm 16 with the base test of Algorithm 23; proof of `thm:short-pcp-ours`) is the base test at the last level of the recursion (`Time.dEqFF_iter`). `deqP` iterates the levels from
the level in `38`–`41` (`iterP` with fuel `κ`), sets the degree `d_{κ',2} = 2^{κ'}/4 − 1` of the last level in `12`,
and runs the base test `dtP` (`deqP_spec`). With fuel `κ` the recursion stops (`stop_iterate_depth`: every level
lowers `κ` until `κ ≤ 4`), so the base test reads at most `16` answers; every level's basis stays independent
(`indep_iterate_depth`), so its points are distinct.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

section Levels

variable {F : Type} [Field F]

theorem step_length_lt (x : Lvl F) (h : ¬ x.stop = true) : x.step.B.length < x.B.length := by
  have h5 : 5 ≤ x.B.length := by simp [Lvl.stop] at h; omega
  unfold Lvl.step
  split_ifs <;> simp [zMulti_length] <;> omega

/-- With fuel at least `κ`, the recursion reaches `κ ≤ κ0`. -/
theorem stop_iterate_depth : ∀ (n : ℕ) (x : Lvl F), x.B.length ≤ n → (Lvl.step^[x.depth n] x).stop = true
  | 0, x, h => by simp [Lvl.depth, Lvl.stop]; omega
  | n + 1, x, h => by
    by_cases hs : x.stop = true
    · simp [Lvl.depth, hs]
    · have e : x.depth (n + 1) = x.step.depth n + 1 := by rw [Lvl.depth, if_neg hs]
      rw [e, Function.iterate_succ_apply]
      exact stop_iterate_depth n x.step (by have := step_length_lt x hs; omega)

/-- Every level of an independent basis is independent (the bases of §12.3.1). -/
theorem indep_step [CharP F 2] (x : Lvl F) (hB : Indep x.B) (h : ¬ x.stop = true) : Indep x.step.B := by
  have h5 : 5 ≤ x.B.length := by simp [Lvl.stop] at h; omega
  have hk1 : x.B.length / 2 + 1 < x.B.length := by omega
  unfold Lvl.step
  split_ifs with hr hrv
  · show Indep (x.B.take (x.B.length / 2 + 1) ++ [x.B.getD (x.B.length / 2 + 1) 0])
    rw [rowMem_eq x.B _ hk1]; exact indep_take hB _
  · have hlt : bitsValue ((x.r.drop 1).take (x.B.drop (x.B.length / 2)).length) <
        2 ^ (x.B.drop (x.B.length / 2)).length :=
      lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))
    have := indep_rowNew hB (x.B.length / 2) hk1 (by omega) hlt
    show Indep (x.B.take (x.B.length / 2 + 1) ++ [sel (x.B.drop (x.B.length / 2))
      (bitsValue ((x.r.drop 1).take (x.B.drop (x.B.length / 2)).length)) + x.O + x.O])
    rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero, sel_drop x.B _ _ (by omega)]
  · exact indep_zMulti hB (x.B.length / 2) (by omega)

theorem indep_iterate_depth [CharP F 2] : ∀ (n : ℕ) (x : Lvl F), Indep x.B → Indep (Lvl.step^[x.depth n] x).B
  | 0, x, h => by simpa [Lvl.depth] using h
  | n + 1, x, h => by
    by_cases hs : x.stop = true
    · simpa [Lvl.depth, hs] using h
    · have e : x.depth (n + 1) = x.step.depth n + 1 := by rw [Lvl.depth, if_neg hs]
      rw [e, Function.iterate_succ_apply]
      exact indep_iterate_depth n x.step (indep_step x h hs)

end Levels

/-- **`D_{RS,=}`**: the levels, the degree of the last level, the base test (result bit in `7`). -/
def deqP : S := .seq (iterP (.v 39)) (.seq (.set 12 (.sub (.shr (.shl (.k 1) (.v 39)) (.k 2)) (.k 1))) dtP)

/-- The variables `deqP` writes. -/
def deqW : List Var := 12 :: iterW ++ dtW

/-- **`D_{RS,=}`** (`Time.dEqFF degreeTestF`, the poly-time form of the leaf's `dEqF`) on the level in `38`–`41` with
the packed answers in `11`. -/
theorem deqP_spec {F : Type} [Field F] [CharP F 2] [DecidableEq F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (x : Lvl F) (ansl : List ℕ) (hx : LRep φ s.fl u s x) (hind : Indep x.B)
    (haw : ∀ a ∈ ansl, a < 2 ^ s.fl) (h11 : s.env 11 = packW s.fl ansl) (h23 : s.env 23 = s.fl)
    (h42 : s.env 42 = bitsValue u) (h43 : s.env 43 = u.length) (hok : fieldOk G s.fl s.fp = true)
    (hirr : Irreducible (GF.toPoly s.fp))
    (hK : s.fl * x.B.length + 17 * s.fl + 1 ≤ G.K) (hN : x.B.length + 16 ≤ G.N)
    (hoff : s.env 41 + (x.B.length + 1) * (x.B.length + 2) ≤ G.K) (h48 : s.env 48 + x.B.length ≤ G.K) :
    let t := evalS G deqP s
    t.env 7 = (if dEqFF degreeTestF x.B.length x.B x.O x.r (fun i => ev φ (ansl.getD i 0)) then 1 else 0) ∧
      Wr deqW s t := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have h39 : s.env 39 = x.B.length := by
    obtain ⟨l, -, l39, -, llm, -⟩ := hx; rw [l39, ← llm, List.length_map]
  have hit := iterP_spec G s φ u x (.v 39) x.B.length (by simp [evalE, h39]; omega) hx h23 h42 h43 hok
    (by omega) (by omega) hoff h48
  obtain ⟨hy, -, hW, -⟩ := hit
  generalize hs1 : evalS G (iterP (.v 39)) s = s1 at hy hW
  have hstop := stop_iterate_depth x.B.length x le_rfl
  have hiy := indep_iterate_depth x.B.length x hind
  obtain ⟨y, hyd⟩ : ∃ y, Lvl.step^[x.depth x.B.length] x = y := ⟨_, rfl⟩
  rw [hyd] at hy hstop hiy
  have hy4 : y.B.length ≤ 4 := by simpa [Lvl.stop] using hstop
  obtain ⟨l, l38, l39, llw, llm, l40, lO, lr⟩ := hy
  have hl4 : l.length ≤ 4 := by rw [← llm, List.length_map] at hy4; exact hy4
  have h16 : 2 ^ l.length ≤ 16 := by
    calc 2 ^ l.length ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hl4
      _ = 16 := by norm_num
  obtain ⟨env, out, fl, fp, ip, bad⟩ := s1
  obtain rfl : fp = s.fp := hW.fp
  obtain rfl : fl = s.fl := hW.fl
  dsimp only at l38 l39 l40 lO lr
  have hW11 : env 11 = s.env 11 := hW.env 11 (by decide)
  have hW23 : env 23 = s.env 23 := hW.env 23 (by decide)
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hc2 : min 2 G.cap = 2 := min_cap (by omega)
  have e16 : min (2 ^ l.length) G.cap = 2 ^ l.length := min_cap_pow (by omega)
  have he : evalE G (⟨env, out, s.fl, s.fp, ip, bad⟩ : FS) (.sub (.shr (.shl (.k 1) (.v 39)) (.k 2)) (.k 1)) =
      dKE l.length 2 := by
    simp only [evalE, hc1, hc2, one_mul, l39, e16, dKE]
  have hdle : dKE l.length 2 ≤ 2 ^ l.length := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
  have hK16 : 2 ^ l.length * s.fl + s.fl + 1 ≤ G.K := by have := Nat.mul_le_mul_right s.fl h16; omega
  have hdt := dtP_spec G ((⟨env, out, s.fl, s.fp, ip, bad⟩ : FS).setv 12 (dKE l.length 2)) φ l ansl (dKE l.length 2)
    llw haw (by simp [l38]) (by simp [l39]) (by simpa using l40)
    (by simp; rw [hW11, h11]) (by simp)
    (by simp; rw [hW23, h23]) hok hirr (llm.symm ▸ hiy) hK16 (by omega) (by omega)
  obtain ⟨d7, dW⟩ := hdt
  have ht : t = evalS G dtP ((⟨env, out, s.fl, s.fp, ip, bad⟩ : FS).setv 12 (dKE l.length 2)) := by
    show evalS G deqP s = _
    simp only [deqP, evalS_seq]
    rw [hs1, evalS_set, he]
  refine ⟨?_, ?_⟩
  · have e1 : y.B = l.map (ev φ) := llm.symm
    have e2 : y.O = ev φ (env 40) := lO.symm
    rw [ht, d7, dEqFF_iter, hyd, T0_η, e1, e2, List.length_map]
    simp
  · rw [ht]
    exact ((hW.mono (W' := deqW) (by decide)).trans (Wr.setv (W := deqW) (i := 12) _ (by decide) _)).trans
      (dW.mono (W' := deqW) (by decide))

end NearCubicGates.Adapters.ShortPCP.Machines.FL
