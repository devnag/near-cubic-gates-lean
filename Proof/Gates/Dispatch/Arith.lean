import Proof.Gates.Dispatch.Macros

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

variable {C : Ctx}

theorem pow_lt_iff_lt_clog (m j : ℕ) : 2 ^ j < m ↔ j < Nat.clog 2 m :=
  (Nat.lt_clog_iff_pow_lt (by norm_num)).symm

/-- `t5 := Nat.clog 2 t3` (scratch `t6`). -/
def clog2 : St VV := .seq (.op (.zero t5)) (.seq (.op (.copy t6 v1)) (.loop (.lt t6 t3) (.seq (.op (.shl t6))
  (.op (.inc t5)))))

theorem clog2_spec (a : DS VV) (hc : Cst a) (hW : 2 * a.env t3 + 2 < 2 ^ C.Wd) :
    Hs C clog2 a (5 * Nat.clog 2 (a.env t3) + 6) (fun b => b.env t5 = Nat.clog 2 (a.env t3) ∧
      b.env t6 = 2 ^ Nat.clog 2 (a.env t3) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [t5, t6]) := by
  set m := a.env t3 with hm
  set c := Nat.clog 2 m with hcdef
  have hpow : ∀ j ≤ c, 2 ^ j < 2 * m + 2 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp only [pow_zero]; omega
    · have : 2 ^ (j - 1) < m := (pow_lt_iff_lt_clog m (j - 1)).2 (by omega)
      have e : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
      omega
  let I : ℕ → DS VV → Prop := fun k b => b.env t5 = k ∧ b.env t6 = 2 ^ k ∧ b.env t3 = m ∧ b.cp = a.cp ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Fr a b [t5, t6]
  have l : ∀ b, I 0 b → Hs C (.loop (.lt t6 t3) (.seq (.op (.shl t6)) (.op (.inc t5)))) b (c * (3 + 2) + 2) (I c) := by
    refine Hs.loopN (c := .lt t6 t3) (show t6 ≠ t3 by decide) I c 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7⟩
      refine ⟨by simp only [Cnd.eval, h2, h3, decide_eq_true_eq]; exact (pow_lt_iff_lt_clog m k).2 hk, ?_⟩
      have hk1 := hpow (k + 1) hk
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C t6 b (by rw [h2]; rw [pow_succ] at hk1; omega)) (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_inc C t5 _ (by vsimp [h1]; have := Nat.lt_two_pow_self (n := k); omega)) le_rfl ?_
      rintro e rfl
      exact ⟨by vsimp [h1], by vsimp [h2, pow_succ]; ring, by vsimp [h3], h4, h5, h6,
        Fr.trans h7 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
    · intro b ⟨h1, h2, h3, _⟩
      simp only [Cnd.eval, h2, h3, decide_eq_false_iff_not]
      rw [pow_lt_iff_lt_clog]; omega
  refine Hx.hs (Hs.then (hs_zero C t5 a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_copy C t6 v1 _ (by decide)) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.last (l _ ⟨by vsimp [], by vsimp [hc.one], by vsimp [hm], rfl, rfl, rfl,
    Fr.trans (Fr.set a _ (by decide)) (Fr.set _ _ (by decide))⟩) ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n2 hn2
  exact ⟨⟨b1, b2, b4, b5, b6, Cst.of_fr hc b7 (by decide) (by rw [b7 vPOS (by decide), b4]; exact hc.pos), b7⟩,
    by omega⟩

/-- `t5 := t3 ^ k` (scratch `t6`). -/
def powK : ℕ → St VV
  | 0 => .op (.copy t5 v1)
  | k + 1 => .seq (powK k) (.seq (.op (.mul t5 t3 t6)) (.op (.copy t5 t6)))

theorem powK_spec (a : DS VV) (hc : Cst a) :
    ∀ k : ℕ, (∀ j ≤ k, a.env t3 ^ j < 2 ^ C.Wd) →
      Hs C (powK k) a (4 * k + 1) (fun b => b.env t5 = a.env t3 ^ k ∧ b.env t3 = a.env t3 ∧ b.cp = a.cp ∧
        b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [t5, t6]) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine Hs.mono (hs_copy C t5 v1 a (by decide)) le_rfl ?_
    rintro b rfl
    exact ⟨by vsimp [hc.one], by vsimp [], rfl, rfl, rfl, Cst.of_fr (T := [t5]) hc (Fr.set a _ (by decide))
      (by decide) (by vsimp [hc.pos]), Fr.set a _ (by decide)⟩
  | succ k ih =>
    intro hall
    refine Hs.mono (Hs.seq (t2 := 3) (ih (fun j hj => hall j (by omega))) (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ => ?_))
      (show 4 * k + 1 + 3 + 1 ≤ 4 * (k + 1) + 1 by omega) (fun _ h => h)
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_mul C t5 t3 t6 b (by decide) (by decide) (by decide)
      (by rw [b1, b2, ← pow_succ]; exact hall (k + 1) le_rfl)) (fun d hd => ?_)
    subst hd
    refine Hs.mono (hs_copy C t5 t6 _ (by decide)) le_rfl ?_
    rintro e rfl
    refine ⟨by vsimp [b1, b2, pow_succ], by vsimp [b2], b3, b4, b5, ?_, ?_⟩
    · exact Cst.of_fr (T := [t5, t6]) b6 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))) (by decide)
        (by vsimp [b6.pos])
    · exact Fr.trans b7 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))

end NearCubicGates.Close.Dispatch
