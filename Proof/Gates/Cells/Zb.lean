import Proof.Gates.Cells.Blk

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

section Rank
variable {n : ℕ}

theorem idxOf_sorted : ∀ (L : List (Fin n)), L.Pairwise (· < ·) → ∀ x ∈ L, L.idxOf x = (L.filter (· < x)).length
  | [], _, x, hx => by simp at hx
  | a :: L, hs, x, hx => by
    rw [List.pairwise_cons] at hs
    by_cases hax : a = x
    · subst hax
      rw [List.idxOf_cons_self]
      have : L.filter (· < a) = [] := List.filter_eq_nil_iff.mpr (fun y hy => by
        have := hs.1 y hy; simp; exact le_of_lt this)
      simp [this]
    · have hxL : x ∈ L := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hax
        · exact h
      have hlt : a < x := hs.1 x hxL
      rw [List.idxOf_cons_ne _ (fun h => hax (by simpa using h)), idxOf_sorted L hs.2 x hxL]
      simp [List.filter_cons, hlt]

/-- The number of outer coordinates below `j`. -/
def rank (I : Finset (Fin n)) (j : ℕ) : ℕ := (Finset.univ.filter fun y : Fin n => y ∉ I ∧ y.val < j).card

theorem outer_sorted (I : Finset (Fin n)) : (outerCoords I).Pairwise (· < ·) :=
  List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort _)

theorem outer_idx (I : Finset (Fin n)) (x : Fin n) (hx : x ∉ I) : (outerCoords I).idxOf x = rank I x.val := by
  have hmem : x ∈ outerCoords I := by simp [outerCoords, hx]
  rw [idxOf_sorted _ (outer_sorted I) x hmem, rank]
  have hnd : (outerCoords I).Nodup := (outer_sorted I).imp ne_of_lt
  rw [← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter]
  congr 1
  ext y
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [outerCoords, Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

/-- **The point `z_y`.** -/
theorem zpt_eq (I : Finset (Fin n)) (i : ℕ) (j : Fin n) :
    extend I (cellOf I i) (zeroPoint I) j = if j ∈ I then false else i.testBit (rank I j.val) := by
  unfold extend
  split_ifs with h
  · rfl
  · simp only [cellOf]
    rw [outer_idx I j h]

theorem rank_succ (I : Finset (Fin n)) (j : ℕ) (hj : j < n) :
    rank I (j + 1) = rank I j + (if (⟨j, hj⟩ : Fin n) ∈ I then 0 else 1) := by
  unfold rank
  have : (Finset.univ.filter fun y : Fin n => y ∉ I ∧ y.val < j + 1) =
      (Finset.univ.filter fun y : Fin n => y ∉ I ∧ y.val < j) ∪
        (if (⟨j, hj⟩ : Fin n) ∈ I then ∅ else {⟨j, hj⟩}) := by
    ext y
    split_ifs with h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.union_empty]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h3 | h3
        · exact h3
        · exact absurd (by rw [show y = ⟨j, hj⟩ from Fin.ext h3]; exact h) h1
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h3 | h3
        · exact Or.inl ⟨h1, h3⟩
        · exact Or.inr (Fin.ext h3)
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨h1, by omega⟩
        · exact ⟨h, by simp⟩
  rw [this]
  split_ifs with h
  · simp
  · rw [Finset.card_union_of_disjoint (by simp [Finset.disjoint_singleton_right])]
    simp

end Rank

/-! ## The z-bits of a cell -/

section ZbP
variable {C : Ctx}

/-- The cell index. -/
def cI : Fin VV := ⟨41, by decide⟩

/-- The membership list of `I` (`1` at the inner coordinates). -/
def membL {n : ℕ} (I : Finset (Fin n)) : List ℕ := List.ofFn fun j : Fin n => if j ∈ I then 1 else 0

/-- The z-bits of cell `i`. -/
def zbL {n : ℕ} (I : Finset (Fin n)) (i : ℕ) : List ℕ :=
  List.ofFn fun j : Fin n => if j ∈ I then 0 else i / 2 ^ rank I j.val % 2

/-- Per cell: `sZb := zbL I i` from `sR = membL I` (`a5` holds `i / 2^{rank}`). -/
def zbP : St VV MM :=
  .seq (.op (.copy a5 cI)) (.seq (.op (.rwM sR)) (.seq (.op (.rwM sZb))
    (forS c2 gN (.seq (.op (.rdM sR a6)) (.seq (.ite (.eq a6 v1) (.op (.zero a7))
      (.seq (.op (.dm a5 v2 a8 a7)) (.op (.copy a5 a8)))) (.op (.wrM sZb a7)))))))

def zbT : List (Fin VV) := [a5, a6, a7, a8, c2, vJ]

theorem zbP_spec {n : ℕ} (I : Finset (Fin n)) (a : DS VV MM) (hc : Cst a) (hn : a.env gN = n) (hnW : n < 2 ^ C.Wd)
    (hW4 : 4 ≤ 2 ^ C.Wd) (hR : a.ram sR = membL I) (hold : (a.ram sZb).length ≤ n) :
    Hs C zbP a (1 + (a.rc sR + 1 + (a.rc sZb + 1 + (n * (8 + 4) + 4) + 1) + 1) + 1)
      (fun b => b.ram = Function.update a.ram sZb (zbL I (a.env cI)) ∧
        b.rc = Function.update (Function.update a.rc sR n) sZb n ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b zbT) := by
  set i := a.env cI with hi
  have hsd : sR ≠ sZb := by decide
  refine Hs.seq (hs_copy C a5 cI a (by decide)) (fun b1 hb1 => ?_)
  subst hb1
  refine Hs.seq (hs_rwM C sR _) (fun b2 hb2 => ?_)
  subst hb2
  refine Hs.seq (hs_rwM C sZb _) (fun b3 hb3 => ?_)
  subst hb3
  set s0 := ((a.set a5 (a.env cI)).rew sR).rew sZb
  set old := a.ram sZb
  have hlenR : (membL I).length = n := by simp [membL]
  have hlenZ : (zbL I i).length = n := by simp [zbL]
  let J : ℕ → DS VV MM → Prop := fun k e => e.env a5 = i / 2 ^ rank I k ∧
    e.ram = Function.update a.ram sZb ((zbL I i).take k ++ old.drop k) ∧
    e.rc = Function.update (Function.update a.rc sR k) sZb k ∧
    e.ip = a.ip ∧ e.out = a.out ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e zbT
  have hl := forS_spec' (C := C) c2 gN (by decide) (.seq (.op (.rdM sR a6)) (.seq (.ite (.eq a6 v1) (.op (.zero a7))
      (.seq (.op (.dm a5 v2 a8 a7)) (.op (.copy a5 a8)))) (.op (.wrM sZb a7)))) s0 n hnW J 8
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1, i2, i3, i4,
      i5, i6, i7, i8, Fr.trans i9 (Fr.set e v (by decide))⟩)
    ⟨by simp [s0, DS.rew, DS.set, rank, i], by simp [s0, DS.rew, DS.set, old],
      by funext m; simp only [s0, DS.rew, DS.set, Function.update_apply],
      by simp [s0, DS.rew, DS.set], by simp [s0, DS.rew, DS.set], by simp [s0, DS.rew, DS.set],
      by simp [s0, DS.rew, DS.set], by simp [s0, DS.rew, DS.set],
      fun y hy => by simp only [s0, DS.rew, DS.set]; rw [Function.update_of_ne (fun h => hy (by rw [h]; decide))]⟩
    (by simp only [s0, DS.rew, DS.set]; rw [Function.update_of_ne (by decide)]; exact hn) ?_
  · refine Hs.mono hl (by omega) ?_
    rintro e ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩, _, _⟩
    refine ⟨by rw [i2, List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil], i3, i4,
      i5, i6, i7, i8, i9⟩
  · intro k hk e ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ hek hem
    have hc' : Cst e := Cst.of_fr hc i9 (by decide)
    have eR : e.ram sR = membL I := by rw [i2, Function.update_of_ne hsd, hR]
    have eRc : e.rc sR = k := by rw [i3, Function.update_of_ne hsd]; simp
    have eZc : e.rc sZb = k := by rw [i3]; simp
    have eZ : e.ram sZb = (zbL I i).take k ++ old.drop k := by rw [i2]; simp
    have hmk : (membL I).getD k 0 = if (⟨k, hk⟩ : Fin n) ∈ I then 1 else 0 := by
      rw [List.getD_eq_getElem _ _ (by rw [hlenR]; exact hk)]; simp [membL]
    have hzk : (zbL I i)[k]'(by rw [hlenZ]; exact hk) =
        if (⟨k, hk⟩ : Fin n) ∈ I then 0 else i / 2 ^ rank I k % 2 := by simp [zbL]
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 4 + 1 + 1) (hs_rdM C sR a6 e (by rw [eRc, eR, hlenR]; exact hk))
      (fun f hf => ?_)) (by norm_num) (fun _ h => h)
    subst hf
    set f := (e.set a6 ((e.ram sR).getD (e.rc sR) 0)).adv sR with hfdef
    have f6 : f.env a6 = if (⟨k, hk⟩ : Fin n) ∈ I then 1 else 0 := by
      simp only [hfdef, DS.adv, DS.set_env_self, eR, eRc, hmk]
    have f5 : f.env a5 = i / 2 ^ rank I k := by simp only [hfdef, DS.adv]; vsimp [i1]
    have fv1 : f.env v1 = 1 := by simp only [hfdef, DS.adv]; vsimp [hc'.one]
    have fv2 : f.env v2 = 2 := by simp only [hfdef, DS.adv]; vsimp [hc'.two]
    -- the branch
    have hbr : Hs C (.ite (.eq a6 v1) (.op (.zero a7)) (.seq (.op (.dm a5 v2 a8 a7)) (.op (.copy a5 a8)))) f (3 + 1)
        (fun g => g.env a7 = (if (⟨k, hk⟩ : Fin n) ∈ I then 0 else i / 2 ^ rank I k % 2) ∧
          g.env a5 = i / 2 ^ rank I (k + 1) ∧ g.sh = f.sh ∧ Fr f g [a5, a7, a8, vJ]) := by
      refine Hs.ite (show a6 ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
      · have hin : (⟨k, hk⟩ : Fin n) ∈ I := by
          by_contra h; simp only [Cnd.eval, f6, fv1, if_neg h] at he; simp at he
        refine Hs.mono (hs_zero C a7 f) (by norm_num) ?_
        rintro g rfl
        refine ⟨by vsimp [if_pos hin], ?_, rfl, Fr.set f _ (by decide)⟩
        rw [DS.set_env_ne _ _ (by decide), f5, rank_succ I k hk, if_pos hin, Nat.add_zero]
      · have hin : (⟨k, hk⟩ : Fin n) ∉ I := by
          intro h; simp only [Cnd.eval, f6, fv1, if_pos h] at he; simp at he
        refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1) (hs_dm C a5 v2 a8 a7 f (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by rw [fv2]; norm_num) (by rw [fv2]; omega)) (fun g hg => ?_))
          (by norm_num) (fun _ h => h)
        subst hg
        refine Hs.mono (hs_copy C a5 a8 _ (by decide)) le_rfl ?_
        rintro g rfl
        refine ⟨by vsimp [if_neg hin, f5, fv2], ?_, rfl, ?_⟩
        · vsimp [f5, fv2]
          rw [rank_succ I k hk, if_neg hin, Nat.pow_succ, Nat.div_div_eq_div_mul]
        · exact Fr.trans (Fr.set f _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
    refine Hs.seq (t1 := 3 + 1) (t2 := 1) hbr (fun g ⟨g1, g2, g3, g4⟩ => ?_)
    have gs := Same.of_sh g3
    have hrcz : g.rc sZb ≤ (g.ram sZb).length := by
      rw [gs.rc, gs.ram]; simp only [hfdef, DS.adv, DS.set]
      rw [Function.update_of_ne (Ne.symm hsd), eZc, eZ]; simp; omega
    refine Hs.mono (hs_wrM C sZb a7 g hrcz) le_rfl ?_
    rintro r rfl
    have hef : Fr e f zbT := by
      intro y hy
      simp only [hfdef, DS.adv, DS.set]
      rw [Function.update_of_ne (fun h => hy (by rw [h]; decide))]
    have hfr : Fr a (g.put sZb (g.env a7)) zbT := Fr.trans i9 (Fr.trans hef (Fr.weaken g4 (by decide)))
    refine ⟨⟨by show g.env a5 = _; exact g2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr⟩, ?_, ?_⟩
    · simp only [DS.put]; rw [gs.ram, gs.rc]
      simp only [hfdef, DS.adv, DS.set]
      funext m; by_cases hm : m = sZb
      · subst hm
        simp only [Function.update_self]
        rw [Function.update_of_ne (Ne.symm hsd), eZc, i2]
        simp only [Function.update_self]
        have hlenk : ((zbL I i).take k).length = k := by simp; omega
        have hput := putAt_split ((zbL I i).take k) (old.drop k) (g.env a7)
        rw [hlenk] at hput
        rw [hput, g1, List.take_succ_eq_append_getElem (by rw [hlenZ]; exact hk), hzk]
        simp [List.drop_drop, List.append_assoc]
      · simp only [Function.update_of_ne hm]; rw [i2, Function.update_of_ne hm]
    · simp only [DS.put]; rw [gs.rc]; simp only [hfdef, DS.adv, DS.set]
      funext m; by_cases hm : m = sZb
      · subst hm; simp only [Function.update_self]; rw [Function.update_of_ne (Ne.symm hsd), eZc]
      · by_cases hm2 : m = sR
        · subst hm2; simp [Function.update_of_ne hsd, eRc]
        · simp [Function.update_of_ne hm, Function.update_of_ne hm2, i3]
    · simp only [DS.put]; rw [gs.ip]; simp [hfdef, DS.adv, DS.set, i4]
    · simp only [DS.put]; rw [gs.out]; simp [hfdef, DS.adv, DS.set, i5]
    · simp only [DS.put]; rw [gs.kin]; simp [hfdef, DS.adv, DS.set, i6]
    · simp only [DS.put]; rw [gs.kout]; simp [hfdef, DS.adv, DS.set, i7]
    · simp only [DS.put]; rw [gs.kc]; simp [hfdef, DS.adv, DS.set, i8]
    · show g.env c2 = k; rw [g4 c2 (by decide)]; simp only [hfdef, DS.adv]; vsimp [hek]
    · show g.env gN = n; rw [g4 gN (by decide)]; simp only [hfdef, DS.adv]; vsimp [hem]

end ZbP

end NearCubicGates.Close.Cells
