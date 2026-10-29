import SourceAdapters.ShortPCP.Machines.FLangSel

/-!
# Single-run time, machine layer 10: packed lists and the list builder

The verifier's lists of field words (bases of subspaces, answer lists, the points of Algorithm 21; proof of `thm:short-pcp-ours`)
are held in one number each (`packW w l`: word `j` at bits `j·w … j·w + w − 1`). This module gives the arithmetic of
packed lists (`take` = remainder, `drop` = quotient, append = sum) and one verified combinator: `genP` builds the
packed list `[g 0, …, g (m − 1)]` from a loop body that leaves `g j` in a variable (`genP_spec`). A routine built
with `genP` proves only its body.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5

variable (G : Glob)

/-! ## Packed lists -/

theorem packW_append (w : ℕ) : ∀ (l l' : List ℕ), packW w (l ++ l') = packW w l + 2 ^ (w * l.length) * packW w l'
  | [], l' => by simp [packW]
  | a :: l, l' => by
    simp only [List.cons_append, packW, packW_append w l l', List.length_cons, mul_add, mul_one, pow_add]
    ring

theorem packW_range_succ (w : ℕ) (g : ℕ → ℕ) (j : ℕ) :
    packW w ((List.range (j + 1)).map g) = packW w ((List.range j).map g) + g j * 2 ^ (j * w) := by
  rw [List.range_succ, List.map_append, packW_append]
  simp [packW, mul_comm]

theorem packW_take (w : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w) (k : ℕ) :
    packW w (l.take k) = packW w l % 2 ^ (w * k) := by
  rcases Nat.le_total k l.length with hk | hk
  · conv_rhs => rw [← List.take_append_drop k l]
    rw [packW_append, List.length_take, min_eq_left hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    have := packW_lt w (l.take k) (fun a ha => hl a (List.mem_of_mem_take ha))
    rwa [List.length_take, min_eq_left hk] at this
  · rw [List.take_of_length_le hk, Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le (packW_lt w l hl) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hk))

theorem packW_drop (w : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w) (k : ℕ) :
    packW w (l.drop k) = packW w l / 2 ^ (w * k) := by
  rcases Nat.le_total k l.length with hk | hk
  · conv_rhs => rw [← List.take_append_drop k l]
    have hlt := packW_lt w (l.take k) (fun a ha => hl a (List.mem_of_mem_take ha))
    rw [List.length_take, min_eq_left hk] at hlt
    rw [packW_append, List.length_take, min_eq_left hk, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt hlt, Nat.zero_add]
  · rw [List.drop_of_length_le hk, Nat.div_eq_of_lt]
    · rfl
    · exact lt_of_lt_of_le (packW_lt w l hl) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hk))

theorem packW_map_range_getD (w : ℕ) (g : ℕ → ℕ) (m j : ℕ) :
    ((List.range m).map g).getD j 0 = if j < m then g j else 0 := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, show m ≤ j by omega]

theorem cap_ge (G : Glob) : G.K ≤ G.cap := by
  unfold Glob.cap; have := Nat.lt_two_pow_self (n := G.K); omega

theorem pow_le_cap {G : Glob} {a : ℕ} (h : a ≤ G.K) : 2 ^ a ≤ G.cap + 1 := by
  unfold Glob.cap; have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
  have := Nat.one_le_two_pow (n := G.K); omega

theorem Wr.mono {W W' : List Var} {s t : FS} (h : Wr W s t) (hW : ∀ x ∈ W, x ∈ W') : Wr W' s t :=
  ⟨fun j hj => h.env j (fun h' => hj (hW j h')), h.out, h.fl, h.fp, h.bad⟩

/-! ## The list builder -/

/-- Build the packed list `[g 0, …, g (m − 1)]` (width in `wv`, `m` passes counted by `nv`) in `acc`; the body leaves
`g p` in `y` (loop variable `p`). -/
def genP (nv p y acc wv : Var) (body : S) : S :=
  .seq (.set acc (.k 0)) (.loop p (.v nv) (.seq body (.set acc (.add (.v acc) (.shl (.v y) (.mul (.v p) (.v wv)))))))

/-- **The list builder.** -/
theorem genP_spec (nv p y acc wv : Var) (body : S) (Wb : List Var) (s : FS) (m w : ℕ) (g : ℕ → ℕ)
    (hm : min (s.env nv) G.N = m) (hw : s.env wv = w) (hK : w * m ≤ G.K)
    (hap : acc ≠ p) (han : acc ≠ nv) (haw : acc ≠ wv) (hpw : p ≠ wv)
    (hacc : acc ∉ Wb) (hp : p ∉ Wb) (hwv : wv ∉ Wb)
    (hbody : ∀ j < m, ∀ t, Wr (acc :: p :: Wb) s t → t.env p = j →
      (evalS G body t).env y = g j ∧ g j < 2 ^ w ∧ Wr Wb t (evalS G body t)) :
    (evalS G (genP nv p y acc wv body) s).env acc = packW w ((List.range m).map g) ∧
      Wr (acc :: p :: Wb) s (evalS G (genP nv p y acc wv body) s) := by
  have hc0 : min 0 G.cap = 0 := by omega
  set s1 := s.setv acc (min 0 G.cap) with hs1
  have hn : min (evalE G s1 (.v nv)) G.N = m := by
    simp only [evalE, s1, FS.setv_env, Function.update_of_ne (Ne.symm han)]; exact hm
  have hl := loop_inv G (i := p) (n := .v nv) (s := s1)
    (body := .seq body (.set acc (.add (.v acc) (.shl (.v y) (.mul (.v p) (.v wv))))))
    (fun j t => t.env acc = packW w ((List.range j).map g) ∧ Wr (acc :: p :: Wb) s t)
    ⟨by simp [s1, hc0, packW], Wr.setv s (by simp) _⟩ (by
      rw [hn]
      rintro j hj t ⟨ta, tW⟩
      have t1W : Wr (acc :: p :: Wb) s (t.setv p j) := tW.trans (Wr.setv _ (by simp) _)
      obtain ⟨hy, hgy, bW⟩ := hbody j hj (t.setv p j) t1W (by simp)
      generalize ht2 : evalS G body (t.setv p j) = t2 at hy bW
      have t2a : t2.env acc = packW w ((List.range j).map g) := by
        rw [bW.env acc hacc]; simp [Function.update_of_ne hap, ta]
      have t2p : t2.env p = j := by rw [bW.env p hp]; simp
      have t2w : t2.env wv = w := by
        rw [bW.env wv hwv]; simp only [FS.setv_env, Function.update_of_ne (Ne.symm hpw)]
        rw [tW.env wv (by simp [Ne.symm haw, Ne.symm hpw, hwv])]; exact hw
      have hjw : j * w ≤ G.K := le_trans (by nlinarith) hK
      have hcj : min (j * w) G.cap = j * w := min_eq_left (le_trans hjw (cap_ge G))
      have hpk := pow_le_cap (G := G) (a := w * m) hK
      have hpj : 2 ^ (j * w) * 2 ^ w ≤ 2 ^ (w * m) := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have hlt := packW_lt w ((List.range j).map g) (by
        intro a ha; simp only [List.mem_map, List.mem_range] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact (hbody b (by omega) (s.setv p b) (Wr.setv s (by simp) _) (by simp)).2.1)
      rw [List.length_map, List.length_range, mul_comm] at hlt
      have hg1 : g j * 2 ^ (j * w) + 2 ^ (j * w) ≤ 2 ^ (j * w) * 2 ^ w := by
        rw [mul_comm (2 ^ (j * w))]; nlinarith
      have e1 : min (g j * 2 ^ (j * w)) G.cap = g j * 2 ^ (j * w) := by omega
      have e2 : min (packW w ((List.range j).map g) + g j * 2 ^ (j * w)) G.cap =
          packW w ((List.range j).map g) + g j * 2 ^ (j * w) := by omega
      refine ⟨?_, ?_⟩
      · simp only [evalS_seq, evalS_set, ht2, FS.setv_env, Function.update_self, evalE, t2a, t2p, t2w, hy, hcj, e1,
          e2]
        rw [packW_range_succ]
      · simp only [evalS_seq, evalS_set, ht2]
        exact (t1W.trans (bW.mono (fun x hx => by simp [hx]))).trans (Wr.setv _ (by simp) _))
  rw [hn] at hl
  exact hl

/-- **The list builder, with the body reading the entries built so far** (a table filled by a recursion). -/
theorem genP2_spec (nv p y acc wv : Var) (body : S) (Wb : List Var) (s : FS) (m w : ℕ) (g : ℕ → ℕ)
    (hm : min (s.env nv) G.N = m) (hw : s.env wv = w) (hK : w * m ≤ G.K)
    (hap : acc ≠ p) (han : acc ≠ nv) (haw : acc ≠ wv) (hpw : p ≠ wv)
    (hacc : acc ∉ Wb) (hp : p ∉ Wb) (hwv : wv ∉ Wb)
    (hgw : ∀ j < m, g j < 2 ^ w)
    (hbody : ∀ j < m, ∀ t, Wr (acc :: p :: Wb) s t → t.env p = j → t.env acc = packW w ((List.range j).map g) →
      (evalS G body t).env y = g j ∧ Wr Wb t (evalS G body t)) :
    (evalS G (genP nv p y acc wv body) s).env acc = packW w ((List.range m).map g) ∧
      Wr (acc :: p :: Wb) s (evalS G (genP nv p y acc wv body) s) := by
  have hc0 : min 0 G.cap = 0 := by omega
  set s1 := s.setv acc (min 0 G.cap) with hs1
  have hn : min (evalE G s1 (.v nv)) G.N = m := by
    simp only [evalE, s1, FS.setv_env, Function.update_of_ne (Ne.symm han)]; exact hm
  have hl := loop_inv G (i := p) (n := .v nv) (s := s1)
    (body := .seq body (.set acc (.add (.v acc) (.shl (.v y) (.mul (.v p) (.v wv))))))
    (fun j t => t.env acc = packW w ((List.range j).map g) ∧ Wr (acc :: p :: Wb) s t)
    ⟨by simp [s1, hc0, packW], Wr.setv s (by simp) _⟩ (by
      rw [hn]
      rintro j hj t ⟨ta, tW⟩
      have t1W : Wr (acc :: p :: Wb) s (t.setv p j) := tW.trans (Wr.setv _ (by simp) _)
      obtain ⟨hy, bW⟩ := hbody j hj (t.setv p j) t1W (by simp) (by simp [Function.update_of_ne hap, ta])
      have hgy := hgw j hj
      generalize ht2 : evalS G body (t.setv p j) = t2 at hy bW
      have t2a : t2.env acc = packW w ((List.range j).map g) := by
        rw [bW.env acc hacc]; simp [Function.update_of_ne hap, ta]
      have t2p : t2.env p = j := by rw [bW.env p hp]; simp
      have t2w : t2.env wv = w := by
        rw [bW.env wv hwv]; simp only [FS.setv_env, Function.update_of_ne (Ne.symm hpw)]
        rw [tW.env wv (by simp [Ne.symm haw, Ne.symm hpw, hwv])]; exact hw
      have hjw : j * w ≤ G.K := le_trans (by nlinarith) hK
      have hcj : min (j * w) G.cap = j * w := min_eq_left (le_trans hjw (cap_ge G))
      have hpk := pow_le_cap (G := G) (a := w * m) hK
      have hpj : 2 ^ (j * w) * 2 ^ w ≤ 2 ^ (w * m) := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have hlt := packW_lt w ((List.range j).map g) (by
        intro a ha; simp only [List.mem_map, List.mem_range] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact hgw b (by omega))
      rw [List.length_map, List.length_range, mul_comm] at hlt
      have hg1 : g j * 2 ^ (j * w) + 2 ^ (j * w) ≤ 2 ^ (j * w) * 2 ^ w := by
        rw [mul_comm (2 ^ (j * w))]; nlinarith
      have e1 : min (g j * 2 ^ (j * w)) G.cap = g j * 2 ^ (j * w) := by omega
      have e2 : min (packW w ((List.range j).map g) + g j * 2 ^ (j * w)) G.cap =
          packW w ((List.range j).map g) + g j * 2 ^ (j * w) := by omega
      refine ⟨?_, ?_⟩
      · simp only [evalS_seq, evalS_set, ht2, FS.setv_env, Function.update_self, evalE, t2a, t2p, t2w, hy, hcj, e1,
          e2]
        rw [packW_range_succ]
      · simp only [evalS_seq, evalS_set, ht2]
        exact (t1W.trans (bW.mono (fun x hx => by simp [hx]))).trans (Wr.setv _ (by simp) _))
  rw [hn] at hl
  exact hl

end NearCubicGates.Adapters.ShortPCP.Machines.FL
