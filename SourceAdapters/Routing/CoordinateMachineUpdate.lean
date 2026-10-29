import SourceAdapters.Routing.CoordinateMachineOps

/-!
# The two coefficient updates of the coordinate solver

The construction in `lem:generator`: the triangular coordinate construction updates its annihilator and one coordinate row using
reduced field arithmetic. `rowProgram` and `annProgram` are actual counted programs, with exact packed-list results.
Registers 25 and 26 store the old annihilator and row; 28 stores the pivot, 29 the row value, 30 its inverse pivot.
The builders write 32 and 31 respectively, using loop registers 35–37 and preserving the old vectors.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicGates.Adapters.ShortPCP.Machines.FL

/-- One coefficient of the updated coordinate row, in reduced masks. -/
noncomputable def rowValue (p f a n pinv v : ℕ) (L R : List ℕ) (j : ℕ) : ℕ :=
  if a = n then mulW p f pinv (L.getD j 0)
  else R.getD j 0 ^^^ mulW p f v (mulW p f pinv (L.getD j 0))

/-- One coefficient of the updated annihilator, in reduced masks. -/
noncomputable def annValue (p f pivot : ℕ) (L : List ℕ) (j : ℕ) : ℕ :=
  (if j = 0 then 0 else mulW p f (L.getD (j - 1) 0) (L.getD (j - 1) 0)) ^^^
    mulW p f pivot (L.getD j 0)

theorem rowValue_lt (p f a n pinv v : ℕ) (L R : List ℕ)
    (hR : ∀ x ∈ R, x < 2 ^ f) (j : ℕ) : rowValue p f a n pinv v L R j < 2 ^ f := by
  unfold rowValue
  split
  · exact mulW_lt _ _ _ _
  · exact Nat.xor_lt_two_pow (getD_reduced f R hR j) (mulW_lt _ _ _ _)

theorem annValue_lt (p f pivot : ℕ) (L : List ℕ) (j : ℕ) : annValue p f pivot L j < 2 ^ f := by
  apply Nat.xor_lt_two_pow _ (mulW_lt _ _ _ _)
  split
  · positivity
  · exact mulW_lt _ _ _ _

/-- The update of one row coefficient, with coefficient index in 36 and result in 37. -/
def rowBody : S :=
  .ite (.eq (.v 23) (.v 24))
    (.set 37 (.fmul (.v 30) (getC 25 (.v 36))))
    (.set 37 (.fadd (getC 26 (.v 36)) (.fmul (.v 29) (.fmul (.v 30) (getC 25 (.v 36))))))

/-- The update of one annihilator coefficient. -/
def annBody : S :=
  .ite (.eq (.v 36) (.k 0))
    (.set 37 (.fmul (.v 28) (getC 25 (.v 36))))
    (.set 37 (.fadd
      (.fmul (getC 25 (.sub (.v 36) (.k 1))) (getC 25 (.sub (.v 36) (.k 1))))
      (.fmul (.v 28) (getC 25 (.v 36)))))

/-- Build the updated row of length stored in 35, without overwriting the old vectors. -/
def rowProgram : S := genP 35 36 37 32 20 rowBody

/-- Build the updated annihilator of length stored in 35, without overwriting the old vectors. -/
def annProgram : S := genP 35 36 37 31 20 annBody

theorem rowBody_spec (G : Glob) (s : FS) (L R : List ℕ) (j : ℕ)
    (hL : ∀ x ∈ L, x < 2 ^ s.fl) (hR : ∀ x ∈ R, x < 2 ^ s.fl)
    (h20 : s.env 20 = s.fl) (h25 : s.env 25 = packW s.fl L) (h26 : s.env 26 = packW s.fl R)
    (h36 : s.env 36 = j) (hv : s.env 29 < 2 ^ s.fl) (hp : s.env 30 < 2 ^ s.fl)
    (hj : j * s.fl ≤ G.K) (hw : s.fl + 1 ≤ G.K) :
    (evalS G rowBody s).env 37 = rowValue s.fp s.fl (s.env 23) (s.env 24) (s.env 30) (s.env 29) L R j ∧
      Wr [37] s (evalS G rowBody s) := by
  have hgetL := getC_eval G s 25 (.v 36) s.fl j L hL h25 h20 h36 hj hw
  have hgetR := getC_eval G s 26 (.v 36) s.fl j R hR h26 h20 h36 hj hw
  have hunit := eval_fmul G s (.v 30) (getC 25 (.v 36)) (s.env 30) (L.getD j 0)
    rfl hgetL hp (getD_reduced _ _ hL j)
  have hprod := eval_fmul G s (.v 29) (.fmul (.v 30) (getC 25 (.v 36)))
    (s.env 29) (mulW s.fp s.fl (s.env 30) (L.getD j 0)) rfl hunit hv (mulW_lt _ _ _ _)
  have hadd := eval_fadd G s (getC 26 (.v 36)) (.fmul (.v 29) (.fmul (.v 30) (getC 25 (.v 36))))
    (R.getD j 0) (mulW s.fp s.fl (s.env 29) (mulW s.fp s.fl (s.env 30) (L.getD j 0)))
    hgetR hprod (getD_reduced _ _ hR j) (mulW_lt _ _ _ _)
  have htest : evalE G s (.eq (.v 23) (.v 24)) = if s.env 23 = s.env 24 then 1 else 0 := rfl
  by_cases he : s.env 23 = s.env 24
  · simp only [rowBody, evalS_ite, htest, he, if_true, one_ne_zero, if_false, evalS_set]
    exact ⟨by simpa only [FS.setv_env, Function.update_self, rowValue, he, if_true] using hunit,
      Wr.setv _ (by simp) _⟩
  · simp only [rowBody, evalS_ite, htest, he, if_false, if_true, evalS_set]
    exact ⟨by simpa only [FS.setv_env, Function.update_self, rowValue, he, if_false] using hadd,
      Wr.setv _ (by simp) _⟩

theorem annBody_spec (G : Glob) (s : FS) (L : List ℕ) (j : ℕ)
    (hL : ∀ x ∈ L, x < 2 ^ s.fl) (h20 : s.env 20 = s.fl) (h25 : s.env 25 = packW s.fl L)
    (h36 : s.env 36 = j) (hp : s.env 28 < 2 ^ s.fl)
    (hj : j * s.fl ≤ G.K) (hw : s.fl + 1 ≤ G.K) :
    (evalS G annBody s).env 37 = annValue s.fp s.fl (s.env 28) L j ∧
      Wr [37] s (evalS G annBody s) := by
  have hget := getC_eval G s 25 (.v 36) s.fl j L hL h25 h20 h36 hj hw
  have hmul := eval_fmul G s (.v 28) (getC 25 (.v 36)) (s.env 28) (L.getD j 0)
    rfl hget hp (getD_reduced _ _ hL j)
  have hc1 : min 1 G.cap = 1 := by have := cap_ge G; omega
  have hc0 : min 0 G.cap = 0 := by omega
  have hprev := getC_eval G s 25 (.sub (.v 36) (.k 1)) s.fl (j - 1) L hL h25 h20
    (by simp only [evalE, h36, hc1])
    (le_trans (Nat.mul_le_mul_right _ (Nat.sub_le j 1)) hj) hw
  have hsq := eval_fmul G s (getC 25 (.sub (.v 36) (.k 1))) (getC 25 (.sub (.v 36) (.k 1)))
    (L.getD (j - 1) 0) (L.getD (j - 1) 0) hprev hprev
    (getD_reduced _ _ hL _) (getD_reduced _ _ hL _)
  have hadd := eval_fadd G s
    (.fmul (getC 25 (.sub (.v 36) (.k 1))) (getC 25 (.sub (.v 36) (.k 1))))
    (.fmul (.v 28) (getC 25 (.v 36)))
    (mulW s.fp s.fl (L.getD (j - 1) 0) (L.getD (j - 1) 0))
    (mulW s.fp s.fl (s.env 28) (L.getD j 0)) hsq hmul (mulW_lt _ _ _ _) (mulW_lt _ _ _ _)
  have htest : evalE G s (.eq (.v 36) (.k 0)) = if j = 0 then 1 else 0 := by
    simp only [evalE, h36, hc0]
  by_cases he : j = 0
  · simp only [annBody, evalS_ite, htest, he, if_true, one_ne_zero, if_false, evalS_set]
    exact ⟨by simpa only [FS.setv_env, Function.update_self, annValue, he, if_true, Nat.zero_xor] using hmul,
      Wr.setv _ (by simp) _⟩
  · simp only [annBody, evalS_ite, htest, he, if_false, if_true, evalS_set]
    exact ⟨by simpa only [FS.setv_env, Function.update_self, annValue, he, if_false] using hadd,
      Wr.setv _ (by simp) _⟩

/-- The packed coordinate row update, retaining every old coefficient until the whole new row has been built. -/
theorem rowProgram_spec (G : Glob) (s : FS) (L R : List ℕ) (count : ℕ)
    (hL : ∀ x ∈ L, x < 2 ^ s.fl) (hR : ∀ x ∈ R, x < 2 ^ s.fl)
    (h20 : s.env 20 = s.fl) (h25 : s.env 25 = packW s.fl L) (h26 : s.env 26 = packW s.fl R)
    (hv : s.env 29 < 2 ^ s.fl) (hp : s.env 30 < 2 ^ s.fl)
    (hc : min (s.env 35) G.N = count) (hK : s.fl * count ≤ G.K) (hw : s.fl + 1 ≤ G.K) :
    (evalS G rowProgram s).env 32 =
      packW s.fl ((List.range count).map (rowValue s.fp s.fl (s.env 23) (s.env 24) (s.env 30) (s.env 29) L R)) ∧
      Wr [32, 36, 37] s (evalS G rowProgram s) ∧ (evalS G rowProgram s).ip = s.ip := by
  have hb := genP_spec G 35 36 37 32 20 rowBody [37] s count s.fl
    (rowValue s.fp s.fl (s.env 23) (s.env 24) (s.env 30) (s.env 29) L R)
    hc h20 hK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj t ht ht36
      have hf := ht.fl
      have htp := ht.fp
      have h23 := ht.env 23 (by decide)
      have h24 := ht.env 24 (by decide)
      have h29 := ht.env 29 (by decide)
      have h30 := ht.env 30 (by decide)
      have hbody := rowBody_spec G t L R j
        (by simpa only [hf] using hL) (by simpa only [hf] using hR)
        (by rw [ht.env 20 (by decide), hf, h20])
        (by rw [ht.env 25 (by decide), hf, h25])
        (by rw [ht.env 26 (by decide), hf, h26]) ht36
        (by simpa only [h29, hf] using hv) (by simpa only [h30, hf] using hp)
        (by rw [hf]; exact le_trans (by nlinarith) hK) (by simpa only [hf] using hw)
      refine ⟨?_, rowValue_lt _ _ _ _ _ _ L R hR j, hbody.2⟩
      simpa only [hf, htp, h23, h24, h29, h30] using hbody.1)
  exact ⟨hb.1, hb.2, inputFree_ip G rowProgram (by decide) s⟩

/-- The packed annihilator update, including its new leading coefficient. -/
theorem annProgram_spec (G : Glob) (s : FS) (L : List ℕ) (count : ℕ)
    (hL : ∀ x ∈ L, x < 2 ^ s.fl) (h20 : s.env 20 = s.fl) (h25 : s.env 25 = packW s.fl L)
    (hp : s.env 28 < 2 ^ s.fl) (hc : min (s.env 35) G.N = count)
    (hK : s.fl * count ≤ G.K) (hw : s.fl + 1 ≤ G.K) :
    (evalS G annProgram s).env 31 =
      packW s.fl ((List.range count).map (annValue s.fp s.fl (s.env 28) L)) ∧
      Wr [31, 36, 37] s (evalS G annProgram s) ∧ (evalS G annProgram s).ip = s.ip := by
  have hb := genP_spec G 35 36 37 31 20 annBody [37] s count s.fl (annValue s.fp s.fl (s.env 28) L)
    hc h20 hK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj t ht ht36
      have hf := ht.fl
      have htp := ht.fp
      have h28 := ht.env 28 (by decide)
      have hbody := annBody_spec G t L j
        (by simpa only [hf] using hL)
        (by rw [ht.env 20 (by decide), hf, h20])
        (by rw [ht.env 25 (by decide), hf, h25]) ht36
        (by simpa only [h28, hf] using hp)
        (by rw [hf]; exact le_trans (by nlinarith) hK) (by simpa only [hf] using hw)
      refine ⟨?_, annValue_lt _ _ _ L j, hbody.2⟩
      simpa only [hf, htp, h28] using hbody.1)
  exact ⟨hb.1, hb.2, inputFree_ip G annProgram (by decide) s⟩

end NearCubicGates.Adapters.Routing.CoordinateMachine
