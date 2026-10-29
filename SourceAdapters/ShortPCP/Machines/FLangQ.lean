import SourceAdapters.ShortPCP.Machines.FLangRand

/-!
# Single-run time, machine layer 22: the query maps of `V_{RS,=}` and `V_{RS,<}`

BCGT13 Lemma 12.16 (`Q_{RS,=}`: the index `Translate` returns) and Algorithm 15 (`Q_{RS,<}`: two runs of `Q_{RS,=}`, the
second shifted past the first proof); proof of `thm:short-pcp-ours` ("A single run of V_RS or V_VRS takes poly(f) field
operations"), proof of `thm:short-pcp-ours` ("The queries of V0 are computed from the random string alone"). Every sub-verifier of `V0`
runs on the domain `F` with basis `DOM` (in `19`, `κ = f`) and offset `0` (`Joins/SingleRun.lean`, `domBasis`).
`trQ e` runs `Translate` on the index `e` and leaves `Q_{RS,=}` in `9` (`trQ_spec`); `qLtP` computes `Q_{RS,<}` at the
index in `5` (`qLtP_spec`). The flag `8 = 1` marks a query (`8 = 0`: none).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

/-! ## Indices -/

/-- The index of a `Translate` result. -/
def trIdx {F : Type} : TrOut F → ℕ
  | .inp _ j => j
  | .prf j => j

theorem TRep.idx {F : Type} [Field F] {p : ℕ} {φ : AdjoinRoot (GF.toPoly p) →+* F} {w : ℕ} {s : FS} {r : TrOut F}
    (h : TRep φ w s r) : s.env 54 = trIdx r := by
  cases r with
  | inp α j => exact h.2.2.2.1
  | prf j => exact h.2

theorem qEqF_eq_idx {F : Type} [Field F] [DecidableEq F] (B : List F) (O : F) (r : List Bool) (i : ℕ) :
    qEqF B O r i = some (trIdx (translateF B.length B O r i)) := by
  unfold qEqF; cases translateF B.length B O r i <;> rfl

/-! ## The parameters (domain `DOM`, `κ = f` in `23`) -/

/-- `n_S = 2^f`. -/
def nSE : E := pw (.v 23)

/-- `query_{RS,=}(f) = 2^{min f 4}` (`queryEq_eq`). -/
def qEE : E := pw (.sub (.v 23) (.sub (.v 23) (.k 4)))

/-- `length_{RS,=}(f)` from the table. -/
def lEE : E := getT (.v 23)

theorem qEE_eval {s : FS} {f : ℕ} (h23 : s.env 23 = f) (hK : f + 5 ≤ G.K) : evalE G s qEE = queryEq T0 f := by
  rw [queryEq_eq, qEE, eE_pow (eE_sub (eE_v 23) (eE_sub (eE_v 23) (eE_k (by have := cap_ge G; omega)))) (by
    rw [h23]; omega), h23]
  congr 1; rw [Nat.min_def]; split_ifs <;> omega

theorem nSE_eval {s : FS} {f : ℕ} (h23 : s.env 23 = f) (hK : f + 1 ≤ G.K) : evalE G s nSE = 2 ^ f := by
  rw [nSE, eE_pow (eE_v 23) (by rw [h23]; exact hK), h23]

theorem lEE_eval {s : FS} {f : ℕ} (h23 : s.env 23 = f) (htb : TblRep s f) (hK : (f + 1) * (8 * f + 16) + 1 ≤ G.K) :
    evalE G s lEE = lengthEq T0 f := htb.len G (eE_v 23 |>.trans h23) le_rfl hK

/-! ## `Q_{RS,=}` -/

/-- `Q_{RS,=}` at the index `e`: `8 := 1`, `9 :=` the index `Translate` returns. -/
def trQ (e : E) : S := .seq (.set 51 e) (.seq transP (.seq (.set 8 (.k 1)) (.set 9 (.v 54))))

/-- The variables `trQ` writes. -/
def trW : List Var := [8, 9, 51] ++ transW

/-- **`Q_{RS,=}`** on the first level `(DOM, 0, u)`. -/
theorem trQ_spec {F : Type} [Field F] [CharP F 2] [DecidableEq F] (s : FS)
    (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 : List ℕ) (e : E) (i : ℕ)
    (h19 : s.env 19 = packW s.fl l0) (hl0 : l0.length = s.fl) (hl0w : ∀ a ∈ l0, a < 2 ^ s.fl)
    (h23 : s.env 23 = s.fl) (h42 : s.env 42 = bitsValue u) (h43 : s.env 43 = u.length) (he : evalE G s e = i)
    (hi : i ≤ 2 ^ s.fl) (hok : fieldOk G s.fl s.fp = true) (hirr : Irreducible (GF.toPoly s.fp))
    (htb : TblRep s s.fl) (hK : (s.fl + 1) * (8 * s.fl + 16) + 1 ≤ G.K) (hN : s.fl + 1 ≤ G.N) :
    let t := evalS G (trQ e) s
    qEqF (l0.map (ev φ)) 0 u i = some (t.env 9) ∧ t.env 8 = 1 ∧
      t.env 9 ≤ 2 ^ s.fl + s.fl * 2 ^ (9 * s.fl + 20) ∧ Wr trW s t := by
  intro t
  obtain ⟨hf1, hfK, -, -⟩ := fl_bounds hok
  obtain ⟨tR, tW, t54⟩ := transP_spec G (s.setv 51 i) φ u l0 i (by simp [h19]) hl0 hl0w (by simp [h23])
    (by simp [h42]) (by simp [h43]) (by simp) hi hok hirr (htb.congr (by simp) (by simp)) hK hN
  generalize ht1 : evalS G transP (s.setv 51 i) = t1 at tR tW t54
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have ht : t = (t1.setv 8 1).setv 9 (t1.env 54) := by
    show evalS G (trQ e) s = _
    simp only [trQ, evalS_seq, evalS_set, he, ht1, evalE, hc1]
    rfl
  rw [ht]
  refine ⟨?_, by simp, by simpa using t54, ?_⟩
  · have e54 : t1.env 54 = trIdx (translateF s.fl (l0.map (ev φ)) 0 u i) := tR.idx
    rw [qEqF_eq_idx, List.length_map, hl0, ← e54]; simp
  · exact ((((Wr.setv (W := trW) s (by decide) _).trans (tW.mono (by decide))).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _))

/-! ## `Q_{RS,<}` -/

/-- **`Q_{RS,<}`** (Algorithm 15) at the index in `5`. -/
def qLtP : S :=
  .ite (.lt (.v 5) (.add qEE (.k 1))) (trQ (.v 5))
    (.seq (trQ (.sub (.v 5) qEE))
      (.ite (.mul (.lt (.k 0) (.v 9)) (.lt (.v 9) (.add nSE (.k 1)))) .skip (.set 9 (.add lEE (.v 9)))))

/-- **`Q_{RS,<}`** on the first level, for `1 ≤ i ≤ query`. -/
theorem qLtP_spec {F : Type} [Field F] [CharP F 2] [DecidableEq F] (s : FS)
    (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 : List ℕ) (d i : ℕ)
    (h19 : s.env 19 = packW s.fl l0) (hl0 : l0.length = s.fl) (hl0w : ∀ a ∈ l0, a < 2 ^ s.fl)
    (h23 : s.env 23 = s.fl) (h42 : s.env 42 = bitsValue u) (h43 : s.env 43 = u.length) (h5 : s.env 5 = i)
    (hi1 : 1 ≤ i) (hiq : i ≤ 2 * queryEq T0 s.fl) (hok : fieldOk G s.fl s.fp = true)
    (hirr : Irreducible (GF.toPoly s.fp)) (htb : TblRep s s.fl) (hK : (s.fl + 1) * (8 * s.fl + 16) + 1 ≤ G.K)
    (hN : s.fl + 1 ≤ G.N) :
    let t := evalS G qLtP s
    (vLtF (l0.map (ev φ)) 0 d).Q u i = some (t.env 9) ∧ t.env 8 = 1 ∧
      t.env 9 ≤ lengthEq T0 s.fl + 2 ^ s.fl + s.fl * 2 ^ (9 * s.fl + 20) ∧ Wr trW s t := by
  intro t
  obtain ⟨hf1, hfK, -, -⟩ := fl_bounds hok
  obtain ⟨hK1, hK2, P0, PP⟩ := case_nums s.fl G.K hf1 hK
  have hcb := cap_big s.fl s.fl G hf1 hK
  have hcap := cap_ge G
  have hqE : evalE G s qEE = queryEq T0 s.fl := qEE_eval G h23 (by omega)
  have hqf : queryEq T0 s.fl ≤ 2 ^ s.fl := by
    rw [queryEq_eq]; exact Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
  have hq16 : queryEq T0 s.fl ≤ 16 := by
    rw [queryEq_eq]; exact (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans (by norm_num)
  have hlen : (l0.map (ev φ)).length = s.fl := by rw [List.length_map, hl0]
  have hLE : lengthEq T0 s.fl < 2 ^ (8 * s.fl + 16) := lengthEq_lt _
  have hL9 : 2 ^ (8 * s.fl + 16) ≤ 2 ^ (9 * s.fl + 16) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP1 : s.fl * 2 ^ (9 * s.fl + 20) ≤ (s.fl + 1) * 2 ^ (9 * s.fl + 20) := Nat.mul_le_mul_right _ (by omega)
  have e6 : (s.fl + 1) * 2 ^ (9 * s.fl + 20) = s.fl * 2 ^ (9 * s.fl + 20) + 2 ^ (9 * s.fl + 20) := by ring
  have htf := tf_le hok
  have hc : evalE G s (.lt (.v 5) (.add qEE (.k 1))) = if i < queryEq T0 s.fl + 1 then 1 else 0 :=
    eE_lt h5 (eE_add hqE (eE_k (by omega)) (by omega))
  by_cases hle : i ≤ queryEq T0 s.fl
  · obtain ⟨q1, q8, q9, qW⟩ := trQ_spec G s φ u l0 (.v 5) i h19 hl0 hl0w h23 h42 h43 h5 (by omega) hok hirr htb hK hN
    have ht : t = evalS G (trQ (.v 5)) s := by
      show evalS G qLtP s = _
      rw [qLtP, evalS_ite, hc, if_pos (show i < queryEq T0 s.fl + 1 by omega), if_neg one_ne_zero]
    rw [ht]
    refine ⟨?_, q8, by omega, qW⟩
    simp only [vLtF, hlen, if_pos (show 1 ≤ i ∧ i ≤ queryEq T0 s.fl from ⟨hi1, hle⟩)]
    exact q1
  · have he : evalE G s (.sub (.v 5) qEE) = i - queryEq T0 s.fl := eE_sub h5 hqE
    obtain ⟨q1, q8, q9, qW⟩ := trQ_spec G s φ u l0 (.sub (.v 5) qEE) (i - queryEq T0 s.fl) h19 hl0 hl0w h23 h42 h43
      he (by omega) hok hirr htb hK hN
    generalize ht1 : evalS G (trQ (.sub (.v 5) qEE)) s = t1 at q1 q8 q9 qW
    have t23 : t1.env 23 = s.fl := (qW.env 23 (by decide)).trans h23
    have htb1 : TblRep t1 s.fl := htb.of_wr qW (by decide) (by decide)
    have hn : evalE G t1 nSE = 2 ^ s.fl := nSE_eval G t23 (by omega)
    have hl : evalE G t1 lEE = lengthEq T0 s.fl := lEE_eval G t23 htb1 hK
    have hn1 : evalE G t1 (.add nSE (.k 1)) = 2 ^ s.fl + 1 := eE_add hn (eE_k (by omega)) (by omega)
    have hc2 : evalE G t1 (.mul (.lt (.k 0) (.v 9)) (.lt (.v 9) (.add nSE (.k 1)))) =
        if 0 < t1.env 9 ∧ t1.env 9 ≤ 2 ^ s.fl then 1 else 0 := by
      rw [eE_mul (eE_lt (eE_k (Nat.zero_le _)) (eE_v 9)) (eE_lt (eE_v 9) hn1) (by split_ifs <;> omega)]
      split_ifs <;> first | rfl | omega
    have hpre : t = evalS G (.ite (.mul (.lt (.k 0) (.v 9)) (.lt (.v 9) (.add nSE (.k 1)))) .skip
        (.set 9 (.add lEE (.v 9)))) t1 := by
      show evalS G qLtP s = _
      rw [qLtP, evalS_ite, hc, if_neg (show ¬ i < queryEq T0 s.fl + 1 by omega), if_pos rfl, evalS_seq, ht1]
    have hvl : (vLtF (l0.map (ev φ)) 0 d).Q u i =
        if 0 < t1.env 9 ∧ t1.env 9 ≤ 2 ^ s.fl then some (t1.env 9) else some (lengthEq T0 s.fl + t1.env 9) := by
      simp only [vLtF, hlen, if_neg (show ¬ (1 ≤ i ∧ i ≤ queryEq T0 s.fl) by omega)]
      rw [q1]
    by_cases hin : 0 < t1.env 9 ∧ t1.env 9 ≤ 2 ^ s.fl
    · rw [hpre, evalS_ite, hc2, if_pos hin, if_neg one_ne_zero, evalS_skip, hvl, if_pos hin]
      exact ⟨rfl, q8, by omega, qW⟩
    · have hv : evalE G t1 (.add lEE (.v 9)) = lengthEq T0 s.fl + t1.env 9 := eE_add hl (eE_v 9) (by omega)
      rw [hpre, evalS_ite, hc2, if_neg hin, if_pos rfl, evalS_set, hv, hvl, if_neg hin]
      exact ⟨by simp, by simpa using q8, by simp; omega, qW.trans (Wr.setv _ (by decide) _)⟩

end NearCubicGates.Adapters.ShortPCP.Machines.FL
