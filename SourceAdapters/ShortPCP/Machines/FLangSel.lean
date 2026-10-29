import SourceAdapters.ShortPCP.Machines.FLangLib
import SourceAdapters.ShortPCP.TimeSubspace
import SourceAdapters.ShortPCP.Machines.FLangOps

/-!
# Single-run time, machine layer 9: packed bases and `Σ_j (bit j of v)·B_j`

Bases of affine subspaces of `F` (BCGT13 Algorithms 19–21; proof of `thm:short-pcp-ours`) are lists of field elements; an `FL`
program holds a list of `f`-bit words in one number (`packW`, word `j` at bits `j·f … j·f + f − 1`). `selP` computes the
word of `Time.sel B v = Σ_j (bit j of v)·B_j` (GetRandElt and GetEltWithIndex are `sel` plus the offset,
`Time.getRandElt_eq`, `Time.eltWithIndex_eq`), one field sum per basis element (proof of `thm:short-pcp-ours`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time

variable (G : Glob)

/-- A packed list of `w`-bit words. -/
def packW (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 2 ^ w * packW w l

theorem packW_lt (w : ℕ) : ∀ (l : List ℕ), (∀ a ∈ l, a < 2 ^ w) → packW w l < 2 ^ (w * l.length)
  | [], _ => by simp [packW]
  | a :: l, h => by
    have ha := h a (by simp)
    have hl := packW_lt w l (fun b hb => h b (by simp [hb]))
    simp only [packW, List.length_cons, mul_add, mul_one, pow_add]
    have : 2 ^ w * packW w l + 2 ^ w ≤ 2 ^ w * 2 ^ (w * l.length) := by
      rw [← mul_add_one]; exact Nat.mul_le_mul_left _ hl
    rw [mul_comm (2 ^ (w * l.length))]; omega

theorem packW_get (w : ℕ) : ∀ (l : List ℕ), (∀ a ∈ l, a < 2 ^ w) → ∀ j, packW w l / 2 ^ (j * w) % 2 ^ w = l.getD j 0
  | [], _, j => by simp [packW]
  | a :: l, h, 0 => by
    have ha := h a (by simp)
    simp only [packW, zero_mul, pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  | a :: l, h, j + 1 => by
    have ha := h a (by simp)
    simp only [packW, List.getD_cons_succ]
    rw [show (j + 1) * w = w + j * w by ring, pow_add, ← Nat.div_div_eq_div_mul,
      show (a + 2 ^ w * packW w l) / 2 ^ w = packW w l by
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add]]
    exact packW_get w l (fun b hb => h b (by simp [hb])) j

/-- Word `j` (index in `25`) of the packed basis in `20`, width `f` in `23`. -/
def getB : E := .md (.shr (.v 20) (.mul (.v 25) (.v 23))) (.shl (.k 1) (.v 23))

/-- `24 := sel B v` for the packed basis `B` in `20` of length `21`, `v` in `22`, width in `23` (loop variable `25`). -/
def selP : S :=
  .seq (.set 24 (.k 0)) (.loop 25 (.v 21) (.ite (.eq (.md (.shr (.v 22) (.v 25)) (.k 2)) (.k 1))
    (.set 24 (.fadd (.v 24) getB)) .skip))

theorem sel_take_succ {F : Type} [Field F] (B : List F) (v j : ℕ) (hj : j < B.length) :
    sel (B.take (j + 1)) v = sel (B.take j) v + (if v / 2 ^ j % 2 = 1 then B.getD j 0 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, sel_append, sel_cons, sel_nil, add_zero,
    List.length_take, min_eq_left hj.le, List.getD_eq_getElem _ _ hj]

/-- **Selection by bits**: the word of `Σ_j (bit j of v)·B_j`. -/
theorem selP_spec {F : Type} [Field F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (l : List ℕ)
    (hl : ∀ a ∈ l, a < 2 ^ s.fl) (h20 : s.env 20 = packW s.fl l) (h21 : s.env 21 = l.length)
    (h23 : s.env 23 = s.fl) (hok : fieldOk G s.fl s.fp = true) (hcap : l.length * s.fl ≤ G.cap)
    (hN : l.length ≤ G.N) :
    let t := evalS G selP s
    t.env 24 < 2 ^ s.fl ∧ φ (GF.rep s.fp (t.env 24)) = sel (l.map fun a => φ (GF.rep s.fp a)) (s.env 22) ∧
      Wr [24, 25] s t := by
  intro t
  have hp1 : 1 ≤ 2 ^ s.fl := Nat.one_le_two_pow
  have htf := tf_le hok
  have hmod := (fl_bounds hok).2.2.1
  have hc0 : min 0 G.cap = 0 := by omega
  have hc1 : min 1 G.cap = 1 := by omega
  have hc2 : min 2 G.cap = 2 := by omega
  have hct : min (min 1 G.cap * 2 ^ s.fl) G.cap = 2 ^ s.fl := by rw [hc1]; omega
  set B := l.map fun a => φ (GF.rep s.fp a)
  have hBl : B.length = l.length := by simp [B]
  set s1 := s.setv 24 (min 0 G.cap)
  have hmin : min (evalE G s1 (.v 21)) G.N = l.length := by
    simp (config := { decide := true }) only [s1, evalE, FS.setv_env, Function.update_apply, if_false, h21]; omega
  have hloop := loop_inv G (i := 25) (n := .v 21) (body := .ite (.eq (.md (.shr (.v 22) (.v 25)) (.k 2)) (.k 1))
      (.set 24 (.fadd (.v 24) getB)) .skip) (s := s1)
    (fun j w => w.env 24 < 2 ^ s.fl ∧ φ (GF.rep s.fp (w.env 24)) = sel (B.take j) (s.env 22) ∧ Wr [24, 25] s w)
    ⟨by simp [s1, hc0], by simp [s1, hc0], Wr.setv s (by decide) _⟩ (by
      rw [hmin]
      rintro j hj w ⟨w24, wsel, wW⟩
      have w20 : w.env 20 = packW s.fl l := (wW.env 20 (by decide)).trans h20
      have w22 : w.env 22 = s.env 22 := wW.env 22 (by decide)
      have w23 : w.env 23 = s.fl := (wW.env 23 (by decide)).trans h23
      have wfl : w.fl = s.fl := wW.fl
      have wfp : w.fp = s.fp := wW.fp
      have hjf : min (j * s.fl) G.cap = j * s.fl := by
        have : j * s.fl ≤ l.length * s.fl := Nat.mul_le_mul_right _ hj.le
        omega
      have hget : evalE G (w.setv 25 j) getB = l.getD j 0 := by
        simp (config := { decide := true }) only [getB, evalE, FS.setv_env, Function.update_apply, if_true, if_false,
          w20, w23, hjf, hct]
        exact packW_get s.fl l hl j
      have hlj : l.getD j 0 < 2 ^ s.fl := by
        rw [List.getD_eq_getElem _ _ hj]; exact hl _ (List.getElem_mem _)
      have hBj : B.getD j 0 = φ (GF.rep s.fp (l.getD j 0)) := by
        simp only [B, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
          Option.getD_some]
      have hbit : evalE G (w.setv 25 j) (.eq (.md (.shr (.v 22) (.v 25)) (.k 2)) (.k 1)) =
          if s.env 22 / 2 ^ j % 2 = 1 then 1 else 0 := by
        simp (config := { decide := true }) only [evalE, FS.setv_env, Function.update_apply, if_true, if_false, w22,
          hc2, hc1]
      rw [evalS_ite, hbit]
      by_cases hb : s.env 22 / 2 ^ j % 2 = 1
      · simp only [hb, if_true, one_ne_zero, if_false, evalS_set]
        have e24 : (w.setv 25 j).env 24 = w.env 24 := by simp
        refine ⟨?_, ?_, ?_⟩
        · simp only [FS.setv_env, Function.update_self, evalE, hget, e24, FS.setv_fl, wfl]
          exact Nat.mod_lt _ (by positivity)
        · simp only [FS.setv_env, Function.update_self, evalE, hget, e24, FS.setv_fl, FS.setv_fp, wfl, wfp]
          rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow w24 hlj), GF.rep_xor, map_add, wsel,
            sel_take_succ B _ j (by rw [hBl]; exact hj), if_pos hb, hBj]
        · exact (wW.trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
      · simp only [hb, if_false, if_true, evalS_skip]
        refine ⟨by simpa using w24, ?_, (wW.trans (Wr.setv _ (by decide) _))⟩
        simp only [FS.setv_env, Function.update_apply, show (24 : Var) ≠ 25 by decide, if_false, FS.setv_fp]
        rw [wsel, sel_take_succ B _ j (by rw [hBl]; exact hj), if_neg hb, add_zero])
  rw [hmin, show B.take l.length = B by rw [← hBl, List.take_length]] at hloop
  exact hloop

end NearCubicGates.Adapters.ShortPCP.Machines.FL
