import SourceAdapters.ShortPCP.Machines.FLangSel
import SourceAdapters.ShortPCP.Machines.FLangComp

/-!
# Raw output of one packed coordinate row

The construction in `lem:generator`: field operations and their reduced
bit representations are charged by the ordinary field-word interpreter. This
fixed program emits the actual `fixedWidthNatBits` fields, with no output frame.
Parameters are in 20 (width), 22 (row length), 26 (packed row). Only 0,1,2
are scratch; the solver's state and all other variables are preserved.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicWires
open NearCubicGates.Adapters.ShortPCP.Machines.FL

/-- A raw output append and its complete preservation record. -/
structure Appends (W : List Var) (s t : FS) (word : List Bool) : Prop where
  env : ∀ j, j ∉ W → t.env j = s.env j
  out : t.out = s.out ++ word
  fl : t.fl = s.fl
  fp : t.fp = s.fp
  ip : t.ip = s.ip
  bad : t.bad = s.bad

theorem Appends.refl (W : List Var) (s : FS) : Appends W s s [] :=
  ⟨fun _ _ => rfl, by simp, rfl, rfl, rfl, rfl⟩

theorem Appends.trans {W : List Var} {s t u : FS} {a b : List Bool}
    (h : Appends W s t a) (h' : Appends W t u b) : Appends W s u (a ++ b) :=
  ⟨fun j hj => (h'.env j hj).trans (h.env j hj), by rw [h'.out, h.out, List.append_assoc],
    h'.fl.trans h.fl, h'.fp.trans h.fp, h'.ip.trans h.ip, h'.bad.trans h.bad⟩

theorem Appends.setv (W : List Var) (s : FS) (i : Var) (hi : i ∈ W) (v : ℕ) :
    Appends W s (s.setv i v) [] := by
  refine ⟨?_, by simp, rfl, rfl, rfl, rfl⟩
  intro j hj
  simp [Function.update_of_ne (show j ≠ i from fun h => hj (h ▸ hi))]

theorem Appends.mono {W W' : List Var} {s t : FS} {word : List Bool}
    (h : Appends W s t word) (hw : ∀ i ∈ W, i ∈ W') : Appends W' s t word :=
  ⟨fun j hj => h.env j (fun h' => hj (hw j h')), h.out, h.fl, h.fp, h.ip, h.bad⟩

theorem fixedWidth_eq_range (f n : ℕ) : WilliamsLoaderForms.fixedWidthNatBits f n =
    (List.range f).map n.testBit := by
  apply List.ext_getElem (by simp [WilliamsLoaderForms.fixedWidthNatBits])
  intro j hj hj'
  simp [WilliamsLoaderForms.fixedWidthNatBits]

theorem mod_two_ne_zero (n j : ℕ) : (n / 2 ^ j % 2 != 0) = n.testBit j := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> simp [h]

/-- Emit one raw width-20 word held in variable 2, using only loop variable 1. -/
def rawBits : S := .loop 1 (.v 20) (.emit (.md (.shr (.v 2) (.v 1)) (.k 2)))

theorem rawBits_spec (G : Glob) (s : FS) (f n : ℕ)
    (h20 : s.env 20 = f) (h2 : s.env 2 = n) (hN : f ≤ G.N) (hc : 2 ≤ G.cap) :
    Appends [1] s (evalS G rawBits s) (WilliamsLoaderForms.fixedWidthNatBits f n) := by
  have hm : min (evalE G s (.v 20)) G.N = f := by simp only [evalE, h20]; omega
  have h := loop_inv G (i := 1) (n := .v 20)
    (body := .emit (.md (.shr (.v 2) (.v 1)) (.k 2)))
    (fun j t => Appends [1] s t ((List.range j).map n.testBit))
    (by simpa using Appends.refl [1] s) (by
      intro j _ t ht
      have h2t : (t.setv 1 j).env 2 = n := by
        simp only [FS.setv_env, Function.update_of_ne (by decide : (2 : Var) ≠ 1)]
        exact (ht.env 2 (by decide)).trans h2
      have he : evalE G (t.setv 1 j) (.md (.shr (.v 2) (.v 1)) (.k 2)) = n / 2 ^ j % 2 := by
        simp only [evalE, h2t, FS.setv_env, Function.update_self, min_eq_left hc]
      have hs := Appends.setv [1] t 1 (by simp) j
      have ho : Appends [1] (t.setv 1 j)
          (evalS G (.emit (.md (.shr (.v 2) (.v 1)) (.k 2))) (t.setv 1 j)) [n.testBit j] := by
        refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl, rfl⟩
        simp only [evalS, he, mod_two_ne_zero]
      simpa only [List.range_succ, List.map_append, List.map_singleton, List.nil_append] using
        ht.trans (hs.trans ho))
  rw [hm, ← fixedWidth_eq_range] at h
  exact h

/-- Extract coefficient 0 of the current row (the coefficient index is variable 0). -/
def rowEntry : E :=
  .md (.shr (.v 26) (.mul (.v 0) (.v 20))) (.shl (.k 1) (.v 20))

/-- Print one row in coefficient order, then bit order. -/
def rowEmit : S := .loop 0 (.v 22) (.seq (.set 2 rowEntry) rawBits)

theorem rowEmit_spec (G : Glob) (s : FS) (f : ℕ) (row : List ℕ)
    (h20 : s.env 20 = f) (h22 : s.env 22 = row.length) (h26 : s.env 26 = packW f row)
    (hrow : ∀ x ∈ row, x < 2 ^ f) (hmN : row.length ≤ G.N) (hfN : f ≤ G.N)
    (hmf : row.length * f ≤ G.cap) (hf : 2 ^ f ≤ G.cap) (hc : 2 ≤ G.cap) :
    Appends [0, 1, 2] s (evalS G rowEmit s)
      (row.flatMap (WilliamsLoaderForms.fixedWidthNatBits f)) := by
  have hm : min (evalE G s (.v 22)) G.N = row.length := by simp only [evalE, h22]; omega
  have h := loop_inv G (i := 0) (n := .v 22) (body := .seq (.set 2 rowEntry) rawBits)
    (fun j t => Appends [0, 1, 2] s t ((row.take j).flatMap (WilliamsLoaderForms.fixedWidthNatBits f)))
    (by simpa using Appends.refl [0, 1, 2] s) (by
      intro j hj t ht
      have hjl : j < row.length := by rwa [hm] at hj
      have e20 : (t.setv 0 j).env 20 = f := by
        simp only [FS.setv_env, Function.update_of_ne (by decide : (20 : Var) ≠ 0)]
        exact (ht.env 20 (by decide)).trans h20
      have e26 : (t.setv 0 j).env 26 = packW f row := by
        simp only [FS.setv_env, Function.update_of_ne (by decide : (26 : Var) ≠ 0)]
        exact (ht.env 26 (by decide)).trans h26
      have hjf : j * f ≤ G.cap := le_trans (Nat.mul_le_mul_right f hjl.le) hmf
      have he : evalE G (t.setv 0 j) rowEntry = row.getD j 0 := by
        simp only [rowEntry, evalE, e20, e26, FS.setv_env, Function.update_self,
          min_eq_left hjf, min_eq_left (show 1 ≤ G.cap by omega), one_mul, min_eq_left hf]
        exact packW_get f row hrow j
      let u := (t.setv 0 j).setv 2 (row.getD j 0)
      have hu20 : u.env 20 = f := by
        simpa only [u, FS.setv_env,
          Function.update_of_ne (by decide : (20 : Var) ≠ 2)] using e20
      have hp := rawBits_spec G u f (row.getD j 0) hu20 (by simp [u]) hfN hc
      have h0 := Appends.setv [0, 1, 2] t 0 (by simp) j
      have h2' := Appends.setv [0, 1, 2] (t.setv 0 j) 2 (by simp) (row.getD j 0)
      have hall := ht.trans (h0.trans (h2'.trans (hp.mono (by simp))))
      have hw : (row.take (j + 1)).flatMap (WilliamsLoaderForms.fixedWidthNatBits f) =
          (row.take j).flatMap (WilliamsLoaderForms.fixedWidthNatBits f) ++
            WilliamsLoaderForms.fixedWidthNatBits f (row.getD j 0) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getD_eq_getElem _ _ hjl]
      simpa only [evalS_seq, evalS_set, he, hw, List.nil_append] using hall)
  rw [hm, List.take_length] at h
  exact h

theorem rowEmit_wf (d : ℕ) (hd : d ≤ 6) : wfS rowEmit d = true := by
  simp [rowEmit, rawBits, rowEntry, wfS, dE]
  omega

end NearCubicGates.Adapters.Routing.CoordinateMachine
