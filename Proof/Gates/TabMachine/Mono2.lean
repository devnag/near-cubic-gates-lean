import Proof.Gates.TabMachine.Mono

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## Value level -/

theorem chunk_map (N : ℕ) (l : List (List ℤ)) (a : ℕ) (h : ∀ c ∈ l, c.length = N) (ha : a < l.length) :
    (((l.flatten.map encS).drop (a * N)).take (l[a].map encS).length) = l[a].map encS := by
  rw [List.length_map, h _ (List.getElem_mem ha), ← List.map_drop, ← List.map_take, chunk_drop_take N l a h ha]

theorem seg_get' {α : Type} (xs seg : List α) (p : ℕ) (h : (xs.drop p).take seg.length = seg) (i : ℕ)
    (hi : i < seg.length) : p + i < xs.length ∧ ∀ (h' : p + i < xs.length), xs[p + i] = seg[i] := by
  have hl : ((xs.drop p).take seg.length).length = seg.length := by rw [h]
  rw [List.length_take, List.length_drop] at hl
  refine ⟨by omega, fun h' => ?_⟩
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_take, if_pos hi, List.getElem?_drop, List.getElem?_eq_getElem h',
    List.getElem?_eq_getElem hi, Option.some.injEq] at this
  exact this

/-- The tuple stream read as the stacking machine reads it. -/
theorem tupleAt_fieldNums (m N : ℕ) (lss : List (List (List ℤ))) (hm : ∀ ls ∈ lss, ls.length = m)
    (hl : ∀ ls ∈ lss, ∀ l ∈ ls, l.length = N) :
    ∀ t (ht : t < lss.length), TupleAt (fieldNums (lss.map List.flatten)) (t * (m * N)) N lss[t] := by
  intro t ht c hc j hj
  have hflatlen : ∀ ls ∈ lss, ls.flatten.length = m * N := by
    intro ls hls
    have := flatten_take_length N ls ls.length (hl ls hls) le_rfl
    rw [List.take_of_length_le le_rfl] at this
    rw [this, hm ls hls]
  have hflat : ∀ u ∈ lss.map List.flatten, u.length = m * N := by
    intro u hu
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hu
    exact hflatlen ls hls
  have ht' : t < (lss.map List.flatten).length := by simpa using ht
  have e1 := chunk_drop_take (m * N) (lss.map List.flatten) t hflat ht'
  rw [List.getElem_map] at e1
  have e1' : ((lss.map List.flatten).flatten.drop (t * (m * N))).take lss[t].flatten.length = lss[t].flatten := by
    rw [hflatlen _ (List.getElem_mem ht)]; exact e1
  have hc' : c < lss[t].length := hc
  have hcl : lss[t][c].length = N := hl _ (List.getElem_mem ht) _ (List.getElem_mem hc')
  have e2 := chunk_drop_take N lss[t] c (hl _ (List.getElem_mem ht)) hc'
  have e2' : (lss[t].flatten.drop (c * N)).take lss[t][c].length = lss[t][c] := by rw [hcl]; exact e2
  have g2 := seg_get' _ _ (c * N) e2' j (by rw [hcl]; exact hj)
  have g1 := seg_get' _ _ (t * (m * N)) e1' (c * N + j) g2.1
  unfold fieldNums
  have hidx : t * (m * N) + c * N + j = t * (m * N) + (c * N + j) := Nat.add_assoc _ _ _
  refine ⟨by rw [List.length_map, hidx]; exact g1.1, fun h => ?_⟩
  simp only [List.getElem_map, hidx]
  rw [g1.2 g1.1, g2.2 g2.1, List.getD_eq_getElem _ _ hc', List.getD_eq_getElem _ _ (by rw [hcl]; exact hj)]

theorem tupF_fields (c W : ℕ) (os : List Occ) (hfit : ∀ o ∈ os, ∀ kid ∈ o.kids c, ∀ y ∈ kid, y.natAbs < 2 ^ W) :
    ∀ x ∈ fieldNums (tupF c os), x < 2 ^ (W + 1) := by
  intro x hx
  unfold fieldNums at hx
  rw [tupF_eq] at hx
  simp only [List.mem_map, List.mem_flatten] at hx
  obtain ⟨y, ⟨l, ⟨es, hes, rfl⟩, hyl⟩, rfl⟩ := hx
  rw [List.mem_flatten] at hyl
  obtain ⟨kid, hkid, hy⟩ := hyl
  obtain ⟨L, hL, hkL⟩ := mem_tuples_mem _ es hes kid hkid
  simp only [List.mem_map, List.mem_reverse] at hL
  obtain ⟨o, ho, rfl⟩ := hL
  exact SInt.encS_lt (hfit o ho kid hkL y hy)

/-! ## The state between monomials -/

section MonoRest
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

/-- The cut machine between two monomials at the inner point `c`: at rest, the occurrence stream `xs` on `Z 46`,
the point `c` on `Z 54`, the monomial's coefficient on `Z 43`, the cut stream open on `Z 34` with `g` cuts so far,
the read index `p`. -/
structure MonoRest (cap W s k : ℕ) (xs : List ℕ) (c : ℕ) (coef : ℤ) (out L0 : List Bool) (g p : ℕ)
    (σ : WState ns nr) : Prop where
  rest : GRest Z Y cap W s k σ
  r98 : σ.val (Y 98) = 0
  r99 : σ.val (Y 99) = 0
  r44 : σ.val (Y 44) = 0
  r47 : σ.val (Y 47) = 0
  pg : ∃ junk, σ.st (Z 46) = recStream (xs.map (binary (W + 1))) ++ junk
  pgh : σ.sh (Z 46) = 0
  cx : NumOn σ (Z 54) (W + 1) c
  coef : NumOn σ (Z 43) ((s + 1) * (W + 1)) (encS coef)
  cut : OutOn σ (Z 34) (Y 56) out L0
  gc : σ.val (Y 74) = g
  idx : σ.val (Y 77) = p

/-! ## Prologue: read `m`, start from one empty tuple -/

def monoPre : WMX ns nr :=
  .seq (getAt (Z 46) (Z 47) (Y 75) (Y 76) (Y 77) (Y 78))
  (.seq (toReg (Z 47) (Z 55) (Z 20) (Y 98) (Y 91) (Y 92) (Y 93))
  (.seq (WMX.inc (Y 77))
  (.seq (closeOutX (Z 31) (Y 95)) (WMX.inc (Y 47)))))

def monoPreCost (W p m : ℕ) : ℕ :=
  (p + 1) * (40 * (W + 1) + 40) + 10 * (p + 1) * (2 * (W + 1) + 1) + 10 + 1 +
  (m * (83 * (W + 1) + 30) + 41 * (W + 1) + 14 + 1 + (3 + 1 + (5 * 0 + 3 + 1 + 3)))

theorem monoPre_spec (cap W s k : ℕ) (xs : List ℕ) (c : ℕ) (coef : ℤ) (out L0 : List Bool) (g p : ℕ)
    (σ : WState ns nr) (h : MonoRest Z Y cap W s k xs c coef out L0 g p σ) (hp : p < xs.length)
    (hm : xs[p] < 2 ^ (W + 1)) (hcap : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * p + xs[p] + 2 ≤ cap) :
    Runs cap (monoPre Z Y) σ (monoPreCost W p xs[p]) (fun τ =>
      GRest Z Y cap W s k τ ∧ τ.val (Y 98) = xs[p] ∧ τ.val (Y 77) = p + 1 ∧ τ.val (Y 47) = 1 ∧
      (∃ junk, τ.st (Z 31) = recStream (([] : List ℕ).map (binary ((s + 1) * (W + 1)))) ++ junk) ∧
      SameExcept σ τ (([47, 31] : List (Fin 64)).map Z) (([98, 77, 47] : List (Fin 112)).map Y)) := by
  have hz := h.rest.zero
  obtain ⟨j, hpg⟩ := h.pg
  have hc1 : 2 * (W + 1) + 1 ≤ (xs.length + 1) * (2 * (W + 1) + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h1 := getAt_spec cap (A := Z 46) (Wk := Z 47) (CA := Y 75) (CW := Y 76) (N := Y 77) (K2 := Y 78)
    (Z.injective.ne (by decide)) (by simp [emb_eq_iff]) (W + 1) (by omega) xs p hp σ j hpg h.pgh
    (hz 75 (by decide)) (h.rest.work1 47 (by simp)).1 (h.rest.work1 47 (by simp)).2 (hz 76 (by decide)) h.idx
    (hz 78 (by decide)) (by omega)
  refine Runs.seqE h1 ?_
  set σ1 := σ.sets (Z 47) (frame (binary (W + 1) xs[p])) with hσ1
  have hX : NumOn σ1 (Z 47) (W + 1) xs[p] := ⟨by simp [hσ1], by simp [hσ1]; exact (h.rest.work1 47 (by simp)).1⟩
  have e47 : ∀ i : Fin 64, i ≠ 47 → σ1.st (Z i) = σ.st (Z i) ∧ σ1.sh (Z i) = σ.sh (Z i) := fun i hi => by
    simp [hσ1, Function.update_of_ne (Z.injective.ne hi)]
  have hONE : NumOn σ1 (Z 55) (W + 1) 1 :=
    ⟨by rw [(e47 55 (by decide)).1]; exact h.rest.c55.1, by rw [(e47 55 (by decide)).2]; exact h.rest.c55.2⟩
  have hZ : NumOn σ1 (Z 20) (W + 1) 0 :=
    ⟨by rw [(e47 20 (by decide)).1]; exact h.rest.c20.1, by rw [(e47 20 (by decide)).2]; exact h.rest.c20.2⟩
  have h2 := toReg_spec cap (W + 1) (X := Z 47) (ONE := Z 55) (Z := Z 20) (R := Y 98) (NZ := Y 91) (F := Y 92)
    (Rr := Y 93) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) σ1 xs[p] 0 0 hX hONE hZ
    (by simp [hσ1]; exact h.r98) (by simp [hσ1]; exact hz 91 (by decide)) (by simp [hσ1]; exact hz 92 (by decide))
    (by simp [hσ1]; exact hz 93 (by decide)) hm (by omega) (by omega)
  refine Runs.seqE h2 ?_
  set σ2 := (σ1.sets (Z 47) (frame (binary (W + 1) 0))).setv (Y 98) (0 + xs[p]) with hσ2
  have v2 : ∀ r : Fin 112, r ≠ 98 → σ2.val (Y r) = σ.val (Y r) := fun r hr => by
    simp [hσ2, hσ1, Function.update_of_ne (Y.injective.ne hr)]
  have h3 := WXExec.inc (cap := cap) (Y 77) σ2 (by rw [v2 77 (by decide), h.idx]; omega)
  rw [v2 77 (by decide), h.idx] at h3
  refine Runs.seqE h3 ?_
  set σ3 := σ2.setv (Y 77) (p + 1) with hσ3
  have hO : OutOn σ3 (Z 31) (Y 95) [] (σ3.st (Z 31)) := outOn_start σ3 _ _
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Z.injective.ne (show (31 : Fin 64) ≠ 47 by decide))]
        exact h.rest.closed 31 (by simp))
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Y.injective.ne (show (95 : Fin 112) ≠ 77 by decide)),
          Function.update_of_ne (Y.injective.ne (show (95 : Fin 112) ≠ 98 by decide))]
        exact hz 95 (by decide))
  have h4 := closeOut_runs cap σ3 [] _ hO (by simp)
  refine Runs.seq h4 fun σ4 h4' => ?_
  obtain ⟨⟨j4, b1⟩, b2, b3, b4⟩ := h4'
  have v4 : ∀ r : Fin 112, r ≠ 95 → σ4.val (Y r) = σ3.val (Y r) := fun r hr =>
    b4.val (by simp only [List.mem_singleton]; exact Y.injective.ne hr)
  have h47 : σ4.val (Y 47) = 0 := by
    rw [v4 47 (by decide)]; simp [hσ3, hσ2, hσ1, Function.update_of_ne (Y.injective.ne (show (47 : Fin 112) ≠ 77 by decide)),
      Function.update_of_ne (Y.injective.ne (show (47 : Fin 112) ≠ 98 by decide))]; exact h.r47
  have h5 := WXExec.inc (cap := cap) (Y 47) σ4 (by rw [h47]; omega)
  rw [h47] at h5
  refine Runs.of h5 ?_
  set σ5 := σ4.setv (Y 47) (0 + 1) with hσ5
  -- the frame
  have fr : SameExcept σ σ5 (([47, 31] : List (Fin 64)).map Z) (([98, 77, 47] : List (Fin 112)).map Y) := by
    have f1 : SameExcept σ σ3 (([47, 31] : List (Fin 64)).map Z) (([98, 77, 47] : List (Fin 112)).map Y) := by
      refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hσ3, hσ2, hσ1]⟩
      · have hx' : x ≠ Z 47 := fun e => hx (by simp [e])
        simp [hσ3, hσ2, hσ1, Function.update_of_ne hx']
      · have a : r ≠ Y 98 := fun e => hr (by simp [e])
        have b : r ≠ Y 77 := fun e => hr (by simp [e])
        simp [hσ3, hσ2, hσ1, Function.update_of_ne a, Function.update_of_ne b]
    have f2 : SameExcept σ3 σ4 (([47, 31] : List (Fin 64)).map Z) (([98, 77, 47] : List (Fin 112)).map Y) := by
      refine ⟨fun x hx => b4.1 x (fun hm => hx (by simp at hm ⊢; rw [hm]; simp)), fun r hr => ?_, b4.2.2⟩
      by_cases h95 : r = Y 95
      · subst h95; rw [b3]; simp [hσ3, hσ2, hσ1, Function.update_of_ne (Y.injective.ne (show (95 : Fin 112) ≠ 77 by decide)),
          Function.update_of_ne (Y.injective.ne (show (95 : Fin 112) ≠ 98 by decide))]; exact (hz 95 (by decide)).symm
      · exact b4.2.1 r (by simp [h95])
    exact (f1.trans f2).trans (sameExcept_setv σ4 (by simp) _)
  have st5 : ∀ i : Fin 64, i ∉ ([47, 31] : List (Fin 64)) → σ5.st (Z i) = σ.st (Z i) ∧ σ5.sh (Z i) = σ.sh (Z i) :=
    fun i hi => fr.1 _ (by rw [mem_map_emb]; exact hi)
  have hGR : GRest Z Y cap W s k σ5 := by
    refine grest_frame Z Y h.rest fr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi hm
      rw [mem_map_emb] at hm
      have : i = 47 := (by decide : ∀ i ∈ w1List, i ∈ ([47, 31] : List (Fin 64)) → i = 47) i hi hm
      subst this
      have e := b4.1 (Z 47) (by simp [emb_eq_iff])
      refine ⟨0, ?_, ?_⟩
      · simp only [hσ5, WState.setv_st]; rw [e.1]; simp [hσ3, hσ2]
      · simp only [hσ5, WState.setv_sh]; rw [e.2]; simp [hσ3, hσ2, hσ1]
        exact (h.rest.work1 47 (by simp)).1
    · intro i hi hm; rw [mem_map_emb] at hm
      exact absurd hm ((by decide : ∀ i ∈ wcList, i ∉ ([47, 31] : List (Fin 64))) i hi)
    · intro i hi hm; rw [mem_map_emb] at hm
      exact absurd hm ((by decide : ∀ i ∈ [(20 : Fin 64), 21, 53, 26, 44, 45, 55], i ∉ ([47, 31] : List (Fin 64))) i hi)
    · intro i hi hm
      rw [mem_map_emb] at hm
      have : i = 47 := (by decide : ∀ i ∈ [(3 : Fin 64), 47], i ∈ ([47, 31] : List (Fin 64)) → i = 47) i hi hm
      subst this
      have e := b4.1 (Z 47) (by simp [emb_eq_iff])
      simp only [hσ5, WState.setv_st, WState.setv_sh]
      rw [e.1, e.2]; simp [hσ3, hσ2, hσ1]
      exact (h.rest.work1 47 (by simp)).1
    · intro i hi hm; rw [mem_map_emb] at hm
      exact absurd hm ((by decide : ∀ i ∈ [(24 : Fin 64), 33], i ∉ ([47, 31] : List (Fin 64))) i hi)
    · intro i hi hm
      rw [mem_map_emb] at hm
      have : i = 31 := (by decide : ∀ i ∈ [(0 : Fin 64), 2, 30, 31, 32], i ∈ ([47, 31] : List (Fin 64)) → i = 31) i hi hm
      subst this
      simp only [hσ5, WState.setv_sh]; exact b2
    · intro r hr hm
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
      exact absurd hm ((by decide : ∀ r ∈ zList, ¬ (r = 98 ∨ r = 77 ∨ r = 47)) r hr)
    · intro r hr hm
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
      exact absurd hm ((by decide : ∀ r ∈ [(13 : Fin 112), 32, 41, 66, 84, 89], ¬ (r = 98 ∨ r = 77 ∨ r = 47)) r hr)
  refine ⟨hGR, ?_, ?_, ?_, ⟨j4, ?_⟩, fr⟩
  · simp only [hσ5, WState.setv_val, Function.update_of_ne (Y.injective.ne (show (98 : Fin 112) ≠ 47 by decide))]
    rw [v4 98 (by decide)]; simp [hσ3, hσ2, Function.update_of_ne (Y.injective.ne (show (98 : Fin 112) ≠ 77 by decide))]
  · simp only [hσ5, WState.setv_val, Function.update_of_ne (Y.injective.ne (show (77 : Fin 112) ≠ 47 by decide))]
    rw [v4 77 (by decide)]; simp [hσ3]
  · simp [hσ5]
  · simp only [hσ5, WState.setv_st]; rw [b1]; rfl

end MonoRest

end NearCubicGates.Close.TabMachine
