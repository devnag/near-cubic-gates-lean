import Proof.Gates.TabMachine.Mono2

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

/-! ## Clearing registers -/

/-- Clear every register of the list. -/
def clearAll : List (Fin nr) → WMX ns nr
  | [] => WMX.skip
  | r :: rs => .seq (.wm (WM.clear r)) (clearAll rs)

theorem clearAll_spec (cap B : ℕ) : ∀ (rs : List (Fin nr)) (σ : WState ns nr), (∀ r ∈ rs, σ.val r ≤ B) → B ≤ cap →
    Runs cap (clearAll rs) σ (rs.length * (3 * B + 2)) (fun τ =>
      (∀ r ∈ rs, τ.val r = 0) ∧ SameExcept σ τ [] rs)
  | [], σ, _, _ => by
    simp only [clearAll, List.length_nil, Nat.zero_mul]
    exact Runs.of (WXExec.skip cap σ) ⟨by simp, SameExcept.refl σ [] []⟩
  | r :: rs, σ, hB, hcap => by
    have h1 := wclear_spec (cap := cap) r (σ.val r) σ rfl ((hB r (by simp)).trans hcap)
    have hB' : ∀ q ∈ rs, (σ.setv r 0).val q ≤ B := by
      intro q hq
      by_cases e : q = r
      · subst e; simp
      · simp [Function.update_of_ne e]; exact hB q (by simp [hq])
    have h2 := clearAll_spec cap B rs (σ.setv r 0) hB' hcap
    have h3 : Runs cap (clearAll rs) (σ.setv r 0) (rs.length * (3 * B + 2)) (fun τ =>
        (∀ q ∈ r :: rs, τ.val q = 0) ∧ SameExcept σ τ [] (r :: rs)) := h2.post fun τ ⟨h0, hf⟩ => ⟨?_, ?_⟩
    · show Runs cap (.seq (.wm (WM.clear r)) (clearAll rs)) σ _ _
      refine (Runs.seqE (WXExec.wm h1) h3).cost ?_
      have := hB r (by simp)
      simp only [List.length_cons]; nlinarith
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · by_cases e : q ∈ rs
        · exact h0 q e
        · rw [hf.val e]; simp
      · exact h0 q hq
    · exact (sameExcept_setv σ (S := []) (Rg := r :: rs) (by simp) 0).trans
        (hf.weaken (fun x hx => hx) (fun q hq => by simp [hq]))

section MonoStack
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

def monoClear : List (Fin nr) := [Y 62, Y 73, Y 64, Y 67, Y 98, Y 44, Y 47]

def monoStack : WMX ns nr :=
  .seq (addR (Y 44) (Y 62) (Y 91))
  (.seq (addR (Y 44) (Y 73) (Y 91))
  (.seq (addR (Y 32) (Y 64) (Y 91))
  (.seq (addR (Y 98) (Y 67) (Y 91))
  (.seq (stackAll (zU Z) (yV Y)) (clearAll (monoClear Y))))))

def monoStackCost (Wd s m F T B : ℕ) : ℕ :=
  18 * (m * (s + 1)) + 3 + 1 + (18 * (m * (s + 1)) + 3 + 1 + (18 * (s + 1) + 3 + 1 + (18 * m + 3 + 1 +
    (stackAllCost Wd (m * (s + 1)) (s + 1) m F T + 1 + 7 * (3 * B + 2)))))

/-- The streams the stacking phase may change. -/
def stackIdx : List (Fin 64) := [33, 34, 35, 36, 37, 38, 39, 40, 41, 42]

theorem monoStack_spec (cap W s k Wd m : ℕ) (hWd : Wd + 1 = (s + 1) * (W + 1)) (hWd1 : 1 ≤ Wd)
    (σ : WState ns nr) (coef : ℤ) (out L0 : List Bool) (g : ℕ) (lss : List (List (List ℤ))) (junk : List Bool)
    (hrest : GRest Z Y cap W s k σ)
    (htp : σ.st (Z 31) = recStream ((fieldNums (lss.map List.flatten)).map (binary ((s + 1) * (W + 1)))) ++ junk)
    (hM : σ.val (Y 44) = m * (s + 1)) (hNT : σ.val (Y 47) = lss.length) (hm98 : σ.val (Y 98) = m)
    (hcoef : NumOn σ (Z 43) ((s + 1) * (W + 1)) (encS coef)) (hO : OutOn σ (Z 34) (Y 56) out L0)
    (hg : σ.val (Y 74) = g)
    (hm : ∀ ls ∈ lss, ls.length = m) (hl : ∀ ls ∈ lss, ∀ l ∈ ls, l.length = s + 1)
    (hfl : ∀ x ∈ fieldNums (lss.map List.flatten), x < 2 ^ (Wd + 1))
    (hbound : ∀ ls ∈ lss, (magL ls + 1) ^ (m + 1) < 2 ^ Wd)
    (B : ℕ) (hB : m * (s + 1) + lss.length + s + 1 + m ≤ B) (hBc : B ≤ cap)
    (hcap : ((fieldNums (lss.map List.flatten)).length + 1) * (2 * (Wd + 1) + 1) +
      2 * (fieldNums (lss.map List.flatten)).length + 2 * m + 2 * (m * (s + 1)) +
      lss.length * (m * (s + 1)) + 2 * (s + 1) + m * (s + 1) + g + lss.length + 1 + 2 * lss.length ≤ cap)
    (hcapO : out.length + lss.length * ((s + 2) * (2 * (Wd + 1) + 1)) + 1 ≤ cap) :
    Runs cap (monoStack Z Y) σ (monoStackCost Wd s m (fieldNums (lss.map List.flatten)).length lss.length B)
      (fun τ => GRest Z Y cap W s k τ ∧ τ.val (Y 44) = 0 ∧ τ.val (Y 47) = 0 ∧ τ.val (Y 98) = 0 ∧
        OutOn τ (Z 34) (Y 56) (out ++ lss.flatMap (cutRecs Wd s coef)) L0 ∧ τ.val (Y 74) = g + lss.length ∧
        SameExcept σ τ (stackIdx.map Z) [Y 56, Y 74, Y 44, Y 47, Y 98]) := by
  have hz := hrest.zero
  set fl := fieldNums (lss.map List.flatten) with hfl_def
  -- (1) the four loop constants
  have a1 := addR_spec cap (A := Y 44) (B := Y 62) (T := Y 91) (Y.injective.ne (by decide))
    (Y.injective.ne (by decide)) (Y.injective.ne (by decide)) σ (hz 91 (by decide))
    (by rw [hz 62 (by decide), hM]; omega)
  rw [hz 62 (by decide), hM, Nat.zero_add] at a1
  refine Runs.seqE a1 ?_
  set σ1 := σ.setv (Y 62) (m * (s + 1)) with hσ1
  have v1 : ∀ r : Fin 112, r ≠ 62 → σ1.val (Y r) = σ.val (Y r) := fun r hr => by
    simp [hσ1, Function.update_of_ne (Y.injective.ne hr)]
  have a2 := addR_spec cap (A := Y 44) (B := Y 73) (T := Y 91) (Y.injective.ne (by decide))
    (Y.injective.ne (by decide)) (Y.injective.ne (by decide)) σ1 (by rw [v1 91 (by decide)]; exact hz 91 (by decide))
    (by rw [v1 73 (by decide), v1 44 (by decide), hz 73 (by decide), hM]; omega)
  rw [v1 73 (by decide), v1 44 (by decide), hz 73 (by decide), hM, Nat.zero_add] at a2
  refine Runs.seqE a2 ?_
  set σ2 := σ1.setv (Y 73) (m * (s + 1)) with hσ2
  have v2 : ∀ r : Fin 112, r ≠ 62 → r ≠ 73 → σ2.val (Y r) = σ.val (Y r) := fun r h1 h2 => by
    rw [hσ2, WState.setv_val, Function.update_of_ne (Y.injective.ne h2)]; exact v1 r h1
  have a3 := addR_spec cap (A := Y 32) (B := Y 64) (T := Y 91) (Y.injective.ne (by decide))
    (Y.injective.ne (by decide)) (Y.injective.ne (by decide)) σ2
    (by rw [v2 91 (by decide) (by decide)]; exact hz 91 (by decide))
    (by rw [v2 64 (by decide) (by decide), v2 32 (by decide) (by decide), hz 64 (by decide), hrest.r32]; omega)
  rw [v2 64 (by decide) (by decide), v2 32 (by decide) (by decide), hz 64 (by decide), hrest.r32, Nat.zero_add] at a3
  refine Runs.seqE a3 ?_
  set σ3 := σ2.setv (Y 64) (s + 1) with hσ3
  have v3 : ∀ r : Fin 112, r ≠ 62 → r ≠ 73 → r ≠ 64 → σ3.val (Y r) = σ.val (Y r) := fun r h1 h2 h3 => by
    rw [hσ3, WState.setv_val, Function.update_of_ne (Y.injective.ne h3)]; exact v2 r h1 h2
  have a4 := addR_spec cap (A := Y 98) (B := Y 67) (T := Y 91) (Y.injective.ne (by decide))
    (Y.injective.ne (by decide)) (Y.injective.ne (by decide)) σ3
    (by rw [v3 91 (by decide) (by decide) (by decide)]; exact hz 91 (by decide))
    (by rw [v3 67 (by decide) (by decide) (by decide), v3 98 (by decide) (by decide) (by decide), hz 67 (by decide),
      hm98]; omega)
  rw [v3 67 (by decide) (by decide) (by decide), v3 98 (by decide) (by decide) (by decide), hz 67 (by decide), hm98,
    Nat.zero_add] at a4
  refine Runs.seqE a4 ?_
  set σ4 := σ3.setv (Y 67) m with hσ4
  have v4 : ∀ r : Fin 112, r ≠ 62 → r ≠ 73 → r ≠ 64 → r ≠ 67 → σ4.val (Y r) = σ.val (Y r) :=
    fun r h1 h2 h3 h4 => by rw [hσ4, WState.setv_val, Function.update_of_ne (Y.injective.ne h4)]; exact v3 r h1 h2 h3
  have s62 : σ4.val (Y 62) = m * (s + 1) := by
    simp only [hσ4, hσ3, hσ2, hσ1, WState.setv_val]
    rw [Function.update_of_ne (Y.injective.ne (show (62 : Fin 112) ≠ 67 by decide)),
      Function.update_of_ne (Y.injective.ne (show (62 : Fin 112) ≠ 64 by decide)),
      Function.update_of_ne (Y.injective.ne (show (62 : Fin 112) ≠ 73 by decide)), Function.update_self]
  have s73 : σ4.val (Y 73) = m * (s + 1) := by
    simp only [hσ4, hσ3, hσ2, WState.setv_val]
    rw [Function.update_of_ne (Y.injective.ne (show (73 : Fin 112) ≠ 67 by decide)),
      Function.update_of_ne (Y.injective.ne (show (73 : Fin 112) ≠ 64 by decide)), Function.update_self]
  have s64 : σ4.val (Y 64) = s + 1 := by
    simp only [hσ4, hσ3, WState.setv_val]
    rw [Function.update_of_ne (Y.injective.ne (show (64 : Fin 112) ≠ 67 by decide)), Function.update_self]
  have s67 : σ4.val (Y 67) = m := by simp only [hσ4, WState.setv_val, Function.update_self]
  have st4 : ∀ i : Fin 64, σ4.st (Z i) = σ.st (Z i) ∧ σ4.sh (Z i) = σ.sh (Z i) := fun i => by
    simp [hσ4, hσ3, hσ2, hσ1]
  have z4 : ∀ r : Fin 112, r ∈ zList → r ∉ [(62 : Fin 112), 73, 64, 67] → σ4.val (Y r) = 0 := by
    intro r hr hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [v4 r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]; exact hz r hr
  -- (2) stack
  have hpre : SPre (zU Z) (yV Y) Wd (m * (s + 1)) (s + 1) m fl coef σ4 := by
    refine ⟨⟨junk, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ4.st (Z 31) = _; rw [(st4 31).1, htp, hWd]
    · show σ4.sh (Z 31) = 0; rw [(st4 31).2]; exact hrest.closed 31 (by simp)
    · show σ4.sh (Z 33) = 0; rw [(st4 33).2]; exact (hrest.workc 33 (by simp)).1
    · show (σ4.st (Z 33)).length ≤ _; rw [(st4 33).1, hWd]; exact (hrest.workc 33 (by simp)).2
    · intro j hj
      have hw : ixU j ∈ wcList := by revert j; decide
      obtain ⟨v, hv⟩ := hrest.wc _ hw
      exact ⟨v, by show σ4.st (Z (ixU j)) = _; rw [(st4 _).1, hWd]; exact hv.1,
        by show σ4.sh (Z (ixU j)) = 0; rw [(st4 _).2]; exact hv.2⟩
    · show NumOn σ4 (Z 43) (Wd + 1) (encS coef)
      rw [hWd]; exact ⟨by rw [(st4 43).1]; exact hcoef.1, by rw [(st4 43).2]; exact hcoef.2⟩
    · show NumOn σ4 (Z 44) (Wd + 1) 0
      rw [hWd]; exact ⟨by rw [(st4 44).1]; exact hrest.c44.1, by rw [(st4 44).2]; exact hrest.c44.2⟩
    · show NumOn σ4 (Z 45) (Wd + 1) 2
      rw [hWd]; exact ⟨by rw [(st4 45).1]; exact hrest.c45.1, by rw [(st4 45).2]; exact hrest.c45.2⟩
    · intro j hj
      show σ4.val (Y (ixV j)) = 0
      exact z4 _ (by revert j; decide) (by revert j; decide)
    · show σ4.val (Y 66) = s + 1
      rw [v4 66 (by decide) (by decide) (by decide) (by decide)]; exact hrest.r66
    · exact s73
  have hflen : fl.length = lss.length * (m * (s + 1)) := by
    rw [hfl_def, fieldNums_length (m * (s + 1)), List.length_map]
    intro u hu
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hu
    have := flatten_take_length (s + 1) ls ls.length (hl ls hls) le_rfl
    rw [List.take_of_length_le le_rfl] at this
    rw [this, hm ls hls]
  have h5 := stackAll_spec (zU Z) (yV Y) cap Wd s m fl coef σ4 g lss out L0 hm hl
    (tupleAt_fieldNums m (s + 1) lss hm hl) (by rw [hflen]) hfl hbound hWd1 hpre
    (z4 53 (by decide) (by decide)) (z4 70 (by decide) (by decide)) (z4 69 (by decide) (by decide))
    s62 (z4 63 (by decide) (by decide)) s64 (z4 65 (by decide) (by decide)) s67
    (z4 68 (by decide) (by decide))
    (by show σ4.val (Y 47) = _; rw [v4 47 (by decide) (by decide) (by decide) (by decide)]; exact hNT)
    (z4 72 (by decide) (by decide))
    (by show σ4.val (Y 74) = _; rw [v4 74 (by decide) (by decide) (by decide) (by decide)]; exact hg)
    (by show OutOn σ4 (Z 34) (Y 56) out L0
        exact ⟨by rw [(st4 34).1]; exact hO.1, by rw [(st4 34).2]; exact hO.2.1,
          by rw [v4 56 (by decide) (by decide) (by decide) (by decide)]; exact hO.2.2⟩)
    hcap hcapO
  refine Runs.seq h5 fun τ5 h5' => ?_
  obtain ⟨b1, b2, b3, b4⟩ := h5'
  have f5 : SameExcept σ4 τ5 (stackIdx.map Z) (([56, 74] : List (Fin 112)).map Y) := b4
  have v5 : ∀ r : Fin 112, r ≠ 56 → r ≠ 74 → τ5.val (Y r) = σ4.val (Y r) := fun r h1 h2 =>
    fr_val Y f5 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  -- (3) clear
  have hc := clearAll_spec (ns := ns) cap B (monoClear Y) τ5 (by
      intro r hr
      simp only [monoClear, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [v5 62 (by decide) (by decide), s62]; omega
      · rw [v5 73 (by decide) (by decide), s73]; omega
      · rw [v5 64 (by decide) (by decide), s64]; omega
      · rw [v5 67 (by decide) (by decide), s67]; omega
      · rw [v5 98 (by decide) (by decide), v4 98 (by decide) (by decide) (by decide) (by decide), hm98]; omega
      · rw [v5 44 (by decide) (by decide), v4 44 (by decide) (by decide) (by decide) (by decide), hM]; omega
      · rw [v5 47 (by decide) (by decide), v4 47 (by decide) (by decide) (by decide) (by decide), hNT]; omega) hBc
  refine hc.post fun τ ⟨h0, f6⟩ => ?_
  have v6 : ∀ r : Fin 112, r ∉ ([62, 73, 64, 67, 98, 44, 47] : List (Fin 112)) → τ.val (Y r) = τ5.val (Y r) :=
    fun r hr => fr_val Y (by exact f6) r hr
  have st6 : ∀ i : Fin 64, τ.st (Z i) = τ5.st (Z i) ∧ τ.sh (Z i) = τ5.sh (Z i) := fun i => f6.1 _ (by simp)
  have hfr : SameExcept σ τ (stackIdx.map Z) [Y 56, Y 74, Y 44, Y 47, Y 98] := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by rw [f6.2.2, b4.2.2]; simp [hσ4, hσ3, hσ2, hσ1]⟩
    · rw [(f6.1 x (by simp)).1, (f6.1 x (by simp)).2, (b4.1 x hx).1, (b4.1 x hx).2]
      simp [hσ4, hσ3, hσ2, hσ1]
    · by_cases hc : r ∈ monoClear Y
      · rw [h0 r hc]
        simp only [monoClear, List.mem_cons, List.not_mem_nil, or_false] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact (hz 62 (by decide)).symm
        · exact (hz 73 (by decide)).symm
        · exact (hz 64 (by decide)).symm
        · exact (hz 67 (by decide)).symm
        · exact absurd rfl hr.2.2.2.2
        · exact absurd rfl hr.2.2.1
        · exact absurd rfl hr.2.2.2.1
      · rw [f6.2.1 r hc]
        simp only [monoClear, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [b4.2.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1⟩)]
        simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hc.1, Function.update_of_ne hc.2.1,
          Function.update_of_ne hc.2.2.1, Function.update_of_ne hc.2.2.2.1]
  have hGR : GRest Z Y cap W s k τ := by
    refine grest_frame Z Y hrest hfr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi hm; rw [mem_map_emb] at hm
      exact absurd hm ((by decide : ∀ i ∈ w1List, i ∉ stackIdx) i hi)
    · intro i hi hm
      rw [mem_map_emb] at hm
      have hj : ∃ j : Fin 14, j ∈ [(3 : Fin 14), 4, 5, 6, 7, 8, 9, 10] ∧ ixU j = i :=
        (by decide : ∀ i ∈ wcList, i ∈ stackIdx → ∃ j : Fin 14, j ∈ [(3 : Fin 14), 4, 5, 6, 7, 8, 9, 10] ∧ ixU j = i)
          i hi hm
      obtain ⟨j, hj, rfl⟩ := hj
      obtain ⟨v, hv⟩ := b1.words j hj
      refine ⟨v, ?_, ?_⟩
      · rw [(st6 _).1, ← hWd]; exact hv.1
      · rw [(st6 _).2]; exact hv.2
    · intro i hi hm; rw [mem_map_emb] at hm
      exact absurd hm ((by decide : ∀ i ∈ [(20 : Fin 64), 21, 53, 26, 44, 45, 55], i ∉ stackIdx) i hi)
    · intro i hi hm; rw [mem_map_emb] at hm
      exact absurd hm ((by decide : ∀ i ∈ [(3 : Fin 64), 47], i ∉ stackIdx) i hi)
    · intro i hi hm
      rw [mem_map_emb] at hm
      have : i = 33 := (by decide : ∀ i ∈ [(24 : Fin 64), 33], i ∈ stackIdx → i = 33) i hi hm
      subst this
      rw [(st6 33).1, (st6 33).2, ← hWd]; exact ⟨b1.wh, b1.wl⟩
    · intro i hi hm; rw [mem_map_emb] at hm
      exact absurd hm ((by decide : ∀ i ∈ [(0 : Fin 64), 2, 30, 31, 32], i ∉ stackIdx) i hi)
    · intro r hr hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl
      · exact absurd hr (by decide)
      · exact absurd hr (by decide)
      · exact absurd hr (by decide)
      · exact absurd hr (by decide)
      · exact absurd hr (by decide)
    · intro r hr hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
      exact absurd hm ((by decide : ∀ r ∈ [(13 : Fin 112), 32, 41, 66, 84, 89],
        ¬ (r = 56 ∨ r = 74 ∨ r = 44 ∨ r = 47 ∨ r = 98)) r hr)
  refine ⟨hGR, h0 _ (by simp [monoClear]), h0 _ (by simp [monoClear]), h0 _ (by simp [monoClear]), ?_, ?_, hfr⟩
  · exact ⟨by rw [(st6 34).1]; exact b2.1, by rw [(st6 34).2]; exact b2.2.1,
      by rw [v6 56 (by decide)]; exact b2.2.2⟩
  · rw [v6 74 (by decide)]; exact b3

end MonoStack

end NearCubicGates.Close.TabMachine
