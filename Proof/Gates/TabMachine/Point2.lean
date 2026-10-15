import Proof.Gates.TabMachine.Point

/-! # All monomials at one inner point: **`pointBody_spec`**

A record loop over the coefficient stream `Z 56` (one record `binary Lc (encS a)` per monomial, the coefficient
lands on `Z 43`, where the stacking machine reads it) runs `monoStep` per monomial; then the read index is reset. -/

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

/-- The coefficient records. -/
def coefRecs (s W : ℕ) (ts : List (List Occ × ℤ)) : List (List Bool) :=
  ts.map fun t => binary ((s + 1) * (W + 1)) (encS t.2)

section PointBody
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

def pointBody : WMX ns nr := .seq (recLoop (Z 56) (Z 43) (Y 100) (Y 101) (monoStep Z Y)) (.wm (WM.clear (Y 77)))

/-- The monomial loop's invariant after `i` monomials. -/
def PInv (cap W s k Wd : ℕ) (σ0 : WState ns nr) (c : ℕ) (ts : List (List Occ × ℤ)) (out L0 : List Bool) (g i : ℕ)
    (τ : WState ns nr) : Prop :=
  CutRest Z Y cap W s k (codeRecs ts) (out ++ cutsOf Wd s c (ts.take i)) L0 (g + cutCount c (ts.take i))
      (termStart ts i) τ ∧ NumOn τ (Z 54) (W + 1) c ∧
    SameExcept σ0 τ ((monoIdx ++ [43, 56]).map Z) (([77, 74, 56, 100] : List (Fin 112)).map Y)

/-- The cost of the monomial loop with per-monomial bound `CM`. -/
def pointCost (W s : ℕ) (N X CM : ℕ) : ℕ :=
  N * (CM + (50 * ((s + 1) * (W + 1)) + 30)) + 3 + 1 + (3 * X + 1)

theorem pointBody_spec (cap W s k Wd CS B CM : ℕ) (hs1 : 1 ≤ s) (hWd : Wd + 1 = (s + 1) * (W + 1)) (hWd1 : 1 ≤ Wd)
    (ts : List (List Occ × ℤ)) (c : ℕ) (out L0 : List Bool) (g : ℕ) (σ : WState ns nr)
    (h : CutRest Z Y cap W s k (codeRecs ts) out L0 g 0 σ) (hcx : NumOn σ (Z 54) (W + 1) c)
    (hI : σ.st (Z 56) = recStream (coefRecs s W ts)) (hIh : σ.sh (Z 56) = 0)
    (h100 : σ.val (Y 100) = 0) (h101 : σ.val (Y 101) = 0)
    (hok : ∀ i (hi : i < ts.length), MonoOK cap W s k Wd CS B (codeRecs ts) (termStart ts i) c ts[i].1
      (out ++ cutsOf Wd s c (ts.take i)) (g + cutCount c (ts.take i)))
    (hcm : ∀ i (hi : i < ts.length), monoStepCost W s Wd CS B (termStart ts i) ts[i].1.length
      (fieldNums ((monoTuples c ts[i].1).map List.flatten)).length (monoTuples c ts[i].1).length ≤ CM)
    (hcap : ts.length * (2 * ((s + 1) * (W + 1)) + 1) + 2 * ((s + 1) * (W + 1)) + 2 ≤ cap)
    (hcapX : (codeRecs ts).length ≤ cap) :
    Runs cap (pointBody Z Y) σ (pointCost W s ts.length (codeRecs ts).length CM) (fun τ =>
      CutRest Z Y cap W s k (codeRecs ts) (out ++ cutsOf Wd s c ts) L0 (g + cutCount c ts) 0 τ ∧
      NumOn τ (Z 54) (W + 1) c ∧ τ.val (Y 100) = 0 ∧ τ.val (Y 101) = 0 ∧
      SameExcept σ τ ((monoIdx ++ [43]).map Z) (([74, 56] : List (Fin 112)).map Y)) := by
  set Lc := (s + 1) * (W + 1) with hLc
  have hLc1 : 1 ≤ Lc := by rw [hLc]; nlinarith
  have hw : ∀ w ∈ coefRecs s W ts, w.length = Lc := by
    intro w hw; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hw; simp [hLc]
  have hlen : (coefRecs s W ts).length = ts.length := by simp [coefRecs]
  have hb : BodySpec cap Lc (I := Z 56) (Wk := Z 43) (CI := Y 100) (CW := Y 101) (monoStep Z Y) (coefRecs s W ts)
      (PInv Z Y cap W s k Wd σ c ts out L0 g) (fun _ => CM) := by
    intro i hi ρ hinv hst hsh hci hcw hwh hwl
    rw [hlen] at hi
    obtain ⟨hr, hcxρ, fρ⟩ := hinv
    set ρ' := atRec (Z 56) (Z 43) (Y 100) ρ (coefRecs s W ts)[i] ((i + 1) * (2 * Lc + 1)) with hρ'
    have fa : SameExcept ρ ρ' (([43, 56] : List (Fin 64)).map Z) (([100] : List (Fin 112)).map Y) := by
      refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ', atRec]⟩
      · have a : x ≠ Z 43 := fun e => hx (by simp [e])
        have b : x ≠ Z 56 := fun e => hx (by simp [e])
        simp [hρ', atRec, Function.update_of_ne a, Function.update_of_ne b]
      · have a : r ≠ Y 100 := fun e => hr (by simp [e])
        simp [hρ', atRec, Function.update_of_ne a]
    have sa : ∀ i : Fin 64, i ∉ ([43, 56] : List (Fin 64)) → ρ'.st (Z i) = ρ.st (Z i) ∧ ρ'.sh (Z i) = ρ.sh (Z i) :=
      fun i hi => fr_st Z fa i hi
    have va : ∀ r : Fin 112, r ≠ 100 → ρ'.val (Y r) = ρ.val (Y r) := fun r hr => fr_val Y fa r (by simpa using hr)
    have hmr : MonoRest Z Y cap W s k (codeRecs ts) c ts[i].2 (out ++ cutsOf Wd s c (ts.take i)) L0
        (g + cutCount c (ts.take i)) (termStart ts i) ρ' := by
      obtain ⟨jx, hpg⟩ := hr.pg
      refine ⟨grest_out Z Y hr.rest [43, 56] [100] fa (by decide) (by decide), ?_, ?_, ?_, ?_, ⟨jx, ?_⟩, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · rw [va 98 (by decide)]; exact hr.r98
      · rw [va 99 (by decide)]; exact hr.r99
      · rw [va 44 (by decide)]; exact hr.r44
      · rw [va 47 (by decide)]; exact hr.r47
      · rw [(sa 46 (by decide)).1]; exact hpg
      · rw [(sa 46 (by decide)).2]; exact hr.pgh
      · exact ⟨by rw [(sa 54 (by decide)).1]; exact hcxρ.1, by rw [(sa 54 (by decide)).2]; exact hcxρ.2⟩
      · refine ⟨?_, ?_⟩
        · show ρ'.st (Z 43) = frame (binary Lc (encS ts[i].2))
          simp only [hρ', atRec, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, coefRecs,
            List.getElem_map, hLc]
        · simp only [hρ', atRec, WState.setv_sh, WState.seth_sh, WState.sets_sh]
          rw [Function.update_of_ne (Z.injective.ne (by decide))]; exact hwh
      · exact ⟨by rw [(sa 34 (by decide)).1]; exact hr.cut.1, by rw [(sa 34 (by decide)).2]; exact hr.cut.2.1,
          by rw [va 56 (by decide)]; exact hr.cut.2.2⟩
      · rw [va 74 (by decide)]; exact hr.gc
      · rw [va 77 (by decide)]; exact hr.idx
    have hstep := monoStep_spec Z Y cap W s k Wd CS B hs1 hWd hWd1 (codeRecs ts) c ts[i].2
      (out ++ cutsOf Wd s c (ts.take i)) L0 (g + cutCount c (ts.take i)) (termStart ts i) ts[i].1 ρ' hmr (hok i hi)
    obtain ⟨τ, e, hm, fm⟩ := hstep.cost (hcm i hi)
    have stm : ∀ j : Fin 64, j ∉ monoIdx → τ.st (Z j) = ρ'.st (Z j) ∧ τ.sh (Z j) = ρ'.sh (Z j) :=
      fun j hj => fm.1 _ (by rw [mem_map_emb]; exact hj)
    have vm : ∀ r : Fin 112, r ∉ ([77, 74, 56] : List (Fin 112)) → τ.val (Y r) = ρ'.val (Y r) :=
      fun r hr => fr_val Y (l := [77, 74, 56]) fm r hr
    refine ⟨τ, e, ⟨?_, hm.cx, ?_⟩, ?_, ?_, ?_, ?_, hm.coef.2, ?_⟩
    · have := cutRest_of_mono Z Y hm
      rwa [List.append_assoc, ← cutsOf_take_succ Wd s c ts i hi, Nat.add_assoc, ← cutCount_take_succ c ts i hi,
        posOf_end ts i hi] at this
    · refine ⟨fun x hx => ?_, fun r hr => ?_, by rw [fm.2.2, fa.2.2, fρ.2.2]⟩
      · have n1 : x ∉ monoIdx.map Z := fun hm' => hx (by
          rw [List.map_append]; exact List.mem_append_left _ hm')
        have n2 : x ∉ ([43, 56] : List (Fin 64)).map Z := fun hm' => hx (by
          rw [List.map_append]; exact List.mem_append_right _ hm')
        rw [(fm.1 x n1).1, (fm.1 x n1).2, (fa.1 x n2).1, (fa.1 x n2).2]; exact fρ.1 x hx
      · have n1 : r ∉ ([77, 74, 56] : List (Fin 112)).map Y := fun hm' => hr (by
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm' ⊢; tauto)
        have n2 : r ∉ ([100] : List (Fin 112)).map Y := fun hm' => hr (by
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm' ⊢; tauto)
        rw [fm.2.1 r n1, fa.2.1 r n2]; exact fρ.2.1 r hr
    · rw [(stm 56 (by decide)).1]
    · rw [(stm 56 (by decide)).2]
    · rw [vm 100 (by decide)]
    · rw [vm 101 (by decide)]
    · rw [hm.coef.1, frame_length, binary_length]
  have h0 : PInv Z Y cap W s k Wd σ c ts out L0 g 0 σ := by
    refine ⟨?_, hcx, SameExcept.refl _ _ _⟩
    simpa [cutsOf, cutCount, termStart] using h
  obtain ⟨τ, hτ, hτI, hτW, e⟩ := recLoop_spec (cap := cap) (L := Lc) (I := Z 56) (Wk := Z 43) (CI := Y 100)
    (CW := Y 101) (body := monoStep Z Y) (ws := coefRecs s W ts) (Inv := PInv Z Y cap W s k Wd σ c ts out L0 g)
    (c := fun _ => CM) (Z.injective.ne (by decide)) (Y.injective.ne (by decide)) hw hLc1 (by rw [hlen]; exact hcap)
    hb σ h0 hI hIh h100 h101 h.w43h h.w43l
  rw [hlen] at hτ
  obtain ⟨hr, hcxτ, fτ⟩ := hτ
  rw [List.take_of_length_le le_rfl, termStart_length] at hr
  set σ1 := (τ.setv (Y 100) 0).seth (Z 56) 0 with hσ1
  have e1 : σ1.val (Y 77) = (codeRecs ts).length := by
    simp only [hσ1, WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne (Y.injective.ne (by decide))]; exact hr.idx
  have hcl := wclear_spec (cap := cap) (Y 77) (codeRecs ts).length σ1 e1 (by rw [e1]; exact hcapX)
  have ecost : (∑ i ∈ Finset.range (coefRecs s W ts).length, ((fun _ => CM) i + (50 * Lc + 30))) + 3 =
      ts.length * (CM + (50 * Lc + 30)) + 3 := by
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hlen]
  rw [ecost] at e
  refine Runs.of (WXExec.seq e (WXExec.wm hcl)) ?_
  set σ2 := σ1.setv (Y 77) 0 with hσ2
  have f12 : SameExcept τ σ2 (([56] : List (Fin 64)).map Z) (([100, 77] : List (Fin 112)).map Y) := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hσ2, hσ1]⟩
    · have a : x ≠ Z 56 := fun e => hx (by simp [e])
      simp [hσ2, hσ1, Function.update_of_ne a]
    · have a : r ≠ Y 100 := fun e => hr (by simp [e])
      have b : r ≠ Y 77 := fun e => hr (by simp [e])
      simp [hσ2, hσ1, Function.update_of_ne a, Function.update_of_ne b]
  have s2 : ∀ i : Fin 64, i ≠ 56 → σ2.st (Z i) = τ.st (Z i) ∧ σ2.sh (Z i) = τ.sh (Z i) :=
    fun i hi => fr_st Z f12 i (by simpa using hi)
  have v2 : ∀ r : Fin 112, r ≠ 100 → r ≠ 77 → σ2.val (Y r) = τ.val (Y r) := fun r h1 h2 =>
    fr_val Y f12 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have h77 : σ2.val (Y 77) = 0 := by simp [hσ2]
  have h100' : σ2.val (Y 100) = 0 := by
    simp only [hσ2, hσ1, WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne (Y.injective.ne (by decide)), Function.update_self]
  obtain ⟨jx, hpg⟩ := hr.pg
  refine ⟨⟨grest_out Z Y hr.rest [56] [100, 77] f12 (by decide) (by decide), ?_, ?_, ?_, ?_, ⟨jx, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, h77⟩, ?_, h100', ?_, ?_⟩
  · rw [v2 98 (by decide) (by decide)]; exact hr.r98
  · rw [v2 99 (by decide) (by decide)]; exact hr.r99
  · rw [v2 44 (by decide) (by decide)]; exact hr.r44
  · rw [v2 47 (by decide) (by decide)]; exact hr.r47
  · rw [(s2 46 (by decide)).1]; exact hpg
  · rw [(s2 46 (by decide)).2]; exact hr.pgh
  · rw [(s2 43 (by decide)).2]; exact hr.w43h
  · rw [(s2 43 (by decide)).1]; exact hr.w43l
  · rw [(s2 54 (by decide)).2]; exact hr.w54h
  · rw [(s2 54 (by decide)).1]; exact hr.w54l
  · exact ⟨by rw [(s2 34 (by decide)).1]; exact hr.cut.1, by rw [(s2 34 (by decide)).2]; exact hr.cut.2.1,
      by rw [v2 56 (by decide) (by decide)]; exact hr.cut.2.2⟩
  · rw [v2 74 (by decide) (by decide)]; exact hr.gc
  · exact ⟨by rw [(s2 54 (by decide)).1]; exact hcxτ.1, by rw [(s2 54 (by decide)).2]; exact hcxτ.2⟩
  · rw [v2 101 (by decide) (by decide)]; exact hτW
  · refine ⟨fun x hx => ?_, fun r hr' => ?_, by rw [f12.2.2, fτ.2.2]⟩
    · by_cases e56 : x = Z 56
      · subst e56
        refine ⟨?_, ?_⟩
        · simp only [hσ2, hσ1, WState.setv_st, WState.seth_st]; rw [hτI, hI]
        · simp only [hσ2, hσ1, WState.setv_sh, WState.seth_sh, Function.update_self]; exact hIh.symm
      · have n2 : x ∉ ([56] : List (Fin 64)).map Z := by simpa using e56
        have n1 : x ∉ (monoIdx ++ [43, 56]).map Z := by
          intro hm'
          rw [List.map_append] at hm' hx
          rcases List.mem_append.mp hm' with h' | h'
          · exact hx (List.mem_append_left _ h')
          · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h'
            rcases h' with h' | h'
            · exact hx (List.mem_append_right _ (by simp [h']))
            · exact e56 h'
        rw [(f12.1 x n2).1, (f12.1 x n2).2]; exact fτ.1 x n1
    · by_cases e77 : r = Y 77
      · subst e77; rw [h77]; exact h.idx.symm
      · by_cases e100 : r = Y 100
        · subst e100; rw [h100']; exact h100.symm
        · have n2 : r ∉ ([100, 77] : List (Fin 112)).map Y := by simp [e77, e100]
          have n1 : r ∉ ([77, 74, 56, 100] : List (Fin 112)).map Y := by
            simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; tauto
          rw [f12.2.1 r n2]; exact fτ.2.1 r n1

end PointBody

end NearCubicGates.Close.TabMachine
