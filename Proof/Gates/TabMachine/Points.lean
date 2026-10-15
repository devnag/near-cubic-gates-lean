import Proof.Gates.TabMachine.Point2

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

/-- The cut records at all points `hs` (stacking width `Wd`). -/
def allCuts (Wd s : ℕ) (hs : List ℕ) (ts : List (List Occ × ℤ)) : List Bool := hs.flatMap fun c => cutsOf Wd s c ts

def allCount (hs : List ℕ) (ts : List (List Occ × ℤ)) : ℕ := (hs.map fun c => cutCount c ts).sum

/-- The points of `H` in increasing index order. -/
def hList (C : Code) : List ℕ := (List.range (2 ^ C.k)).filter fun c => C.hb.getD c false

theorem cutsOf_code (Wd : ℕ) (C : Code) (c : ℕ) :
    cutsOf Wd C.s c C.terms = (C.pointCutsL c).flatMap fun l => l.flatMap (fieldRec (Wd + 1)) := by
  unfold cutsOf Code.pointCutsL Code.termCutsL
  rw [List.flatMap_assoc]
  congr 1; funext t
  unfold monoTuples cutRecs
  rw [List.flatMap_map]

theorem filter_flatMap' {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    (l.filter p).flatMap f = l.flatMap fun a => if p a then f a else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem filter_map_sum {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem allCuts_code (Wd : ℕ) (C : Code) :
    allCuts Wd C.s (hList C) C.terms = C.cutsL.flatMap fun l => l.flatMap (fieldRec (Wd + 1)) := by
  unfold allCuts hList Code.cutsL
  rw [filter_flatMap', List.flatMap_assoc]
  congr 1; funext c
  by_cases h : C.hb.getD c false = true
  · rw [if_pos h, if_pos h, cutsOf_code]
  · rw [if_neg h, if_neg h]; rfl

theorem cutCount_code (C : Code) (c : ℕ) : cutCount c C.terms = (C.pointCutsL c).length := by
  unfold cutCount Code.pointCutsL Code.termCutsL
  rw [List.length_flatMap]
  congr 1; apply List.map_congr_left; intro t _; simp [monoTuples]

theorem allCount_code (C : Code) : allCount (hList C) C.terms = C.cutsL.length := by
  unfold allCount hList Code.cutsL
  rw [filter_map_sum, List.length_flatMap]
  congr 1; apply List.map_congr_left; intro c _
  by_cases h : C.hb.getD c false = true
  · rw [if_pos h, if_pos h, cutCount_code]
  · rw [if_neg h, if_neg h]; rfl

theorem allCuts_take_succ (Wd s : ℕ) (hs : List ℕ) (ts : List (List Occ × ℤ)) (j : ℕ) (hj : j < hs.length) :
    allCuts Wd s (hs.take (j + 1)) ts = allCuts Wd s (hs.take j) ts ++ cutsOf Wd s hs[j] ts := by
  unfold allCuts; rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem allCount_take_succ (hs : List ℕ) (ts : List (List Occ × ℤ)) (j : ℕ) (hj : j < hs.length) :
    allCount (hs.take (j + 1)) ts = allCount (hs.take j) ts + cutCount hs[j] ts := by
  unfold allCount; rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]

/-! ## The point loop -/

section Cuts
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

def cutsP : WMX ns nr := recLoop (Z 57) (Z 54) (Y 102) (Y 103) (pointBody Z Y)

/-- The point loop's invariant after `j` points. -/
def HInv (cap W s k Wd : ℕ) (σ0 : WState ns nr) (hs : List ℕ) (ts : List (List Occ × ℤ)) (out L0 : List Bool)
    (g j : ℕ) (τ : WState ns nr) : Prop :=
  CutRest Z Y cap W s k (codeRecs ts) (out ++ allCuts Wd s (hs.take j) ts) L0 (g + allCount (hs.take j) ts) 0 τ ∧
    τ.st (Z 56) = σ0.st (Z 56) ∧ τ.sh (Z 56) = 0 ∧ τ.val (Y 100) = 0 ∧ τ.val (Y 101) = 0 ∧
    SameExcept σ0 τ ((monoIdx ++ [43, 54, 57]).map Z) (([74, 56, 102] : List (Fin 112)).map Y)

/-- The side conditions at the point `hs[j]` (every monomial meets `MonoOK` within `CM`). -/
def PointOK (cap W s k Wd CS B CM : ℕ) (hs : List ℕ) (ts : List (List Occ × ℤ)) (out : List Bool) (g j : ℕ) :
    Prop :=
  ∀ (hj : j < hs.length), hs[j] < 2 ^ (W + 1) ∧
    (∀ i (hi : i < ts.length), MonoOK cap W s k Wd CS B (codeRecs ts) (termStart ts i) hs[j] ts[i].1
      (out ++ allCuts Wd s (hs.take j) ts ++ cutsOf Wd s hs[j] (ts.take i))
      (g + allCount (hs.take j) ts + cutCount hs[j] (ts.take i))) ∧
    ∀ i (hi : i < ts.length), monoStepCost W s Wd CS B (termStart ts i) ts[i].1.length
      (fieldNums ((monoTuples hs[j] ts[i].1).map List.flatten)).length (monoTuples hs[j] ts[i].1).length ≤ CM

theorem cutsP_spec (cap W s k Wd CS B CM : ℕ) (hs1 : 1 ≤ s) (hWd : Wd + 1 = (s + 1) * (W + 1)) (hWd1 : 1 ≤ Wd)
    (hs : List ℕ) (ts : List (List Occ × ℤ)) (out L0 : List Bool) (g : ℕ) (σ : WState ns nr)
    (h : CutRest Z Y cap W s k (codeRecs ts) out L0 g 0 σ)
    (hC : σ.st (Z 56) = recStream (coefRecs s W ts)) (hCh : σ.sh (Z 56) = 0)
    (hH : σ.st (Z 57) = recStream (hs.map (binary (W + 1)))) (hHh : σ.sh (Z 57) = 0)
    (h100 : σ.val (Y 100) = 0) (h101 : σ.val (Y 101) = 0) (h102 : σ.val (Y 102) = 0) (h103 : σ.val (Y 103) = 0)
    (hok : ∀ j, PointOK cap W s k Wd CS B CM hs ts out g j)
    (hcap : ts.length * (2 * ((s + 1) * (W + 1)) + 1) + 2 * ((s + 1) * (W + 1)) + 2 ≤ cap)
    (hcapX : (codeRecs ts).length ≤ cap)
    (hcapH : hs.length * (2 * (W + 1) + 1) + 2 * (W + 1) + 2 ≤ cap) :
    Runs cap (cutsP Z Y) σ (hs.length * (pointCost W s ts.length (codeRecs ts).length CM + (50 * (W + 1) + 30)) + 3)
      (fun τ => CutRest Z Y cap W s k (codeRecs ts) (out ++ allCuts Wd s hs ts) L0 (g + allCount hs ts) 0 τ ∧
        τ.st (Z 56) = σ.st (Z 56) ∧ τ.sh (Z 56) = 0 ∧ τ.st (Z 57) = σ.st (Z 57) ∧ τ.sh (Z 57) = 0 ∧
        τ.val (Y 100) = 0 ∧ τ.val (Y 101) = 0 ∧ τ.val (Y 102) = 0 ∧ τ.val (Y 103) = 0 ∧
        SameExcept σ τ ((monoIdx ++ [43, 54]).map Z) (([74, 56] : List (Fin 112)).map Y)) := by
  have hw : ∀ w ∈ hs.map (binary (W + 1)), w.length = W + 1 := by
    intro w hw; obtain ⟨c, _, rfl⟩ := List.mem_map.mp hw; simp
  have hlen : (hs.map (binary (W + 1))).length = hs.length := by simp
  have hb : BodySpec cap (W + 1) (I := Z 57) (Wk := Z 54) (CI := Y 102) (CW := Y 103) (pointBody Z Y)
      (hs.map (binary (W + 1))) (HInv Z Y cap W s k Wd σ hs ts out L0 g)
      (fun _ => pointCost W s ts.length (codeRecs ts).length CM) := by
    intro j hj ρ hinv hst hsh hci hcw hwh hwl
    rw [hlen] at hj
    obtain ⟨hr, h56, h56h, r100, r101, fρ⟩ := hinv
    obtain ⟨hcj, hokj, hcmj⟩ := hok j hj
    set ρ' := atRec (Z 57) (Z 54) (Y 102) ρ (hs.map (binary (W + 1)))[j] ((j + 1) * (2 * (W + 1) + 1)) with hρ'
    have fa : SameExcept ρ ρ' (([54, 57] : List (Fin 64)).map Z) (([102] : List (Fin 112)).map Y) := by
      refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ', atRec]⟩
      · have a : x ≠ Z 54 := fun e => hx (by simp [e])
        have b : x ≠ Z 57 := fun e => hx (by simp [e])
        simp [hρ', atRec, Function.update_of_ne a, Function.update_of_ne b]
      · have a : r ≠ Y 102 := fun e => hr (by simp [e])
        simp [hρ', atRec, Function.update_of_ne a]
    have sa : ∀ i : Fin 64, i ∉ ([54, 57] : List (Fin 64)) → ρ'.st (Z i) = ρ.st (Z i) ∧ ρ'.sh (Z i) = ρ.sh (Z i) :=
      fun i hi => fr_st Z fa i hi
    have va : ∀ r : Fin 112, r ≠ 102 → ρ'.val (Y r) = ρ.val (Y r) := fun r hr => fr_val Y fa r (by simpa using hr)
    have hcx : NumOn ρ' (Z 54) (W + 1) hs[j] := by
      refine ⟨?_, ?_⟩
      · simp only [hρ', atRec, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, List.getElem_map]
      · simp only [hρ', atRec, WState.setv_sh, WState.seth_sh, WState.sets_sh]
        rw [Function.update_of_ne (Z.injective.ne (by decide))]; exact hwh
    obtain ⟨jx, hpg⟩ := hr.pg
    have hcr : CutRest Z Y cap W s k (codeRecs ts) (out ++ allCuts Wd s (hs.take j) ts) L0
        (g + allCount (hs.take j) ts) 0 ρ' := by
      refine ⟨grest_out Z Y hr.rest [54, 57] [102] fa (by decide) (by decide), ?_, ?_, ?_, ?_, ⟨jx, ?_⟩, ?_, ?_, ?_,
        hcx.2, by rw [hcx.1, frame_length, binary_length], ?_, ?_, ?_⟩
      · rw [va 98 (by decide)]; exact hr.r98
      · rw [va 99 (by decide)]; exact hr.r99
      · rw [va 44 (by decide)]; exact hr.r44
      · rw [va 47 (by decide)]; exact hr.r47
      · rw [(sa 46 (by decide)).1]; exact hpg
      · rw [(sa 46 (by decide)).2]; exact hr.pgh
      · rw [(sa 43 (by decide)).2]; exact hr.w43h
      · rw [(sa 43 (by decide)).1]; exact hr.w43l
      · exact ⟨by rw [(sa 34 (by decide)).1]; exact hr.cut.1, by rw [(sa 34 (by decide)).2]; exact hr.cut.2.1,
          by rw [va 56 (by decide)]; exact hr.cut.2.2⟩
      · rw [va 74 (by decide)]; exact hr.gc
      · rw [va 77 (by decide)]; exact hr.idx
    have hpb := pointBody_spec Z Y cap W s k Wd CS B CM hs1 hWd hWd1 ts hs[j] (out ++ allCuts Wd s (hs.take j) ts) L0
      (g + allCount (hs.take j) ts) ρ' hcr hcx
      (by rw [(sa 56 (by decide)).1, h56]; exact hC) (by rw [(sa 56 (by decide)).2]; exact h56h)
      (by rw [va 100 (by decide)]; exact r100) (by rw [va 101 (by decide)]; exact r101) hokj hcmj hcap hcapX
    obtain ⟨τ, e, hq, hcxq, q100, q101, fq⟩ := hpb
    have stq : ∀ i : Fin 64, i ∉ monoIdx ++ [43] → τ.st (Z i) = ρ'.st (Z i) ∧ τ.sh (Z i) = ρ'.sh (Z i) :=
      fun i hi => fr_st Z fq i hi
    have vq : ∀ r : Fin 112, r ∉ ([74, 56] : List (Fin 112)) → τ.val (Y r) = ρ'.val (Y r) :=
      fun r hr => fr_val Y fq r hr
    refine ⟨τ, e, ⟨?_, ?_, ?_, q100, q101, ?_⟩, ?_, ?_, ?_, ?_, hcxq.2, ?_⟩
    · rwa [List.append_assoc, ← allCuts_take_succ Wd s hs ts j hj, Nat.add_assoc,
        ← allCount_take_succ hs ts j hj] at hq
    · rw [(stq 56 (by decide)).1, (sa 56 (by decide)).1, h56]
    · rw [(stq 56 (by decide)).2, (sa 56 (by decide)).2, h56h]
    · refine ⟨fun x hx => ?_, fun r hr => ?_, by rw [fq.2.2, fa.2.2, fρ.2.2]⟩
      · have n1 : x ∉ (monoIdx ++ [43]).map Z := by
          intro hm'; apply hx
          rw [List.map_append] at hm' ⊢
          rcases List.mem_append.mp hm' with h' | h'
          · exact List.mem_append_left _ h'
          · apply List.mem_append_right
            simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h' ⊢; tauto
        have n2 : x ∉ ([54, 57] : List (Fin 64)).map Z := by
          intro hm'; apply hx
          rw [List.map_append]
          apply List.mem_append_right
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm' ⊢; tauto
        rw [(fq.1 x n1).1, (fq.1 x n1).2, (fa.1 x n2).1, (fa.1 x n2).2]; exact fρ.1 x hx
      · have n1 : r ∉ ([74, 56] : List (Fin 112)).map Y := fun hm' => hr (by
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm' ⊢; tauto)
        have n2 : r ∉ ([102] : List (Fin 112)).map Y := fun hm' => hr (by
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm' ⊢; tauto)
        rw [fq.2.1 r n1, fa.2.1 r n2]; exact fρ.2.1 r hr
    · rw [(stq 57 (by decide)).1]
    · rw [(stq 57 (by decide)).2]
    · rw [vq 102 (by decide)]
    · rw [vq 103 (by decide)]
    · rw [hcxq.1, frame_length, binary_length]
  have h0 : HInv Z Y cap W s k Wd σ hs ts out L0 g 0 σ := by
    refine ⟨?_, rfl, hCh, h100, h101, SameExcept.refl _ _ _⟩
    simpa [allCuts, allCount] using h
  obtain ⟨τ, hτ, hτI, hτW, e⟩ := recLoop_spec (cap := cap) (L := W + 1) (I := Z 57) (Wk := Z 54) (CI := Y 102)
    (CW := Y 103) (body := pointBody Z Y) (ws := hs.map (binary (W + 1)))
    (Inv := HInv Z Y cap W s k Wd σ hs ts out L0 g) (c := fun _ => pointCost W s ts.length (codeRecs ts).length CM)
    (Z.injective.ne (by decide)) (Y.injective.ne (by decide)) hw (by omega) (by rw [hlen]; exact hcapH)
    hb σ h0 hH hHh h102 h103 h.w54h h.w54l
  rw [hlen] at hτ
  obtain ⟨hr, h56, h56h, r100, r101, fτ⟩ := hτ
  rw [List.take_of_length_le le_rfl] at hr
  have ecost : (∑ i ∈ Finset.range (hs.map (binary (W + 1))).length,
      ((fun _ => pointCost W s ts.length (codeRecs ts).length CM) i + (50 * (W + 1) + 30))) + 3 =
      hs.length * (pointCost W s ts.length (codeRecs ts).length CM + (50 * (W + 1) + 30)) + 3 := by
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hlen]
  rw [ecost] at e
  refine Runs.of e ?_
  set σ1 := (τ.setv (Y 102) 0).seth (Z 57) 0 with hσ1
  have f1 : SameExcept τ σ1 (([57] : List (Fin 64)).map Z) (([102] : List (Fin 112)).map Y) := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hσ1]⟩
    · have a : x ≠ Z 57 := fun e => hx (by simp [e])
      simp [hσ1, Function.update_of_ne a]
    · have a : r ≠ Y 102 := fun e => hr (by simp [e])
      simp [hσ1, Function.update_of_ne a]
  have s1 : ∀ i : Fin 64, i ≠ 57 → σ1.st (Z i) = τ.st (Z i) ∧ σ1.sh (Z i) = τ.sh (Z i) :=
    fun i hi => fr_st Z f1 i (by simpa using hi)
  have v1 : ∀ r : Fin 112, r ≠ 102 → σ1.val (Y r) = τ.val (Y r) := fun r hr => fr_val Y f1 r (by simpa using hr)
  obtain ⟨jx, hpg⟩ := hr.pg
  have h102' : σ1.val (Y 102) = 0 := by
    simp only [hσ1, WState.seth_val, WState.setv_val, Function.update_self]
  refine ⟨⟨grest_out Z Y hr.rest [57] [102] f1 (by decide) (by decide), ?_, ?_, ?_, ?_, ⟨jx, ?_⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, h102', ?_, ?_⟩
  · rw [v1 98 (by decide)]; exact hr.r98
  · rw [v1 99 (by decide)]; exact hr.r99
  · rw [v1 44 (by decide)]; exact hr.r44
  · rw [v1 47 (by decide)]; exact hr.r47
  · rw [(s1 46 (by decide)).1]; exact hpg
  · rw [(s1 46 (by decide)).2]; exact hr.pgh
  · rw [(s1 43 (by decide)).2]; exact hr.w43h
  · rw [(s1 43 (by decide)).1]; exact hr.w43l
  · rw [(s1 54 (by decide)).2]; exact hr.w54h
  · rw [(s1 54 (by decide)).1]; exact hr.w54l
  · exact ⟨by rw [(s1 34 (by decide)).1]; exact hr.cut.1, by rw [(s1 34 (by decide)).2]; exact hr.cut.2.1,
      by rw [v1 56 (by decide)]; exact hr.cut.2.2⟩
  · rw [v1 74 (by decide)]; exact hr.gc
  · rw [v1 77 (by decide)]; exact hr.idx
  · rw [(s1 56 (by decide)).1]; exact h56
  · rw [(s1 56 (by decide)).2]; exact h56h
  · simp only [hσ1, WState.seth_st, WState.setv_st]; rw [hτI, hH]
  · simp only [hσ1, WState.seth_sh, Function.update_self]
  · rw [v1 100 (by decide)]; exact r100
  · rw [v1 101 (by decide)]; exact r101
  · rw [v1 103 (by decide)]; exact hτW
  · refine ⟨fun x hx => ?_, fun r hr' => ?_, by rw [f1.2.2, fτ.2.2]⟩
    · by_cases e57 : x = Z 57
      · subst e57
        refine ⟨?_, ?_⟩
        · simp only [hσ1, WState.seth_st, WState.setv_st]; rw [hτI, hH]
        · simp only [hσ1, WState.seth_sh, Function.update_self]; exact hHh.symm
      · have n2 : x ∉ ([57] : List (Fin 64)).map Z := by simpa using e57
        have n1 : x ∉ (monoIdx ++ [43, 54, 57]).map Z := by
          intro hm'
          rw [List.map_append] at hm' hx
          rcases List.mem_append.mp hm' with h' | h'
          · exact hx (List.mem_append_left _ h')
          · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h'
            rcases h' with h' | h' | h'
            · exact hx (List.mem_append_right _ (by simp [h']))
            · exact hx (List.mem_append_right _ (by simp [h']))
            · exact e57 h'
        rw [(f1.1 x n2).1, (f1.1 x n2).2]; exact fτ.1 x n1
    · by_cases e102 : r = Y 102
      · subst e102; rw [h102']; exact h102.symm
      · have n2 : r ∉ ([102] : List (Fin 112)).map Y := by simp [e102]
        have n1 : r ∉ ([74, 56, 102] : List (Fin 112)).map Y := by
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢; tauto
        rw [f1.2.1 r n2]; exact fτ.2.1 r n1

end Cuts

end NearCubicGates.Close.TabMachine
