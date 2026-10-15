import Proof.Gates.TabMachine.Restrict

/-! # Restriction to the inner point, part 2: **`restrictP_spec`** -/

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

section Restrict2
variable (A : Fin 10 ↪ Fin (ns + 1)) (B : Fin 12 ↪ Fin nr)

/-- The restricted target of an occurrence at the inner index `c` (lem:exact's strict target). -/
def rTarget (o : Occ) (c : ℕ) : ℤ := o.thr - (if o.ref then 0 else innerDot o.inW c) - 1

theorem restrictP_spec (cap W : ℕ) (xs : List ℕ) (σ : WState ns nr) (p c : ℕ) (o : Occ)
    (hseg : (xs.drop p).take (2 + o.inW.length) = [o.ref.toNat, encS o.thr] ++ o.inW.map encS)
    (hbound : (o.inW.map Int.natAbs).sum + o.thr.natAbs + 1 < 2 ^ W) (hc : c < 2 ^ (W + 1))
    (hpre : RPre A B W xs σ) (hIDX : σ.val (B 2) = p) (hCX : NumOn σ (A 9) (W + 1) c)
    (hK : σ.val (B 9) = o.inW.length) (hK2 : σ.val (B 10) = 0) (hREF : σ.val (B 11) = 0)
    (hcap : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * xs.length + 2 * o.inW.length ≤ cap) :
    Runs cap (restrictP A B) σ (restrictCost W xs.length o.inW.length p) (fun τ =>
      RPre A B W xs τ ∧ SNumOn τ (A 7) W (rTarget o c) ∧ τ.val (B 2) = p + 2 + o.inW.length ∧
        τ.val (B 9) = o.inW.length ∧ τ.val (B 10) = 0 ∧ τ.val (B 11) = 0 ∧
        SameExcept σ τ [A 1, A 2, A 3, A 4, A 5, A 6, A 7] [B 2]) := by
  have hne : ∀ {a b : Fin 10}, a ≠ b → A a ≠ A b := fun h => emb_ne A h
  have hner : ∀ {a b : Fin 12}, a ≠ b → B a ≠ B b := fun h => emb_ne B h
  have hz := hpre.zero
  set k := o.inW.length with hkdef
  have hcX : 2 * (W + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < xs.length + 1 by omega); omega
  have hsl : ([o.ref.toNat, encS o.thr] ++ o.inW.map encS).length = 2 + k := by simp [hkdef]; omega
  have hseg' : (xs.drop p).take ([o.ref.toNat, encS o.thr] ++ o.inW.map encS).length =
      [o.ref.toNat, encS o.thr] ++ o.inW.map encS := by rw [hsl]; exact hseg
  have hg := seg_get xs p _ hseg'
  obtain ⟨hp0, hx0⟩ := hg 0 (by rw [hsl]; omega)
  obtain ⟨hp1, hx1⟩ := hg 1 (by rw [hsl]; omega)
  have hx0' : xs[p] = o.ref.toNat := by simpa using hx0 hp0
  have hx1' : xs[p + 1] = encS o.thr := by simpa using hx1 hp1
  have hwmem : ∀ j < k, p + 2 + j < xs.length ∧ xs.getD (p + 2 + j) 0 = encS (o.inW.getD j 0) := by
    intro j hj
    obtain ⟨a1, a2⟩ := hg (2 + j) (by rw [hsl]; omega)
    refine ⟨by omega, ?_⟩
    rw [Nat.add_assoc, List.getD_eq_getElem _ _ a1, a2 a1, List.getD_eq_getElem _ _ (by omega)]
    simp [Nat.add_comm 2 j]
  have hbw : ∀ j < k, (o.inW.getD j 0).natAbs ≤ (o.inW.map Int.natAbs).sum := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.le_sum_of_mem (List.mem_map.2 ⟨_, List.getElem_mem (by omega), rfl⟩)
  obtain ⟨junk, hj⟩ := hpre.pg
  have g1 := getAt_spec cap (A := A 0) (Wk := A 1) (CA := B 0) (CW := B 1) (N := B 2) (K2 := B 3) (hne (by decide))
    (by simp [emb_eq_iff]) (W + 1) (by omega) xs p hp0 σ junk hj hpre.pgh (hz 0 (by simp)) hpre.wh hpre.wl
    (hz 1 (by simp)) hIDX (hz 3 (by simp)) (by omega)
  rw [hx0'] at g1
  set σ1 := σ.sets (A 1) (frame (binary (W + 1) o.ref.toNat)) with hσ1
  have g2 := SInt.sgnBitW_spec cap (X := A 1) (S := B 11) σ1 W o.ref.toNat (BinW.numOn_sets_self _ _ _ _ hpre.wh)
    (by simp [hσ1, hREF]) (by omega)
  have hr2 : o.ref.toNat % 2 = o.ref.toNat := by cases o.ref <;> rfl
  rw [hr2] at g2
  set σ2 := σ1.setv (B 11) o.ref.toNat with hσ2
  have h211 : B 2 ≠ B 11 := hner (by decide)
  have e2 : σ2.val (B 2) = p := by simp [hσ2, hσ1, Function.update_of_ne h211, hIDX]
  have g3 := WXExec.inc cap (B 2) σ2 (by rw [e2]; omega)
  set σ3 := σ2.setv (B 2) (σ2.val (B 2) + 1) with hσ3
  have e3 : σ3.val (B 2) = p + 1 := by simp [hσ3, e2]
  have g4 := getAt_spec cap (A := A 0) (Wk := A 1) (CA := B 0) (CW := B 1) (N := B 2) (K2 := B 3) (hne (by decide))
    (by simp [emb_eq_iff]) (W + 1) (by omega) xs (p + 1) hp1 σ3 junk (by simp [hσ3, hσ2, hσ1, emb_eq_iff, hj])
    (by simp [hσ3, hσ2, hσ1, emb_eq_iff, hpre.pgh]) (by simp [hσ3, hσ2, hσ1, hz 0 (by simp)])
    (by simp [hσ3, hσ2, hσ1, hpre.wh]) (by simp [hσ3, hσ2, hσ1, frame_length]) (by simp [hσ3, hσ2, hσ1, hz 1 (by simp)])
    e3 (by simp [hσ3, hσ2, hσ1, hz 3 (by simp)]) (by omega)
  rw [hx1'] at g4
  set σ4 := σ3.sets (A 1) (frame (binary (W + 1) (encS o.thr))) with hσ4
  obtain ⟨t0, ht0⟩ := hpre.words 7 (by simp)
  have g5 := BinW.copy_spec (A := A 7) (B := A 1) (F := B 6) (R := B 7) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ4 t0 (encS o.thr) ⟨by simp [hσ4, hσ3, hσ2, hσ1, emb_eq_iff, ht0.1], by
      simp [hσ4, hσ3, hσ2, hσ1, emb_eq_iff, ht0.2]⟩ (BinW.numOn_sets_self _ _ _ _ (by simp [hσ3, hσ2, hσ1, hpre.wh]))
    (by simp [hσ4, hσ3, hσ2, hσ1, hz 6 (by simp)]) (by simp [hσ4, hσ3, hσ2, hσ1, hz 7 (by simp)]) hcX
  set σ5 := σ4.sets (A 7) (frame (binary (W + 1) (encS o.thr))) with hσ5
  have g6 := WXExec.inc cap (B 2) σ5 (by simp only [hσ5, WState.sets_val, hσ4]; rw [e3]; omega)
  set σ6 := σ5.setv (B 2) (σ5.val (B 2) + 1) with hσ6
  have e6 : σ6.val (B 2) = p + 2 := by
    simp only [hσ6, hσ5, hσ4, WState.setv_val, WState.sets_val, Function.update_self]
    rw [e3]
  obtain ⟨x0, hx0⟩ := hpre.words 2 (by simp)
  have g7 := BinW.copy_spec (A := A 2) (B := A 9) (F := B 6) (R := B 7) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ6 x0 c ⟨by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hx0.1], by
      simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hx0.2]⟩
    ⟨by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hCX.1], by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff,
      hCX.2]⟩ (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hz 6 (by simp)])
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hz 7 (by simp)]) hcX
  set σ7 := σ6.sets (A 2) (frame (binary (W + 1) c)) with hσ7
  obtain ⟨d0, hd0⟩ := hpre.words 3 (by simp)
  have g8 := BinW.zero_spec (A := A 3) (B := A 9) (F := B 6) (R := B 7) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ7 d0 c ⟨by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hd0.1], by
      simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hd0.2]⟩
    ⟨by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hCX.1], by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
      emb_eq_iff, hCX.2]⟩ (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hz 6 (by simp)])
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hz 7 (by simp)]) hcX
  set σ8 := σ7.sets (A 3) (frame (binary (W + 1) 0)) with hσ8
  have hfr8 : SameExcept σ σ8 [A 1, A 2, A 3, A 7] [B 2, B 11] := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2.1,
        Function.update_of_ne hx.2.2.1, Function.update_of_ne hx.2.2.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
  have hpre8 : RPre A B W xs σ8 := by
    refine rPre_frame A B hpre (hfr8.weaken (by simp) (by simp)) (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
      emb_eq_iff, hpre.wh]) (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, frame_length]) ?_
    intro j hj
    by_cases j2 : j = 2
    · subst j2; exact ⟨c, by simp [hσ8, hσ7, emb_eq_iff], by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
        emb_eq_iff, hx0.2]⟩
    · by_cases j3 : j = 3
      · subst j3; exact ⟨0, by simp [hσ8], by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hd0.2]⟩
      · by_cases j7 : j = 7
        · subst j7; exact ⟨encS o.thr, by simp [hσ8, hσ7, hσ6, hσ5, emb_eq_iff], by simp [hσ8, hσ7, hσ6, hσ5, hσ4,
            hσ3, hσ2, hσ1, emb_eq_iff, ht0.2]⟩
        · obtain ⟨v, hv⟩ := hpre.words j hj
          have j1 : j ≠ 1 := by rintro rfl; simp at hj
          exact ⟨v, hfr8.numOn (by simp [emb_eq_iff, j1, j2, j3, j7]) hv⟩
  have hthrW : o.thr.natAbs < 2 ^ W := by omega
  let Inv : ℕ → WState ns nr → Prop := fun j ρ =>
    RPre A B W xs ρ ∧ SNumOn ρ (A 3) W (innerDot (o.inW.take j) c) ∧ NumOn ρ (A 2) (W + 1) (c / 2 ^ j) ∧
      ρ.val (B 2) = p + 2 + j ∧ SNumOn ρ (A 7) W o.thr ∧ ρ.val (B 11) = o.ref.toNat ∧
      SameExcept σ8 ρ [A 1, A 2, A 3, A 4, A 5, A 6] [B 2, B 9, B 10]
  have hInv : ∀ j ρ (q : Fin 12), q = 9 ∨ q = 10 → ∀ v, Inv j ρ → Inv j (ρ.setv (B q) v) := by
    rintro j ρ q hq v ⟨a1, a2, a3, a4, a5, a6, a7⟩
    have hs : SameExcept ρ (ρ.setv (B q) v) [] [B q] := sameExcept_setv ρ (by simp) v
    have h2q : (2 : Fin 12) ≠ q := by rcases hq with rfl | rfl <;> decide
    have h11q : (11 : Fin 12) ≠ q := by rcases hq with rfl | rfl <;> decide
    refine ⟨rPre_frame A B a1 (hs.weaken (by simp) (by rcases hq with rfl | rfl <;> simp)) (by simpa using a1.wh)
      (by simpa using a1.wl) (fun k hk => (a1.words k hk).elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩),
      ⟨BinW.numOn_setv a2.1 _ _, a2.2⟩, BinW.numOn_setv a3 _ _, ?_, ⟨BinW.numOn_setv a5.1 _ _, a5.2⟩, ?_,
      a7.trans (sameExcept_setv ρ (by rcases hq with rfl | rfl <;> simp) v)⟩
    · rw [WState.setv_val, Function.update_of_ne (hner h2q)]; exact a4
    · rw [WState.setv_val, Function.update_of_ne (hner h11q)]; exact a6
  have hσ8v : ∀ q : Fin 12, q ≠ 2 → q ≠ 11 → σ8.val (B q) = σ.val (B q) := fun q a b =>
    hfr8.val (by simp [emb_eq_iff, a, b])
  have hD8 : SNumOn σ8 (A 3) W (innerDot (o.inW.take 0) c) :=
    ⟨⟨by simp [hσ8, innerDot, encS], by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hd0.2]⟩,
      by simp [innerDot]⟩
  have hE8 : NumOn σ8 (A 2) (W + 1) (c / 2 ^ 0) :=
    ⟨by simp [hσ8, hσ7, emb_eq_iff], by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff, hx0.2]⟩
  have hT8 : SNumOn σ8 (A 7) W o.thr :=
    ⟨⟨by simp [hσ8, hσ7, hσ6, hσ5, emb_eq_iff], by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, emb_eq_iff,
      ht0.2]⟩, hthrW⟩
  have hR8 : σ8.val (B 11) = o.ref.toNat := by
    simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, Function.update_of_ne (hner (show (11 : Fin 12) ≠ 2 by decide))]
  have hrep := Runs.rep (cap := cap) (K := B 9) (K2 := B 10) (body := dotBody A B) (hner (by decide))
    (dotBodyCost W xs.length) k Inv (by omega) (fun j ρ v hI => hInv j ρ 9 (Or.inl rfl) v hI)
    (fun j ρ v hI => hInv j ρ 10 (Or.inr rfl) v hI) ?_ σ8
    ⟨hpre8, hD8, hE8, by simp [hσ8, hσ7, e6], hT8, hR8, SameExcept.refl _ _ _⟩
    (by rw [hσ8v 9 (by decide) (by decide)]; exact hK) (by rw [hσ8v 10 (by decide) (by decide)]; exact hK2)
  · have htail : ∀ ρ, (Inv k ρ ∧ ρ.val (B 9) = k ∧ ρ.val (B 10) = 0) →
        Runs cap (.seq (.ifr (B 11) (WMX.dec (B 11)) (SInt.ssub (A 7) (A 3) (A 5) (A 6) (B 4) (B 5) (B 6) (B 7)))
          (SInt.ssub (A 7) (A 8) (A 5) (A 6) (B 4) (B 5) (B 6) (B 7))) ρ (420 * W + 611 + 1 + (420 * W + 610))
          (fun τ => RPre A B W xs τ ∧ SNumOn τ (A 7) W (rTarget o c) ∧ τ.val (B 2) = p + 2 + k ∧
            τ.val (B 9) = k ∧ τ.val (B 10) = 0 ∧ τ.val (B 11) = 0 ∧
            SameExcept σ τ [A 1, A 2, A 3, A 4, A 5, A 6, A 7] [B 2]) := by
      intro ρ hρ
      obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, a8, a9⟩ := hρ
      rw [List.take_of_length_le (le_refl _)] at a2
      have hvρ : ∀ q : Fin 12, q ≠ 2 → q ≠ 9 → q ≠ 10 → ρ.val (B q) = σ8.val (B q) := fun q a b c =>
        a7.val (by simp [emb_eq_iff, a, b, c])
      obtain ⟨m0, hm0⟩ := a1.words 5 (by simp)
      obtain ⟨n0, hn0⟩ := a1.words 6 (by simp)
      have hdb := innerDot_bound o.inW c
      have hbr : Runs cap (.ifr (B 11) (WMX.dec (B 11)) (SInt.ssub (A 7) (A 3) (A 5) (A 6) (B 4) (B 5) (B 6) (B 7)))
          ρ (420 * W + 611) (fun τ => SNumOn τ (A 7) W (o.thr - (if o.ref then 0 else innerDot o.inW c)) ∧
            τ.val (B 11) = 0 ∧ (∃ a, NumOn τ (A 5) (W + 1) a) ∧ (∃ b, NumOn τ (A 6) (W + 1) b) ∧
            SameExcept ρ τ [A 5, A 6, A 7] [B 11]) := by
        by_cases hr : o.ref = true
        · have h1 : ρ.val (B 11) = 1 := by rw [a6, hr]; rfl
          have hv : ρ.val (B 11) ≠ 0 := by rw [h1]; omega
          have hd := WXExec.dec cap (B 11) ρ (by rw [h1]; omega)
          refine (Runs.ifrT hv (Runs.of hd ⟨?_, by simp [h1], ⟨m0, BinW.numOn_setv hm0 _ _⟩,
            ⟨n0, BinW.numOn_setv hn0 _ _⟩, sameExcept_setv ρ (by simp) _⟩)).cost (by omega)
          simp only [hr, if_true, sub_zero]; exact ⟨BinW.numOn_setv a5.1 _ _, a5.2⟩
        · have hf : o.ref = false := by simpa using hr
          have hsub : ∀ x ∈ [A 7, A 5, A 6], x ∈ [A 5, A 6, A 7] := by
            intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
            rcases hx with h | h | h <;> simp [h]
          have hv : ρ.val (B 11) = 0 := by rw [a6, hf]; rfl
          have hs := SInt.ssub_spec cap W (X := A 7) (Y := A 3) (M := A 5) (N := A 6) (S := B 4) (T := B 5) (F := B 6)
            (R := B 7) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) ρ o.thr (innerDot o.inW c) m0 n0 a5 a2 hm0 hn0
            (by rw [hvρ 4 (by decide) (by decide) (by decide), hσ8v 4 (by decide) (by decide)]; exact hz 4 (by simp))
            (by rw [hvρ 5 (by decide) (by decide) (by decide), hσ8v 5 (by decide) (by decide)]; exact hz 5 (by simp))
            (by rw [hvρ 6 (by decide) (by decide) (by decide), hσ8v 6 (by decide) (by decide)]; exact hz 6 (by simp))
            (by rw [hvρ 7 (by decide) (by decide) (by decide), hσ8v 7 (by decide) (by decide)]; exact hz 7 (by simp))
            (by have := Int.natAbs_sub_le o.thr (innerDot o.inW c); omega) hcX
          refine (Runs.ifrF hv (hs.post fun τ ⟨b1, b2, b3, b4⟩ => ⟨by simpa [hf] using b1, ?_, b2, b3,
            b4.weaken hsub (by simp)⟩)).cost (by omega)
          rw [b4.val (by simp)]; exact hv
      refine Runs.seq (c2 := 420 * W + 610) hbr fun τ ⟨b1, b2, ⟨m1, hm1⟩, ⟨n1, hn1⟩, b5⟩ => ?_
      have h1W : (1 : ℤ).natAbs < 2 ^ W := by rw [Int.natAbs_one]; omega
      have hvτ : ∀ q : Fin 12, q ≠ 2 → q ≠ 9 → q ≠ 10 → q ≠ 11 → τ.val (B q) = σ.val (B q) := fun q a b c d => by
        rw [b5.val (by simp [emb_eq_iff, d]), hvρ q a b c, hσ8v q a d]
      have hs := SInt.ssub_spec cap W (X := A 7) (Y := A 8) (M := A 5) (N := A 6) (S := B 4) (T := B 5) (F := B 6)
        (R := B 7) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) τ _ 1 m1 n1 b1
        ⟨b5.numOn (by simp [emb_eq_iff]) a1.one, h1W⟩ hm1 hn1
        (by rw [hvτ 4 (by decide) (by decide) (by decide) (by decide)]; exact hz 4 (by simp))
        (by rw [hvτ 5 (by decide) (by decide) (by decide) (by decide)]; exact hz 5 (by simp))
        (by rw [hvτ 6 (by decide) (by decide) (by decide) (by decide)]; exact hz 6 (by simp))
        (by rw [hvτ 7 (by decide) (by decide) (by decide) (by decide)]; exact hz 7 (by simp))
        (by
          have h1 := Int.natAbs_sub_le (o.thr - (if o.ref then 0 else innerDot o.inW c)) 1
          have h2 := Int.natAbs_sub_le o.thr (if o.ref then 0 else innerDot o.inW c)
          have h3 : (if o.ref then (0 : ℤ) else innerDot o.inW c).natAbs ≤ (o.inW.map Int.natAbs).sum := by
              split <;> simp [hdb]
          rw [Int.natAbs_one] at h1
          omega)
        hcX
      refine hs.post fun τ' ⟨d1, d2, d3, d4⟩ => ⟨?_, by simpa [rTarget] using d1, ?_, ?_, ?_, ?_, ?_⟩
      · refine rPre_frame A B a1 ((b5.comp' d4).weaken ?_ (by simp)) ?_ ?_ ?_
        · intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
          rcases hx with (h | h | h) | (h | h | h) <;> simp [h]
        · rw [d4.sh (by simp [emb_eq_iff]), b5.sh (by simp [emb_eq_iff])]; exact a1.wh
        · rw [d4.st (by simp [emb_eq_iff]), b5.st (by simp [emb_eq_iff])]; exact a1.wl
        · intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
          · obtain ⟨v, hv⟩ := a1.words 2 (by simp)
            exact ⟨v, d4.numOn (by simp [emb_eq_iff]) (b5.numOn (by simp [emb_eq_iff]) hv)⟩
          · obtain ⟨v, hv⟩ := a1.words 3 (by simp)
            exact ⟨v, d4.numOn (by simp [emb_eq_iff]) (b5.numOn (by simp [emb_eq_iff]) hv)⟩
          · obtain ⟨v, hv⟩ := a1.words 4 (by simp)
            exact ⟨v, d4.numOn (by simp [emb_eq_iff]) (b5.numOn (by simp [emb_eq_iff]) hv)⟩
          · exact d2
          · exact d3
          · exact ⟨_, d1.1⟩
      · rw [d4.val (by simp), b5.val (by simp [emb_eq_iff]), a4]
      · rw [d4.val (by simp), b5.val (by simp [emb_eq_iff]), a8]
      · rw [d4.val (by simp), b5.val (by simp [emb_eq_iff]), a9]
      · rw [d4.val (by simp)]; exact b2
      · refine ⟨fun x hx => ?_, fun r hr => ?_, by rw [d4.cell, b5.cell, a7.cell, hfr8.cell]⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
          obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hx
          have e1 := d4.1 x (by simp [n5, n6, n7])
          have e2 := b5.1 x (by simp [n5, n6, n7])
          have e3 := a7.1 x (by simp [n1, n2, n3, n4, n5, n6])
          have e4 := hfr8.1 x (by simp [n1, n2, n3, n7])
          exact ⟨e1.1.trans (e2.1.trans (e3.1.trans e4.1)), e1.2.trans (e2.2.trans (e3.2.trans e4.2))⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rw [d4.val (by simp)]
          by_cases r9 : r = B 9
          · rw [r9, b5.val (by simp [emb_eq_iff]), a8, hK]
          · by_cases r10 : r = B 10
            · rw [r10, b5.val (by simp [emb_eq_iff]), a9, hK2]
            · by_cases r11 : r = B 11
              · rw [r11, b2, hREF]
              · rw [b5.val (by simp [r11]), a7.val (by simp [hr, r9, r10]), hfr8.val (by simp [hr, r11])]
    unfold restrictP
    exact Runs.cost (Runs.seqE g1 (Runs.seqE (WXExec.wm g2) (Runs.seqE g3 (Runs.seqE g4 (Runs.seqE g5 (Runs.seqE g6
      (Runs.seqE g7 (Runs.seqE g8 (Runs.seq hrep htail))))))))) le_rfl
  · intro j hj ρ ⟨a1, a2, a3, a4, a5, a6, a7⟩
    obtain ⟨hil, hgd⟩ := hwmem j hj
    have hxi : xs[p + 2 + j] = encS (o.inW.getD j 0) := by rw [← List.getD_eq_getElem xs 0 hil]; exact hgd
    have hwj := hbw j hj
    have htk : o.inW.take (j + 1) = o.inW.take j ++ [o.inW.getD j 0] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]; rfl
    have hsum : ((o.inW.take j).map Int.natAbs).sum + (o.inW.getD j 0).natAbs ≤ (o.inW.map Int.natAbs).sum := by
      have := sum_take_le o.inW (j + 1)
      rw [htk, List.map_append, List.sum_append] at this; simpa using this
    have hdb := innerDot_bound (o.inW.take j) c
    have hdiv : c / 2 ^ j < 2 ^ (W + 1) := lt_of_le_of_lt (Nat.div_le_self _ _) hc
    have hx := dotBody_spec A B cap W xs ρ (p + 2 + j) (c / 2 ^ j) (o.inW.getD j 0) (innerDot (o.inW.take j) c) hil
      hxi (by omega) a1 a4 a3 hdiv a2
      (by have := Int.natAbs_add_le (innerDot (o.inW.take j) c) (o.inW.getD j 0); omega) (by omega)
    refine hx.post fun τ ⟨b1, b2, b3, b4, b5⟩ => ⟨⟨b1, ?_, ?_, by rw [b4]; ring, SInt.SameExcept.sNumOn b5
      (by simp [emb_eq_iff]) a5, by rw [b5.val (by simp [emb_eq_iff])]; exact a6, a7.trans (b5.weaken (by simp)
      (by simp))⟩, b5.val (by simp [emb_eq_iff]), b5.val (by simp [emb_eq_iff])⟩
    · rw [htk, innerDot_snoc, List.length_take, min_eq_left (by omega)]; exact b2
    · rw [pow_succ, ← Nat.div_div_eq_div_mul]; exact b3

end Restrict2

end NearCubicGates.Close.TabMachine
