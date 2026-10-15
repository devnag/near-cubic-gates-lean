import Proof.Gates.TabMachine.Stack2

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

theorem innerDot_snoc (l : List ℤ) (w : ℤ) (c : ℕ) :
    innerDot (l ++ [w]) c = innerDot l c + (if c / 2 ^ l.length % 2 = 1 then w else 0) := by
  induction l generalizing c with
  | nil => simp [innerDot]
  | cons x l ih =>
    simp only [List.cons_append, innerDot, ih, List.length_cons]
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
    ring

theorem innerDot_bound (l : List ℤ) (c : ℕ) : (innerDot l c).natAbs ≤ (l.map Int.natAbs).sum := by
  induction l generalizing c with
  | nil => simp [innerDot]
  | cons x l ih =>
    simp only [innerDot, List.map_cons, List.sum_cons]
    have := ih (c / 2)
    have h2 := Int.natAbs_add_le (if c % 2 = 1 then x else 0) (innerDot l (c / 2))
    split at h2
    · omega
    · simp only [Int.natAbs_zero, Nat.zero_add] at h2; omega

theorem sum_take_le (l : List ℤ) (j : ℕ) : ((l.take j).map Int.natAbs).sum ≤ (l.map Int.natAbs).sum := by
  conv_rhs => rw [← List.take_append_drop j l]
  rw [List.map_append, List.sum_append]; omega

/-- The occurrence block's records: `ref`, `θ`, the inner weights, the outer weights. -/
def occRecs (o : Occ) : List ℕ := [o.ref.toNat, encS o.thr] ++ o.inW.map encS ++ o.outW.map encS

section Restrict
/- Streams: `0` the occurrence stream `PG`, `1` the read work stream, `2` `c` being halved, `3` DOT, `4` the weight,
`5, 6` arithmetic scratch, `7` the target word (the compiler's `S 11`), `8` the word `encS 1`, `9` the word `c`.
Registers: `0, 1, 3` read scratch, `2` the read index, `4`-`7` arithmetic scratch, `8` the bit flag, `9` `k`
(count), `10` scratch, `11` the reference flag. -/
variable (A : Fin 10 ↪ Fin (ns + 1)) (B : Fin 12 ↪ Fin nr)

/-- One inner weight: `DOT += [bit] · w_j`, `c := c / 2`. -/
def dotBody : WMX ns nr :=
  .seq (getAt (A 0) (A 1) (B 0) (B 1) (B 2) (B 3))
  (.seq (BinW.copy (A 4) (A 1) (B 6) (B 7))
  (.seq (.wm (SInt.sgnBitW (A 2) (B 8)))
  (.seq (.ifr (B 8) (.seq (WMX.dec (B 8)) (SInt.sadd (A 3) (A 4) (A 5) (A 6) (B 4) (B 5) (B 6) (B 7))) WMX.skip)
  (.seq (BinW.half (A 2) (B 7)) (WMX.inc (B 2))))))

def dotBodyCost (W n : ℕ) : ℕ :=
  (n + 1) * (40 * (W + 1) + 40) + 10 * (n + 1) * (2 * (W + 1) + 1) + 10 + 1 + (41 * (W + 1) + 3 + 1 +
    (8 + 1 + (1 + 1 + (410 * W + 600) + 1 + 1 + (34 * (W + 1) + 3 + 1 + 3))))

/-- The resting data of the restriction step. -/
structure RPre (W : ℕ) (xs : List ℕ) (σ : WState ns nr) : Prop where
  pg : ∃ junk, σ.st (A 0) = recStream (xs.map (binary (W + 1))) ++ junk
  pgh : σ.sh (A 0) = 0
  wh : σ.sh (A 1) = 0
  wl : (σ.st (A 1)).length ≤ 2 * (W + 1) + 1
  words : ∀ k : Fin 10, k ∈ [(2 : Fin 10), 3, 4, 5, 6, 7] → ∃ v, NumOn σ (A k) (W + 1) v
  one : NumOn σ (A 8) (W + 1) 2
  zero : ∀ k : Fin 12, k ∈ [(0 : Fin 12), 1, 3, 4, 5, 6, 7, 8] → σ.val (B k) = 0

theorem rPre_frame {W : ℕ} {xs : List ℕ} {σ τ : WState ns nr} (h : RPre A B W xs σ)
    (hfr : SameExcept σ τ [A 1, A 2, A 3, A 4, A 5, A 6, A 7] [B 2, B 9, B 10, B 11])
    (hwh : τ.sh (A 1) = 0) (hwl : (τ.st (A 1)).length ≤ 2 * (W + 1) + 1)
    (hw : ∀ k : Fin 10, k ∈ [(2 : Fin 10), 3, 4, 5, 6, 7] → ∃ v, NumOn τ (A k) (W + 1) v) : RPre A B W xs τ := by
  have h0 := hfr.1 (A 0) (by simp [emb_eq_iff])
  have h8 := hfr.1 (A 8) (by simp [emb_eq_iff])
  refine ⟨by rw [h0.1]; exact h.pg, by rw [h0.2]; exact h.pgh, hwh, hwl, hw, ⟨by rw [h8.1]; exact h.one.1,
    by rw [h8.2]; exact h.one.2⟩, fun k hk => ?_⟩
  rw [hfr.val (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [emb_eq_iff])]
  exact h.zero k hk

theorem dotBody_spec (cap W : ℕ) (xs : List ℕ) (ρ : WState ns nr) (i e : ℕ) (w d : ℤ) (hi : i < xs.length)
    (hxi : xs[i] = encS w) (hw : w.natAbs < 2 ^ W) (hpre : RPre A B W xs ρ) (hIDX : ρ.val (B 2) = i)
    (hE : NumOn ρ (A 2) (W + 1) e) (he : e < 2 ^ (W + 1)) (hD : SNumOn ρ (A 3) W d)
    (hdw : (d + w).natAbs < 2 ^ W)
    (hcap : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * xs.length ≤ cap) :
    Runs cap (dotBody A B) ρ (dotBodyCost W xs.length) (fun τ =>
      RPre A B W xs τ ∧ SNumOn τ (A 3) W (d + if e % 2 = 1 then w else 0) ∧ NumOn τ (A 2) (W + 1) (e / 2) ∧
        τ.val (B 2) = i + 1 ∧ SameExcept ρ τ [A 1, A 2, A 3, A 4, A 5, A 6] [B 2]) := by
  have hne : ∀ {a b : Fin 10}, a ≠ b → A a ≠ A b := fun h => emb_ne A h
  have hner : ∀ {a b : Fin 12}, a ≠ b → B a ≠ B b := fun h => emb_ne B h
  have hz := hpre.zero
  have hcX : 2 * (W + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < xs.length + 1 by omega); omega
  obtain ⟨junk, hj⟩ := hpre.pg
  have g1 := getAt_spec cap (A := A 0) (Wk := A 1) (CA := B 0) (CW := B 1) (N := B 2) (K2 := B 3) (hne (by decide))
    (by simp [emb_eq_iff]) (W + 1) (by omega) xs i hi ρ junk hj hpre.pgh (hz 0 (by simp)) hpre.wh hpre.wl
    (hz 1 (by simp)) hIDX (hz 3 (by simp)) (by omega)
  rw [hxi] at g1
  set ρ1 := ρ.sets (A 1) (frame (binary (W + 1) (encS w))) with hρ1
  obtain ⟨t0, ht0⟩ := hpre.words 4 (by simp)
  have g2 := BinW.copy_spec (A := A 4) (B := A 1) (F := B 6) (R := B 7) cap (W + 1) (hne (by decide))
    (hner (by decide)) ρ1 t0 (encS w) (BinW.numOn_sets_ne ht0 (hne (by decide)) _)
    (BinW.numOn_sets_self _ _ _ _ hpre.wh) (by simp [hρ1, hz 6 (by simp)]) (by simp [hρ1, hz 7 (by simp)]) hcX
  set ρ2 := ρ1.sets (A 4) (frame (binary (W + 1) (encS w))) with hρ2
  have hfr2 : SameExcept ρ ρ2 [A 1, A 4] [] := by
    refine ⟨fun x hx => ?_, fun r _ => by simp [hρ2, hρ1], by simp [hρ2, hρ1]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hρ2, hρ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
  have hE2 : NumOn ρ2 (A 2) (W + 1) e := hfr2.numOn (by simp [emb_eq_iff]) hE
  have g3 := SInt.sgnBitW_spec cap (X := A 2) (S := B 8) ρ2 W e hE2 (by rw [hfr2.val (by simp)]; exact hz 8 (by simp))
    (by omega)
  set ρ3 := ρ2.setv (B 8) (e % 2) with hρ3
  have hv3 : ∀ k : Fin 12, k ≠ 8 → ρ3.val (B k) = ρ.val (B k) := fun k hk => by
    rw [hρ3, WState.setv_val, Function.update_of_ne (hner hk), hfr2.val (by simp)]
  obtain ⟨m0, hm0⟩ := hpre.words 5 (by simp)
  obtain ⟨n0, hn0⟩ := hpre.words 6 (by simp)
  have hW4n2 : NumOn ρ2 (A 4) (W + 1) (encS w) :=
    BinW.numOn_sets_self _ _ _ _ (by simp [hρ1, emb_eq_iff, ht0.2])
  have hW4 : SNumOn ρ3 (A 4) W w := ⟨BinW.numOn_setv hW4n2 _ _, hw⟩
  -- the branch
  have hbr : Runs cap (.ifr (B 8) (.seq (WMX.dec (B 8)) (SInt.sadd (A 3) (A 4) (A 5) (A 6) (B 4) (B 5) (B 6) (B 7)))
      WMX.skip) ρ3 (1 + 1 + (410 * W + 600) + 1) (fun τ => SNumOn τ (A 3) W (d + if e % 2 = 1 then w else 0) ∧
        (∃ a, NumOn τ (A 5) (W + 1) a) ∧ (∃ b, NumOn τ (A 6) (W + 1) b) ∧ τ.val (B 8) = 0 ∧
        SameExcept ρ3 τ [A 3, A 5, A 6] [B 8]) := by
    by_cases he1 : e % 2 = 1
    · have hv : ρ3.val (B 8) ≠ 0 := by simp [hρ3, he1]
      have hd8 := WXExec.dec cap (B 8) ρ3 (by simp [hρ3, he1]; omega)
      set ρ4 := ρ3.setv (B 8) (ρ3.val (B 8) - 1) with hρ4
      have hfr4 : SameExcept ρ3 ρ4 [] [B 8] := sameExcept_setv ρ3 (by simp) _
      have hs := SInt.sadd_spec cap W (X := A 3) (Y := A 4) (M := A 5) (N := A 6) (S := B 4) (T := B 5) (F := B 6)
        (R := B 7) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) ρ4 d w m0 n0
        (SInt.SameExcept.sNumOn (hfr2.comp' ((sameExcept_setv ρ2 (S := []) (Rg := [B 8]) (by simp) _).comp' hfr4))
          (by simp [emb_eq_iff]) hD)
        (SInt.SameExcept.sNumOn hfr4 (by simp) hW4)
        (hfr4.numOn (by simp) ((hfr2.comp' (sameExcept_setv ρ2 (S := []) (Rg := [B 8]) (by simp) _)).numOn
          (by simp [emb_eq_iff]) hm0))
        (hfr4.numOn (by simp) ((hfr2.comp' (sameExcept_setv ρ2 (S := []) (Rg := [B 8]) (by simp) _)).numOn
          (by simp [emb_eq_iff]) hn0))
        (by rw [hfr4.val (by simp [emb_eq_iff]), hv3 4 (by decide)]; exact hz 4 (by simp))
        (by rw [hfr4.val (by simp [emb_eq_iff]), hv3 5 (by decide)]; exact hz 5 (by simp))
        (by rw [hfr4.val (by simp [emb_eq_iff]), hv3 6 (by decide)]; exact hz 6 (by simp))
        (by rw [hfr4.val (by simp [emb_eq_iff]), hv3 7 (by decide)]; exact hz 7 (by simp)) hdw hcX
      refine (Runs.ifrT hv (Runs.seqE hd8 (hs.post fun τ ⟨b1, b2, b3, b4⟩ => ⟨by simpa [he1] using b1, b2, b3, ?_,
        ?_⟩))).cost (by omega)
      · rw [b4.val (by simp [emb_eq_iff])]; simp [hρ4, hρ3, he1]
      · exact (hfr4.comp' b4).weaken (by simp) (by simp)
    · have hv : ρ3.val (B 8) = 0 := by simp [hρ3]; omega
      refine (Runs.ifrF hv (Runs.of (WXExec.skip cap ρ3) ⟨?_, ⟨m0, ?_⟩, ⟨n0, ?_⟩, hv, SameExcept.refl _ _ _⟩)).cost
        (by omega)
      · simpa [he1] using SInt.SameExcept.sNumOn (hfr2.comp' (sameExcept_setv ρ2 (S := []) (Rg := [B 8]) (by simp) _))
          (by simp [emb_eq_iff]) hD
      · exact (hfr2.comp' (sameExcept_setv ρ2 (S := []) (Rg := [B 8]) (by simp) _)).numOn (by simp [emb_eq_iff]) hm0
      · exact (hfr2.comp' (sameExcept_setv ρ2 (S := []) (Rg := [B 8]) (by simp) _)).numOn (by simp [emb_eq_iff]) hn0
  have cc1 := Nat.mul_le_mul_right (40 * (W + 1) + 40) (show i + 1 ≤ xs.length + 1 by omega)
  have cc2 := Nat.mul_le_mul_right (2 * (W + 1) + 1) (Nat.mul_le_mul_left 10 (show i + 1 ≤ xs.length + 1 by omega))
  refine (Runs.seqE g1 (Runs.seqE g2 (Runs.seqE (WXExec.wm g3) (Runs.seq (c2 := 34 * (W + 1) + 3 + 1 + 3) hbr
    fun ρ4 hρ4 => ?_)))).cost (by unfold dotBodyCost; omega)
  obtain ⟨b1, ⟨ma, hma⟩, ⟨nb, hnb⟩, b4, b5⟩ := hρ4
  have hE4 : NumOn ρ4 (A 2) (W + 1) e :=
    b5.numOn (by simp [emb_eq_iff]) (BinW.numOn_setv hE2 _ _)
  have hh := BinW.half_spec (A := A 2) (R := B 7) cap (W + 1) ρ4 e hE4
    (by rw [b5.val (by simp [emb_eq_iff]), hv3 7 (by decide)]; exact hz 7 (by simp)) he (by omega)
  set ρ5 := ρ4.sets (A 2) (frame (binary (W + 1) (e / 2))) with hρ5
  have e2 : ρ5.val (B 2) = i := by
    simp only [hρ5, WState.sets_val]; rw [b5.val (by simp [emb_eq_iff]), hv3 2 (by decide), hIDX]
  have hi2 := WXExec.inc cap (B 2) ρ5 (by rw [e2]; omega)
  have hfr : SameExcept ρ (ρ5.setv (B 2) (ρ5.val (B 2) + 1)) [A 1, A 2, A 3, A 4, A 5, A 6] [B 2] := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ5, b5.cell, hρ3, hfr2.cell]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      have h1 := b5.1 x (by simp [hx.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2])
      have h2 := hfr2.1 x (by simp [hx.1, hx.2.2.2.1])
      simp only [WState.setv_st, WState.setv_sh, hρ5, WState.sets_st, WState.sets_sh,
        Function.update_of_ne hx.2.1, h1.1, h1.2, hρ3]
      exact h2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [WState.setv_val, Function.update_of_ne hr, hρ5, WState.sets_val]
      by_cases r8 : r = B 8
      · rw [r8, b4, hz 8 (by simp)]
      · rw [b5.val (by simp [r8]), hρ3, WState.setv_val, Function.update_of_ne r8, hfr2.val (by simp)]
  have hfrw : SameExcept ρ (ρ5.setv (B 2) (ρ5.val (B 2) + 1)) [A 1, A 2, A 3, A 4, A 5, A 6, A 7]
      [B 2, B 9, B 10, B 11] := by
    refine hfr.weaken ?_ (by simp)
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h <;> simp [h]
  refine Runs.of (WXExec.seq hh hi2) ⟨?_, ?_, ?_, ?_, hfr⟩
  · refine rPre_frame A B hpre hfrw ?_ ?_ ?_
    · rw [WState.setv_sh, hρ5, WState.sets_sh, b5.sh (by simp [emb_eq_iff])]
      simp [hρ3, hρ2, hρ1, emb_eq_iff, hpre.wh]
    · rw [WState.setv_st, hρ5, WState.sets_st, Function.update_of_ne (hne (by decide)), b5.st (by simp [emb_eq_iff])]
      simp [hρ3, hρ2, hρ1, emb_eq_iff, frame_length]
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ hE4.2) _ _⟩
      · exact ⟨_, BinW.numOn_setv (BinW.numOn_sets_ne b1.1 (hne (by decide)) _) _ _⟩
      · exact ⟨_, BinW.numOn_setv (BinW.numOn_sets_ne (b5.numOn (by simp [emb_eq_iff]) hW4.1)
          (hne (by decide)) _) _ _⟩
      · exact ⟨_, BinW.numOn_setv (BinW.numOn_sets_ne hma (hne (by decide)) _) _ _⟩
      · exact ⟨_, BinW.numOn_setv (BinW.numOn_sets_ne hnb (hne (by decide)) _) _ _⟩
      · obtain ⟨v, hv⟩ := hpre.words 7 (by simp)
        exact ⟨v, hfr.numOn (by simp [emb_eq_iff]) hv⟩
  · exact ⟨BinW.numOn_setv (BinW.numOn_sets_ne b1.1 (hne (by decide)) _) _ _, b1.2⟩
  · exact BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ hE4.2) _ _
  · rw [WState.setv_val, Function.update_self, e2]

/-- **The restriction**: `T := θ − [¬ref]·innerDot w c − 1` from the block `[ref, θ, w…]` at read index `p`. -/
def restrictP : WMX ns nr :=
  .seq (getAt (A 0) (A 1) (B 0) (B 1) (B 2) (B 3))
  (.seq (.wm (SInt.sgnBitW (A 1) (B 11)))
  (.seq (WMX.inc (B 2))
  (.seq (getAt (A 0) (A 1) (B 0) (B 1) (B 2) (B 3))
  (.seq (BinW.copy (A 7) (A 1) (B 6) (B 7))
  (.seq (WMX.inc (B 2))
  (.seq (BinW.copy (A 2) (A 9) (B 6) (B 7))
  (.seq (BinW.zero (A 3) (A 9) (B 6) (B 7))
  (.seq (repK (B 9) (B 10) (dotBody A B))
  (.seq (.ifr (B 11) (WMX.dec (B 11)) (SInt.ssub (A 7) (A 3) (A 5) (A 6) (B 4) (B 5) (B 6) (B 7)))
  (SInt.ssub (A 7) (A 8) (A 5) (A 6) (B 4) (B 5) (B 6) (B 7)))))))))))

/-- The restriction's cost (exact composition; `p` the block's read index, `n` the stream's record count). -/
def restrictCost (W n k p : ℕ) : ℕ :=
  (p + 1) * (40 * (W + 1) + 40) + 10 * (p + 1) * (2 * (W + 1) + 1) + 10 + 1 + (8 + 1 + (3 + 1 +
    ((p + 1 + 1) * (40 * (W + 1) + 40) + 10 * (p + 1 + 1) * (2 * (W + 1) + 1) + 10 + 1 +
    (41 * (W + 1) + 3 + 1 + (3 + 1 + (41 * (W + 1) + 3 + 1 + (41 * (W + 1) + 3 + 1 +
    (k * (dotBodyCost W n + 8) + 7 * k + 3 + 1 + (420 * W + 611 + 1 + (420 * W + 610))))))))))

theorem seg_get (xs : List ℕ) (p : ℕ) (seg : List ℕ) (h : (xs.drop p).take seg.length = seg) (i : ℕ)
    (hi : i < seg.length) : p + i < xs.length ∧ ∀ (h' : p + i < xs.length), xs[p + i] = seg[i] := by
  have hl : ((xs.drop p).take seg.length).length = seg.length := by rw [h]
  rw [List.length_take, List.length_drop] at hl
  refine ⟨by omega, fun h' => ?_⟩
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_take, if_pos hi, List.getElem?_drop, List.getElem?_eq_getElem h',
    List.getElem?_eq_getElem hi, Option.some.injEq] at this
  exact this

end Restrict

end NearCubicGates.Close.TabMachine
