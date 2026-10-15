import Proof.Gates.TabMachine.StackVal

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

section Stack
/- Streams: `0` the tuples' fields `TP`, `1` the read work stream, `2` the cut stream, `3` ACC, `4` PW, `5` BASE,
`6` FLD, `7`-`10` arithmetic scratch, `11` the coefficient, `12` the word `0`, `13` the word `2` (= `encS 1`).
Registers: `0, 1, 3` read scratch, `2` the read index, `4` copy scratch, `5` the cut stream counter, `6`-`10`
arithmetic scratch, `11` `M` (fields per tuple, count), `12` scratch, `13` `N` (count), `14` scratch, `15` `N`
(stride), `16` `m` (children per tuple, count), `17` scratch, `18` the tuple's offset, `19` the field's offset,
`20` scratch, `21` the tuple count, `22` scratch, `23` `M` (stride), `24` the cut count. -/
variable (U : Fin 14 ↪ Fin (ns + 1)) (V : Fin 25 ↪ Fin nr)

/-- The stacking machine's data at rest. -/
structure SPre (Wd M N m : ℕ) (fl : List ℕ) (coef : ℤ) (σ : WState ns nr) : Prop where
  tp : ∃ junk, σ.st (U 0) = recStream (fl.map (binary (Wd + 1))) ++ junk
  tph : σ.sh (U 0) = 0
  wh : σ.sh (U 1) = 0
  wl : (σ.st (U 1)).length ≤ 2 * (Wd + 1) + 1
  words : ∀ k : Fin 14, k ∈ [(3 : Fin 14), 4, 5, 6, 7, 8, 9, 10] → ∃ v, NumOn σ (U k) (Wd + 1) v
  coef : NumOn σ (U 11) (Wd + 1) (encS coef)
  zr : NumOn σ (U 12) (Wd + 1) 0
  two : NumOn σ (U 13) (Wd + 1) 2
  zero : ∀ k : Fin 25, k ∈ [(0 : Fin 25), 1, 3, 4, 6, 7, 8, 9, 10, 20] → σ.val (V k) = 0
  js : σ.val (V 15) = N
  ms : σ.val (V 23) = M

/-- The streams and registers the stacking machine may change. -/
def sStreams : List (Fin (ns + 1)) := [U 1, U 2, U 3, U 4, U 5, U 6, U 7, U 8, U 9, U 10]
def sRegs : List (Fin nr) := [V 2, V 5, V 11, V 12, V 13, V 14, V 16, V 17, V 18, V 19, V 21, V 22, V 24]

theorem sPre_frame {Wd M N m : ℕ} {fl : List ℕ} {coef : ℤ} {σ τ : WState ns nr}
    (h : SPre U V Wd M N m fl coef σ) (hfr : SameExcept σ τ (sStreams U) (sRegs V))
    (hwh : τ.sh (U 1) = 0) (hwl : (τ.st (U 1)).length ≤ 2 * (Wd + 1) + 1)
    (hw : ∀ k : Fin 14, k ∈ [(3 : Fin 14), 4, 5, 6, 7, 8, 9, 10] → ∃ v, NumOn τ (U k) (Wd + 1) v) :
    SPre U V Wd M N m fl coef τ := by
  have hs : ∀ k : Fin 14, k = 0 ∨ k = 11 ∨ k = 12 ∨ k = 13 → τ.st (U k) = σ.st (U k) ∧ τ.sh (U k) = σ.sh (U k) :=
    fun k hk => hfr.1 _ (by
      unfold sStreams; rcases hk with rfl | rfl | rfl | rfl <;> simp [emb_eq_iff])
  have hv : ∀ k : Fin 25, k ∉ [(2 : Fin 25), 5, 11, 12, 13, 14, 16, 17, 18, 19, 21, 22, 24] →
      τ.val (V k) = σ.val (V k) := fun k hk => hfr.2.1 _ (by unfold sRegs; simpa [emb_eq_iff] using hk)
  have hz : ∀ k : Fin 25, k ∈ [(0 : Fin 25), 1, 3, 4, 6, 7, 8, 9, 10, 20] → τ.val (V k) = 0 := by
    intro k hk
    have hk' : k ∉ [(2 : Fin 25), 5, 11, 12, 13, 14, 16, 17, 18, 19, 21, 22, 24] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hv k hk']; exact h.zero k hk
  have h0 := hs 0 (by decide)
  have h11 := hs 11 (by decide)
  have h12 := hs 12 (by decide)
  have h13 := hs 13 (by decide)
  exact ⟨by rw [h0.1]; exact h.tp, by rw [h0.2]; exact h.tph, hwh, hwl, hw,
    ⟨by rw [h11.1]; exact h.coef.1, by rw [h11.2]; exact h.coef.2⟩,
    ⟨by rw [h12.1]; exact h.zr.1, by rw [h12.2]; exact h.zr.2⟩,
    ⟨by rw [h13.1]; exact h.two.1, by rw [h13.2]; exact h.two.2⟩, hz,
    by rw [hv 15 (by decide)]; exact h.js, by rw [hv 23 (by decide)]; exact h.ms⟩

/-- `BASE += |TP[IDX]|`, `IDX += 1`. -/
def sumBody : WMX ns nr :=
  .seq (getAt (U 0) (U 1) (V 0) (V 1) (V 2) (V 3))
  (.seq (BinW.copy (U 6) (U 1) (V 8) (V 9))
  (.seq (BinW.half (U 6) (V 9))
  (.seq (BinW.add (U 5) (U 6) (V 8) (V 9)) (WMX.inc (V 2)))))

def sumBodyCost (Wd n : ℕ) : ℕ :=
  (n + 1) * (40 * (Wd + 1) + 40) + 10 * (n + 1) * (2 * (Wd + 1) + 1) + 10 + 1 +
    (41 * (Wd + 1) + 3 + 1 + (34 * (Wd + 1) + 3 + 1 + (41 * (Wd + 1) + 3 + 1 + 3)))

theorem sumBody_spec (cap Wd M N m : ℕ) (fl : List ℕ) (coef : ℤ) (ρ : WState ns nr) (i acc : ℕ)
    (hi : i < fl.length) (hpre : SPre U V Wd M N m fl coef ρ) (hIDX : ρ.val (V 2) = i)
    (hB : NumOn ρ (U 5) (Wd + 1) acc) (hfl : ∀ x ∈ fl, x < 2 ^ (Wd + 1)) (hacc : acc + fl[i] / 2 < 2 ^ (Wd + 1))
    (hcap : (fl.length + 1) * (2 * (Wd + 1) + 1) + 2 * fl.length ≤ cap) :
    Runs cap (sumBody U V) ρ (sumBodyCost Wd fl.length) (fun τ =>
      SPre U V Wd M N m fl coef τ ∧ NumOn τ (U 5) (Wd + 1) (acc + fl[i] / 2) ∧ τ.val (V 2) = i + 1 ∧
        SameExcept ρ τ [U 1, U 5, U 6] [V 2]) := by
  have hne : ∀ {a b : Fin 14}, a ≠ b → U a ≠ U b := fun h => emb_ne U h
  have hner : ∀ {a b : Fin 25}, a ≠ b → V a ≠ V b := fun h => emb_ne V h
  have hz := hpre.zero
  have hcX : 2 * (Wd + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (Wd + 1) + 1) (show 0 < fl.length + 1 by omega); omega
  obtain ⟨junk, hj⟩ := hpre.tp
  have h1 := getAt_spec cap (A := U 0) (Wk := U 1) (CA := V 0) (CW := V 1) (N := V 2) (K2 := V 3) (hne (by decide))
    (by simp [emb_eq_iff]) (Wd + 1) (by omega) fl i hi ρ junk hj hpre.tph (hz 0 (by simp)) hpre.wh hpre.wl
    (hz 1 (by simp)) hIDX (hz 3 (by simp)) (by omega)
  set ρ1 := ρ.sets (U 1) (frame (binary (Wd + 1) fl[i])) with hρ1
  obtain ⟨f0, hf0⟩ := hpre.words 6 (by simp)
  have h2 := BinW.copy_spec (A := U 6) (B := U 1) (F := V 8) (R := V 9) cap (Wd + 1) (hne (by decide))
    (hner (by decide)) ρ1 f0 fl[i] (BinW.numOn_sets_ne hf0 (hne (by decide)) _)
    (BinW.numOn_sets_self _ _ _ _ hpre.wh) (by simp [hρ1, hz 8 (by simp)]) (by simp [hρ1, hz 9 (by simp)]) (by omega)
  set ρ2 := ρ1.sets (U 6) (frame (binary (Wd + 1) fl[i])) with hρ2
  have h3 := BinW.half_spec (A := U 6) (R := V 9) cap (Wd + 1) ρ2 fl[i]
    (BinW.numOn_sets_self _ _ _ _ (by simp [hρ1, emb_eq_iff, hf0.2])) (by simp [hρ2, hρ1, hz 9 (by simp)])
    (hfl _ (List.getElem_mem hi)) (by omega)
  set ρ3 := ρ2.sets (U 6) (frame (binary (Wd + 1) (fl[i] / 2))) with hρ3
  have h4 := BinW.add_spec (A := U 5) (B := U 6) (F := V 8) (R := V 9) cap (Wd + 1) (hne (by decide))
    (hner (by decide)) ρ3 acc (fl[i] / 2)
    ⟨by simp [hρ3, hρ2, hρ1, emb_eq_iff, hB.1], by simp [hρ3, hρ2, hρ1, emb_eq_iff, hB.2]⟩
    (BinW.numOn_sets_self _ _ _ _ (by simp [hρ2, hρ1, emb_eq_iff, hf0.2]))
    (by simp [hρ3, hρ2, hρ1, hz 8 (by simp)]) (by simp [hρ3, hρ2, hρ1, hz 9 (by simp)]) hacc (by omega)
  set ρ4 := ρ3.sets (U 5) (frame (binary (Wd + 1) (acc + fl[i] / 2))) with hρ4
  have e5 : ρ4.val (V 2) = i := by simp [hρ4, hρ3, hρ2, hρ1, hIDX]
  have h5 := WXExec.inc cap (V 2) ρ4 (by rw [e5]; omega)
  have hfr : SameExcept ρ (ρ4.setv (V 2) (ρ4.val (V 2) + 1)) [U 1, U 5, U 6] [V 2] := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ4, hρ3, hρ2, hρ1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [hρ4, hρ3, hρ2, hρ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2.1,
        Function.update_of_ne hx.2.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [hρ4, hρ3, hρ2, hρ1, Function.update_of_ne hr]
  have c1 := Nat.mul_le_mul_right (40 * (Wd + 1) + 40) (show i + 1 ≤ fl.length + 1 by omega)
  have c2 := Nat.mul_le_mul_right (2 * (Wd + 1) + 1) (Nat.mul_le_mul_left 10 (show i + 1 ≤ fl.length + 1 by omega))
  refine Runs.of ((WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 h5)))).mono
    (by unfold sumBodyCost; omega)) ⟨?_, ?_, ?_, hfr⟩
  · refine sPre_frame U V hpre (hfr.weaken (by unfold sStreams; simp) (by unfold sRegs; simp)) ?_ ?_ ?_
    · simp [hρ4, hρ3, hρ2, hρ1, emb_eq_iff, hpre.wh]
    · simp [hρ4, hρ3, hρ2, hρ1, emb_eq_iff, frame_length]
    · intro k hk
      by_cases k5 : k = 5
      · subst k5; exact ⟨_, BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ (by
          simp [hρ3, hρ2, hρ1, emb_eq_iff, hB.2])) _ _⟩
      · by_cases k6 : k = 6
        · subst k6; exact ⟨fl[i] / 2, BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _ (by
            simp [hρ2, hρ1, emb_eq_iff, hf0.2])) (hne (by decide)) _) _ _⟩
        · obtain ⟨v, hv⟩ := hpre.words k hk
          exact ⟨v, hfr.numOn (by
            have k1 : k ≠ 1 := by rintro rfl; simp at hk
            simp [emb_eq_iff, k1, k5, k6]) hv⟩
  · exact BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ (by simp [hρ3, hρ2, hρ1, emb_eq_iff, hB.2])) _ _
  · simp [hρ4, hρ3, hρ2, hρ1, hIDX]

/-- `Σ_{q < k} |f_{t₀+q}|` (the records are `encS f`). -/
def absSum (fl : List ℕ) (t0 k : ℕ) : ℕ := ((List.range k).map fun q => fl.getD (t0 + q) 0 / 2).sum

theorem absSum_succ (fl : List ℕ) (t0 k : ℕ) : absSum fl t0 (k + 1) = absSum fl t0 k + fl.getD (t0 + k) 0 / 2 := by
  unfold absSum; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem absSum_mono (fl : List ℕ) (t0 k M : ℕ) (h : k ≤ M) : absSum fl t0 k ≤ absSum fl t0 M := by
  induction M with
  | zero => have : k = 0 := by omega
            subst this; exact le_refl _
  | succ M ih =>
    rcases Nat.lt_or_ge k (M + 1) with h1 | h1
    · rw [absSum_succ]; have := ih (by omega); omega
    · have : k = M + 1 := by omega
      subst this; exact le_refl _

/-- `BASE := encS (1 + Σ_{q < M} |TP[t₀ + q]|)` (`t₀` in register `18`). -/
def baseP : WMX ns nr :=
  .seq (BinW.copy (U 5) (U 12) (V 8) (V 9))
  (.seq (addR (V 18) (V 2) (V 20))
  (.seq (repK (V 11) (V 12) (sumBody U V))
  (.seq (.wm (WM.clear (V 2)))
  (.seq (BinW.inc (U 5) (U 12) (V 8) (V 9)) (BinW.shl (U 5) (U 12) (V 8) (V 9))))))

def baseCost (Wd M n t0 : ℕ) : ℕ :=
  41 * (Wd + 1) + 3 + 1 + (18 * t0 + 3 + 1 + (M * (sumBodyCost Wd n + 8) + 7 * M + 3 + 1 + (3 * (t0 + M) + 1 + 1 +
    (41 * (Wd + 1) + 7 + 1 + (41 * (Wd + 1) + 8)))))

theorem baseP_spec (cap Wd M N m : ℕ) (fl : List ℕ) (coef : ℤ) (σ : WState ns nr) (t0 : ℕ)
    (hk : t0 + M ≤ fl.length) (hpre : SPre U V Wd M N m fl coef σ) (hIDX : σ.val (V 2) = 0)
    (hB0 : σ.val (V 18) = t0) (hMC : σ.val (V 11) = M) (hMC2 : σ.val (V 12) = 0) (hfl : ∀ x ∈ fl, x < 2 ^ (Wd + 1))
    (hS : 2 * (absSum fl t0 M + 1) < 2 ^ (Wd + 1))
    (hcap : (fl.length + 1) * (2 * (Wd + 1) + 1) + 2 * fl.length + 2 * M ≤ cap) :
    Runs cap (baseP U V) σ (baseCost Wd M fl.length t0) (fun τ =>
      SPre U V Wd M N m fl coef τ ∧ NumOn τ (U 5) (Wd + 1) (encS ((absSum fl t0 M + 1 : ℕ) : ℤ)) ∧
        τ.val (V 2) = 0 ∧ SameExcept σ τ [U 1, U 5, U 6] []) := by
  have hne : ∀ {a b : Fin 14}, a ≠ b → U a ≠ U b := fun h => emb_ne U h
  have hner : ∀ {a b : Fin 25}, a ≠ b → V a ≠ V b := fun h => emb_ne V h
  have hz := hpre.zero
  have hcX : 2 * (Wd + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (Wd + 1) + 1) (show 0 < fl.length + 1 by omega); omega
  obtain ⟨b0, hb0⟩ := hpre.words 5 (by simp)
  have h1 := BinW.copy_spec (A := U 5) (B := U 12) (F := V 8) (R := V 9) cap (Wd + 1) (hne (by decide))
    (hner (by decide)) σ b0 0 hb0 hpre.zr (hz 8 (by simp)) (hz 9 (by simp)) hcX
  set σ1 := σ.sets (U 5) (frame (binary (Wd + 1) 0)) with hσ1
  have hfr1 : SameExcept σ σ1 [U 5] [] := sameExcept_sets σ (by simp) _
  have h2 := addR_spec cap (A := V 18) (B := V 2) (T := V 20) (hner (by decide)) (hner (by decide))
    (hner (by decide)) σ1 (by simp [hσ1, hz 20 (by simp)]) (by simp [hσ1, hIDX, hB0]; omega)
  rw [show σ1.val (V 2) + σ1.val (V 18) = t0 by simp [hσ1, hIDX, hB0]] at h2
  set σ2 := σ1.setv (V 2) t0 with hσ2
  have hfr2 : SameExcept σ σ2 [U 5] [V 2] :=
    (hfr1.comp' (sameExcept_setv σ1 (S := []) (Rg := [V 2]) (by simp) _)).weaken (by simp) (by simp)
  have hpre2 : SPre U V Wd M N m fl coef σ2 := by
    refine sPre_frame U V hpre (hfr2.weaken (by unfold sStreams; simp) (by unfold sRegs; simp))
      (by simp [hσ2, hσ1, emb_eq_iff, hpre.wh]) (by simp [hσ2, hσ1, emb_eq_iff, hpre.wl]) ?_
    intro k hk
    by_cases k5 : k = 5
    · subst k5; exact ⟨0, BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ hb0.2) _ _⟩
    · obtain ⟨v, hv⟩ := hpre.words k hk; exact ⟨v, hfr2.numOn (by simp [emb_eq_iff, k5]) hv⟩
  let Inv : ℕ → WState ns nr → Prop := fun k ρ =>
    SPre U V Wd M N m fl coef ρ ∧ NumOn ρ (U 5) (Wd + 1) (absSum fl t0 k) ∧ ρ.val (V 2) = t0 + k ∧
      SameExcept σ ρ [U 1, U 5, U 6] [V 2, V 11, V 12]
  have hInv : ∀ k ρ (j : Fin 25), j = 11 ∨ j = 12 → ∀ v, Inv k ρ → Inv k (ρ.setv (V j) v) := by
    rintro k ρ j hj v ⟨a1, a2, a3, a4⟩
    have hs : SameExcept ρ (ρ.setv (V j) v) [] [V j] := sameExcept_setv ρ (by simp) v
    have h2j : (2 : Fin 25) ≠ j := by rcases hj with rfl | rfl <;> decide
    refine ⟨sPre_frame U V a1 (hs.weaken (by simp) (by unfold sRegs; rcases hj with rfl | rfl <;> simp))
      (by simpa using a1.wh) (by simpa using a1.wl) (fun k hk => (a1.words k hk).elim fun x hx =>
        ⟨x, BinW.numOn_setv hx _ _⟩), BinW.numOn_setv a2 _ _, ?_, a4.trans (sameExcept_setv ρ (by
          rcases hj with rfl | rfl <;> simp) v)⟩
    rw [WState.setv_val, Function.update_of_ne (hner h2j)]; exact a3
  have hrep := Runs.rep (cap := cap) (K := V 11) (K2 := V 12) (body := sumBody U V) (hner (by decide))
    (sumBodyCost Wd fl.length) M Inv (by omega) (fun k ρ v hI => hInv k ρ 11 (Or.inl rfl) v hI)
    (fun k ρ v hI => hInv k ρ 12 (Or.inr rfl) v hI) ?_ σ2
    ⟨hpre2, ⟨by simp [hσ2, hσ1, absSum], by simp [hσ2, hσ1, emb_eq_iff, hb0.2]⟩, by simp [hσ2],
      hfr2.weaken (by simp) (by simp)⟩
    (by rw [hfr2.val (by simp [emb_eq_iff])]; exact hMC) (by rw [hfr2.val (by simp [emb_eq_iff])]; exact hMC2)
  · have hS1 : absSum fl t0 M + 1 < 2 ^ (Wd + 1) := by omega
    refine (Runs.seqE h1 (Runs.seqE h2 (Runs.seq (c2 := 3 * (t0 + M) + 1 + 1 + (41 * (Wd + 1) + 7 + 1 +
      (41 * (Wd + 1) + 8))) hrep fun ρ hρ => ?_))).cost (by unfold baseCost; rw [hσ1]; simp [hB0])
    obtain ⟨⟨a1, a2, a3, a4⟩, a5, a6⟩ := hρ
    have hc := wclear_spec (cap := cap) (V 2) (t0 + M) ρ a3 (by omega)
    set ρ1 := ρ.setv (V 2) 0 with hρ1
    have hi := BinW.inc_spec (A := U 5) (B := U 12) (F := V 8) (R := V 9) cap (Wd + 1) (hne (by decide))
      (hner (by decide)) ρ1 (absSum fl t0 M) 0 (BinW.numOn_setv a2 _ _) (BinW.numOn_setv a1.zr _ _)
      (by simp [hρ1, a1.zero 8 (by simp)]) (by simp [hρ1, a1.zero 9 (by simp)]) hS1 hcX
    set ρ2 := ρ1.sets (U 5) (frame (binary (Wd + 1) (absSum fl t0 M + 1))) with hρ2
    have hsh := BinW.shl_spec (A := U 5) (B := U 12) (F := V 8) (R := V 9) cap (Wd + 1) (hne (by decide))
      (hner (by decide)) ρ2 (absSum fl t0 M + 1) 0 (BinW.numOn_sets_self _ _ _ _ (by simp [hρ1, a2.2]))
      (BinW.numOn_sets_ne (BinW.numOn_setv a1.zr _ _) (hne (by decide)) _)
      (by simp [hρ2, hρ1, a1.zero 8 (by simp)]) (by simp [hρ2, hρ1, a1.zero 9 (by simp)]) hcX
    have hfin : SameExcept σ (ρ2.sets (U 5) (frame (binary (Wd + 1) (2 * (absSum fl t0 M + 1))))) [U 1, U 5, U 6] [] := by
      refine ⟨fun x hx => ?_, fun r _ => ?_, by simp [hρ2, hρ1, a4.cell]⟩
      · have := a4.1 x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [hρ2, hρ1, Function.update_of_ne hx.2.1, this.1, this.2]
      · simp only [hρ2, hρ1, WState.sets_val, WState.setv_val, Function.update_apply]
        split_ifs with h
        · rw [h, hIDX]
        · by_cases r11 : r = V 11
          · rw [r11, a5, hMC]
          · by_cases r12 : r = V 12
            · rw [r12, a6, hMC2]
            · exact a4.2.1 r (by simp [h, r11, r12])
    refine Runs.of (WXExec.seq (WXExec.wm hc) (WXExec.seq hi hsh)) ⟨?_, ?_, ?_, hfin⟩
    · refine sPre_frame U V hpre (hfin.weaken (by unfold sStreams; simp) (by simp)) ?_ ?_ ?_
      · simp [hρ2, hρ1, emb_eq_iff, a1.wh]
      · simp [hρ2, hρ1, emb_eq_iff, a1.wl]
      · intro k hk
        by_cases k5 : k = 5
        · subst k5; exact ⟨_, BinW.numOn_sets_self _ _ _ _ (by simp [hρ2, hρ1, a2.2])⟩
        · obtain ⟨v, hv⟩ := a1.words k hk
          exact ⟨v, BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_setv hv _ _) (hne k5) _) (hne k5) _⟩
    · rw [encS_natCast]
      exact BinW.numOn_sets_self _ _ _ _ (by simp [hρ2, hρ1, a2.2])
    · simp [hρ2, hρ1]
  · intro k hk ρ ⟨a1, a2, a3, a4⟩
    have hik : t0 + k < fl.length := by omega
    have hget : fl.getD (t0 + k) 0 = fl[t0 + k] := List.getD_eq_getElem _ _ hik
    have hmono := absSum_mono fl t0 (k + 1) M (by omega)
    rw [absSum_succ, hget] at hmono
    have hb := sumBody_spec U V cap Wd M N m fl coef ρ (t0 + k) (absSum fl t0 k) hik a1 a3 a2 hfl (by omega)
      (by omega)
    refine hb.post fun τ ⟨b1, b2, b3, b4⟩ => ⟨⟨b1, ?_, by rw [b3]; ring, a4.trans (b4.weaken (by simp) (by simp))⟩,
      b4.val (by simp [emb_eq_iff]), b4.val (by simp [emb_eq_iff])⟩
    rw [absSum_succ, hget]; exact b2

/-- One child of the forward scan at field `j`: `FLD := TP[IDX]·PW`, `ACC += FLD`, `PW := PW·BASE`,
`IDX += N`. -/
def fieldBody : WMX ns nr :=
  .seq (getAt (U 0) (U 1) (V 0) (V 1) (V 2) (V 3))
  (.seq (BinW.copy (U 6) (U 1) (V 8) (V 9))
  (.seq (SInt.smul (U 6) (U 4) (U 7) (U 8) (U 9) (U 10) (V 6) (V 7) (V 8) (V 9) (V 10))
  (.seq (SInt.sadd (U 3) (U 6) (U 7) (U 8) (V 6) (V 7) (V 8) (V 9))
  (.seq (SInt.smul (U 4) (U 5) (U 7) (U 8) (U 9) (U 10) (V 6) (V 7) (V 8) (V 9) (V 10))
  (addR (V 15) (V 2) (V 20))))))

def fieldBodyCost (Wd n N : ℕ) : ℕ :=
  (n + 1) * (40 * (Wd + 1) + 40) + 10 * (n + 1) * (2 * (Wd + 1) + 1) + 10 + 1 + (41 * (Wd + 1) + 3 + 1 +
    (SInt.smulCost Wd + 1 + (410 * Wd + 600 + 1 + (SInt.smulCost Wd + 1 + (18 * N + 3)))))

theorem fieldBody_spec (cap Wd M N m : ℕ) (fl : List ℕ) (coef : ℤ) (ρ : WState ns nr) (i : ℕ) (f acc pw b : ℤ)
    (hi : i < fl.length) (hfi : fl[i] = encS f) (hf : f.natAbs < 2 ^ Wd) (hpre : SPre U V Wd M N m fl coef ρ)
    (hIDX : ρ.val (V 2) = i) (hACC : SNumOn ρ (U 3) Wd acc) (hPW : SNumOn ρ (U 4) Wd pw)
    (hB : SNumOn ρ (U 5) Wd b) (h1 : (f * pw).natAbs < 2 ^ Wd) (h2 : (acc + f * pw).natAbs < 2 ^ Wd)
    (h3 : (pw * b).natAbs < 2 ^ Wd)
    (hcap : (fl.length + 1) * (2 * (Wd + 1) + 1) + 2 * fl.length ≤ cap) (hcapI : i + N ≤ cap) :
    Runs cap (fieldBody U V) ρ (fieldBodyCost Wd fl.length N) (fun τ =>
      SPre U V Wd M N m fl coef τ ∧ SNumOn τ (U 3) Wd (acc + f * pw) ∧ SNumOn τ (U 4) Wd (pw * b) ∧
        SNumOn τ (U 5) Wd b ∧ τ.val (V 2) = i + N ∧
        SameExcept ρ τ [U 1, U 3, U 4, U 6, U 7, U 8, U 9, U 10] [V 2]) := by
  have hne : ∀ {a b : Fin 14}, a ≠ b → U a ≠ U b := fun h => emb_ne U h
  have hner : ∀ {a b : Fin 25}, a ≠ b → V a ≠ V b := fun h => emb_ne V h
  have hz := hpre.zero
  have hcX : 2 * (Wd + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (Wd + 1) + 1) (show 0 < fl.length + 1 by omega); omega
  obtain ⟨junk, hj⟩ := hpre.tp
  have g1 := getAt_spec cap (A := U 0) (Wk := U 1) (CA := V 0) (CW := V 1) (N := V 2) (K2 := V 3) (hne (by decide))
    (by simp [emb_eq_iff]) (Wd + 1) (by omega) fl i hi ρ junk hj hpre.tph (hz 0 (by simp)) hpre.wh hpre.wl
    (hz 1 (by simp)) hIDX (hz 3 (by simp)) (by omega)
  rw [hfi] at g1
  set ρ1 := ρ.sets (U 1) (frame (binary (Wd + 1) (encS f))) with hρ1
  have hfr1 : SameExcept ρ ρ1 [U 1] [] := sameExcept_sets ρ (by simp) _
  obtain ⟨f0, hf0⟩ := hpre.words 6 (by simp)
  have g2 := BinW.copy_spec (A := U 6) (B := U 1) (F := V 8) (R := V 9) cap (Wd + 1) (hne (by decide))
    (hner (by decide)) ρ1 f0 (encS f) (hfr1.numOn (by simp [emb_eq_iff]) hf0)
    (BinW.numOn_sets_self _ _ _ _ hpre.wh) (by simp [hρ1, hz 8 (by simp)]) (by simp [hρ1, hz 9 (by simp)]) hcX
  set ρ2 := ρ1.sets (U 6) (frame (binary (Wd + 1) (encS f))) with hρ2
  have hfr2 : SameExcept ρ ρ2 [U 1, U 6] [] :=
    (hfr1.comp' (sameExcept_sets ρ1 (S := [U 6]) (Rg := []) (by simp) _)).weaken (by simp) (by simp)
  have hv2 : ∀ k : Fin 25, ρ2.val (V k) = ρ.val (V k) := fun k => hfr2.val (by simp)
  obtain ⟨a7, ha7⟩ := hpre.words 7 (by simp)
  obtain ⟨a8, ha8⟩ := hpre.words 8 (by simp)
  obtain ⟨a9, ha9⟩ := hpre.words 9 (by simp)
  obtain ⟨a10, ha10⟩ := hpre.words 10 (by simp)
  have g3 := SInt.smul_spec cap Wd (X := U 6) (Y := U 4) (M := U 7) (N := U 8) (C := U 9) (D := U 10) (S := V 6)
    (T := V 7) (F := V 8) (R := V 9) (G := V 10) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) ρ2 f pw a7 a8 a9 a10
    ⟨BinW.numOn_sets_self _ _ _ _ (by simp [hρ1, emb_eq_iff, hf0.2]), hf⟩ (SInt.SameExcept.sNumOn hfr2
      (by simp [emb_eq_iff]) hPW) (hfr2.numOn (by simp [emb_eq_iff]) ha7) (hfr2.numOn (by simp [emb_eq_iff]) ha8)
    (hfr2.numOn (by simp [emb_eq_iff]) ha9) (hfr2.numOn (by simp [emb_eq_iff]) ha10)
    (by rw [hv2]; exact hz 6 (by simp)) (by rw [hv2]; exact hz 7 (by simp)) (by rw [hv2]; exact hz 8 (by simp))
    (by rw [hv2]; exact hz 9 (by simp)) (by rw [hv2]; exact hz 10 (by simp)) h1 (by omega)
  have cc1 := Nat.mul_le_mul_right (40 * (Wd + 1) + 40) (show i + 1 ≤ fl.length + 1 by omega)
  have cc2 := Nat.mul_le_mul_right (2 * (Wd + 1) + 1) (Nat.mul_le_mul_left 10 (show i + 1 ≤ fl.length + 1 by omega))
  refine (Runs.seqE g1 (Runs.seqE g2 (Runs.seq (c2 := 410 * Wd + 600 + 1 + (SInt.smulCost Wd + 1 + (18 * N + 3)))
    g3 fun ρ3 hρ3 => ?_))).cost (by unfold fieldBodyCost; omega)
  obtain ⟨c1, ⟨m1, hm1⟩, ⟨n1, hn1⟩, ⟨cc, hcc⟩, ⟨dd, hdd⟩, c6⟩ := hρ3
  have hfr3 : SameExcept ρ ρ3 [U 1, U 6, U 7, U 8, U 9, U 10] [] := by
    refine (hfr2.comp' c6).weaken ?_ (by simp)
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto
  have g4 := SInt.sadd_spec cap Wd (X := U 3) (Y := U 6) (M := U 7) (N := U 8) (S := V 6) (T := V 7) (F := V 8)
    (R := V 9) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) ρ3 acc (f * pw) m1 n1
    (SInt.SameExcept.sNumOn hfr3 (by simp [emb_eq_iff]) hACC) c1 hm1 hn1
    (by rw [hfr3.val (by simp)]; exact hz 6 (by simp)) (by rw [hfr3.val (by simp)]; exact hz 7 (by simp))
    (by rw [hfr3.val (by simp)]; exact hz 8 (by simp)) (by rw [hfr3.val (by simp)]; exact hz 9 (by simp)) h2
    (by omega)
  refine Runs.seq (c2 := SInt.smulCost Wd + 1 + (18 * N + 3)) g4 fun ρ4 hρ4 => ?_
  obtain ⟨d1, ⟨m2, hm2⟩, ⟨n2, hn2⟩, d4⟩ := hρ4
  have hfr4 : SameExcept ρ ρ4 [U 1, U 3, U 6, U 7, U 8, U 9, U 10] [] := by
    refine (hfr3.comp' d4).weaken ?_ (by simp)
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    tauto
  have g5 := SInt.smul_spec cap Wd (X := U 4) (Y := U 5) (M := U 7) (N := U 8) (C := U 9) (D := U 10) (S := V 6)
    (T := V 7) (F := V 8) (R := V 9) (G := V 10) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) ρ4 pw b m2 n2 cc dd
    (SInt.SameExcept.sNumOn hfr4 (by simp [emb_eq_iff]) hPW) (SInt.SameExcept.sNumOn hfr4 (by simp [emb_eq_iff]) hB)
    hm2 hn2 (d4.numOn (by simp [emb_eq_iff]) hcc) (d4.numOn (by simp [emb_eq_iff]) hdd)
    (by rw [hfr4.val (by simp)]; exact hz 6 (by simp)) (by rw [hfr4.val (by simp)]; exact hz 7 (by simp))
    (by rw [hfr4.val (by simp)]; exact hz 8 (by simp)) (by rw [hfr4.val (by simp)]; exact hz 9 (by simp))
    (by rw [hfr4.val (by simp)]; exact hz 10 (by simp)) h3 (by omega)
  refine Runs.seq (c2 := 18 * N + 3) g5 fun ρ5 hρ5 => ?_
  obtain ⟨e1, ⟨m3, hm3⟩, ⟨n3, hn3⟩, ⟨c3, hc3⟩, ⟨d3, hd3⟩, e6⟩ := hρ5
  have hfr5 : SameExcept ρ ρ5 [U 1, U 3, U 4, U 6, U 7, U 8, U 9, U 10] [] := by
    refine (hfr4.comp' e6).weaken ?_ (by simp)
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (h | h | h | h | h | h | h) | (h | h | h | h | h) <;> simp [h]
  have hv5 : ∀ k : Fin 25, ρ5.val (V k) = ρ.val (V k) := fun k => hfr5.val (by simp)
  have g6 := addR_spec cap (A := V 15) (B := V 2) (T := V 20) (hner (by decide)) (hner (by decide))
    (hner (by decide)) ρ5 (by rw [hv5]; exact hz 20 (by simp)) (by rw [hv5, hv5, hIDX, hpre.js]; omega)
  rw [hv5 15, hpre.js] at g6
  have hfr6 : SameExcept ρ (ρ5.setv (V 2) (ρ5.val (V 2) + N)) [U 1, U 3, U 4, U 6, U 7, U 8, U 9, U 10] [V 2] :=
    (hfr5.comp' (sameExcept_setv ρ5 (S := []) (Rg := [V 2]) (by simp) _)).weaken (by simp) (by simp)
  have hU6 : SNumOn ρ5 (U 6) Wd (f * pw) :=
    SInt.SameExcept.sNumOn e6 (by simp [emb_eq_iff]) (SInt.SameExcept.sNumOn d4 (by simp [emb_eq_iff]) c1)
  refine Runs.of g6 ⟨?_, ?_, ?_, ?_, ?_, hfr6⟩
  · refine sPre_frame U V hpre (hfr6.weaken (by unfold sStreams; simp) (by unfold sRegs; simp)) ?_ ?_ ?_
    · rw [WState.setv_sh, e6.sh (x := U 1) (by simp [emb_eq_iff]), d4.sh (x := U 1) (by simp [emb_eq_iff]),
        c6.sh (x := U 1) (by simp [emb_eq_iff])]; simp [hρ2, hρ1, emb_eq_iff, hpre.wh]
    · rw [WState.setv_st, e6.st (x := U 1) (by simp [emb_eq_iff]), d4.st (x := U 1) (by simp [emb_eq_iff]),
        c6.st (x := U 1) (by simp [emb_eq_iff])]; simp [hρ2, hρ1, emb_eq_iff, frame_length]
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, BinW.numOn_setv (SInt.SameExcept.sNumOn e6 (by simp [emb_eq_iff]) d1).1 _ _⟩
      · exact ⟨_, BinW.numOn_setv e1.1 _ _⟩
      · exact ⟨_, BinW.numOn_setv (hfr5.numOn (by simp [emb_eq_iff]) hB.1) _ _⟩
      · exact ⟨_, BinW.numOn_setv hU6.1 _ _⟩
      · exact ⟨_, BinW.numOn_setv hm3 _ _⟩
      · exact ⟨_, BinW.numOn_setv hn3 _ _⟩
      · exact ⟨_, BinW.numOn_setv hc3 _ _⟩
      · exact ⟨_, BinW.numOn_setv hd3 _ _⟩
  · exact ⟨BinW.numOn_setv (SInt.SameExcept.sNumOn e6 (by simp [emb_eq_iff]) d1).1 _ _, h2⟩
  · exact ⟨BinW.numOn_setv e1.1 _ _, h3⟩
  · exact ⟨BinW.numOn_setv (hfr5.numOn (by simp [emb_eq_iff]) hB.1) _ _, hB.2⟩
  · simp [hv5, hIDX]

/-- One stacked field: `ACC := 0`, `PW := 1`, the forward scan over the `m` children, append `ACC`, `JB += 1`. -/
def oneField : WMX ns nr :=
  .seq (BinW.copy (U 3) (U 12) (V 8) (V 9))
  (.seq (BinW.copy (U 4) (U 13) (V 8) (V 9))
  (.seq (addR (V 19) (V 2) (V 20))
  (.seq (repK (V 16) (V 17) (fieldBody U V))
  (.seq (.wm (WM.clear (V 2)))
  (.seq (appendRecX (U 3) (U 2) (V 4) (V 5)) (WMX.inc (V 19)))))))

def oneFieldCost (Wd n N m p : ℕ) : ℕ :=
  41 * (Wd + 1) + 3 + 1 + (41 * (Wd + 1) + 3 + 1 + (18 * p + 3 + 1 + (m * (fieldBodyCost Wd n N + 8) + 7 * m + 3 + 1 +
    (3 * (p + m * N) + 1 + 1 + (40 * (Wd + 1) + 11 + 1 + 3)))))

/-- The tuple's entries as the stacking machine reads them: entry `t₀ + c·N + j` is `encS` of field `j` of child
`c`. -/
def TupleAt (fl : List ℕ) (t0 N : ℕ) (ls : List (List ℤ)) : Prop :=
  ∀ c < ls.length, ∀ j < N, t0 + c * N + j < fl.length ∧ ∀ (h : t0 + c * N + j < fl.length),
    fl[t0 + c * N + j] = encS ((ls.getD c []).getD j 0)

theorem oneField_spec (cap Wd M N m : ℕ) (fl : List ℕ) (coef : ℤ) (σ : WState ns nr) (t0 j : ℕ)
    (ls : List (List ℤ)) (b : ℕ) (out L0 : List Bool) (hm : ls.length = m) (hj : j < N) (hat : TupleAt fl t0 N ls)
    (hb1 : 1 ≤ b) (hfb : ∀ c < m, ((ls.getD c []).getD j 0).natAbs ≤ b - 1) (hbm : b ^ m < 2 ^ Wd)
    (hpre : SPre U V Wd M N m fl coef σ) (hIDX : σ.val (V 2) = 0) (hJB : σ.val (V 19) = t0 + j)
    (hCM : σ.val (V 16) = m) (hCM2 : σ.val (V 17) = 0) (hB : SNumOn σ (U 5) Wd (b : ℤ))
    (hO : OutOn σ (U 2) (V 5) out L0) (hWd : 1 ≤ Wd)
    (hcap : (fl.length + 1) * (2 * (Wd + 1) + 1) + 2 * fl.length + 2 * m + t0 + j + m * N + N ≤ cap)
    (hcapO : out.length + 2 * (Wd + 1) + 2 ≤ cap) :
    Runs cap (oneField U V) σ (oneFieldCost Wd fl.length N m (t0 + j)) (fun τ =>
      SPre U V Wd M N m fl coef τ ∧ OutOn τ (U 2) (V 5) (out ++ fieldRec (Wd + 1) (fsum b ls j m)) L0 ∧
        τ.val (V 2) = 0 ∧ τ.val (V 19) = t0 + j + 1 ∧ τ.val (V 16) = m ∧ τ.val (V 17) = 0 ∧
        SNumOn τ (U 5) Wd (b : ℤ) ∧ SameExcept σ τ (sStreams U) [V 5, V 19]) := by
  have hne : ∀ {a b : Fin 14}, a ≠ b → U a ≠ U b := fun h => emb_ne U h
  have hner : ∀ {a b : Fin 25}, a ≠ b → V a ≠ V b := fun h => emb_ne V h
  have hz := hpre.zero
  have hcX : 2 * (Wd + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (Wd + 1) + 1) (show 0 < fl.length + 1 by omega); omega
  have hbm' : ∀ c ≤ m, b ^ c < 2 ^ Wd := fun c hc =>
    lt_of_le_of_lt (Nat.pow_le_pow_right hb1 hc) hbm
  obtain ⟨a0, ha0⟩ := hpre.words 3 (by simp)
  obtain ⟨p0, hp0⟩ := hpre.words 4 (by simp)
  have g1 := BinW.copy_spec (A := U 3) (B := U 12) (F := V 8) (R := V 9) cap (Wd + 1) (hne (by decide))
    (hner (by decide)) σ a0 0 ha0 hpre.zr (hz 8 (by simp)) (hz 9 (by simp)) hcX
  set σ1 := σ.sets (U 3) (frame (binary (Wd + 1) 0)) with hσ1
  have g2 := BinW.copy_spec (A := U 4) (B := U 13) (F := V 8) (R := V 9) cap (Wd + 1) (hne (by decide))
    (hner (by decide)) σ1 p0 2 (BinW.numOn_sets_ne hp0 (hne (by decide)) _)
    (BinW.numOn_sets_ne hpre.two (hne (by decide)) _) (by simp [hσ1, hz 8 (by simp)])
    (by simp [hσ1, hz 9 (by simp)]) hcX
  set σ2 := σ1.sets (U 4) (frame (binary (Wd + 1) 2)) with hσ2
  have g3 := addR_spec cap (A := V 19) (B := V 2) (T := V 20) (hner (by decide)) (hner (by decide))
    (hner (by decide)) σ2 (by simp [hσ2, hσ1, hz 20 (by simp)]) (by simp [hσ2, hσ1, hIDX, hJB]; omega)
  rw [show σ2.val (V 2) + σ2.val (V 19) = t0 + j by simp [hσ2, hσ1, hIDX, hJB]] at g3
  set σ3 := σ2.setv (V 2) (t0 + j) with hσ3
  have hfr3 : SameExcept σ σ3 [U 3, U 4] [V 2] := by
    refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hσ3, hσ2, hσ1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [hσ3, hσ2, hσ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [hσ3, hσ2, hσ1, Function.update_of_ne hr]
  have hpre3 : SPre U V Wd M N m fl coef σ3 := by
    refine sPre_frame U V hpre (hfr3.weaken (by unfold sStreams; simp) (by unfold sRegs; simp))
      (by simp [hσ3, hσ2, hσ1, emb_eq_iff, hpre.wh]) (by simp [hσ3, hσ2, hσ1, emb_eq_iff, hpre.wl]) ?_
    intro k hk
    by_cases k3 : k = 3
    · subst k3; exact ⟨0, by simp [hσ3, hσ2, hσ1, emb_eq_iff], by simp [hσ3, hσ2, hσ1, emb_eq_iff, ha0.2]⟩
    · by_cases k4 : k = 4
      · subst k4; exact ⟨2, by simp [hσ3, hσ2, hσ1, emb_eq_iff], by simp [hσ3, hσ2, hσ1, emb_eq_iff, hp0.2]⟩
      · obtain ⟨v, hv⟩ := hpre.words k hk; exact ⟨v, hfr3.numOn (by simp [emb_eq_iff, k3, k4]) hv⟩
  let Inv : ℕ → WState ns nr → Prop := fun c ρ =>
    SPre U V Wd M N m fl coef ρ ∧ SNumOn ρ (U 3) Wd (fsum (b : ℤ) ls j c) ∧ SNumOn ρ (U 4) Wd ((b : ℤ) ^ c) ∧
      SNumOn ρ (U 5) Wd (b : ℤ) ∧ ρ.val (V 2) = t0 + j + c * N ∧
      SameExcept σ3 ρ [U 1, U 3, U 4, U 6, U 7, U 8, U 9, U 10] [V 2, V 16, V 17]
  have hInv : ∀ c ρ (k : Fin 25), k = 16 ∨ k = 17 → ∀ v, Inv c ρ → Inv c (ρ.setv (V k) v) := by
    rintro c ρ k hk v ⟨a1, a2, a3, a4, a5, a6⟩
    have hs : SameExcept ρ (ρ.setv (V k) v) [] [V k] := sameExcept_setv ρ (by simp) v
    have h2k : (2 : Fin 25) ≠ k := by rcases hk with rfl | rfl <;> decide
    refine ⟨sPre_frame U V a1 (hs.weaken (by simp) (by unfold sRegs; rcases hk with rfl | rfl <;> simp))
      (by simpa using a1.wh) (by simpa using a1.wl) (fun k hk => (a1.words k hk).elim fun x hx =>
        ⟨x, BinW.numOn_setv hx _ _⟩), ⟨BinW.numOn_setv a2.1 _ _, a2.2⟩, ⟨BinW.numOn_setv a3.1 _ _, a3.2⟩,
      ⟨BinW.numOn_setv a4.1 _ _, a4.2⟩, ?_, a6.trans (sameExcept_setv ρ (by rcases hk with rfl | rfl <;> simp) v)⟩
    rw [WState.setv_val, Function.update_of_ne (hner h2k)]; exact a5
  have hA0 : SNumOn σ3 (U 3) Wd (fsum (b : ℤ) ls j 0) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [hσ3, hσ2, hσ1, emb_eq_iff, fsum, encS]
    · simp [hσ3, hσ2, hσ1, emb_eq_iff, ha0.2]
    · simp [fsum]
  have hP0 : SNumOn σ3 (U 4) Wd ((b : ℤ) ^ 0) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [hσ3, hσ2, hσ1, emb_eq_iff, encS]
    · simp [hσ3, hσ2, hσ1, emb_eq_iff, hp0.2]
    · have h2 : 2 ^ 1 ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) hWd
      simp; omega
  have hrep := Runs.rep (cap := cap) (K := V 16) (K2 := V 17) (body := fieldBody U V) (hner (by decide))
    (fieldBodyCost Wd fl.length N) m Inv (by omega) (fun c ρ v hI => hInv c ρ 16 (Or.inl rfl) v hI)
    (fun c ρ v hI => hInv c ρ 17 (Or.inr rfl) v hI) ?_ σ3
    ⟨hpre3, hA0, hP0, ⟨hfr3.numOn (by simp [emb_eq_iff]) hB.1, hB.2⟩, by simp [hσ3], SameExcept.refl _ _ _⟩
    (by rw [hfr3.val (by simp [emb_eq_iff])]; exact hCM) (by rw [hfr3.val (by simp [emb_eq_iff])]; exact hCM2)
  · have hO3 : OutOn σ3 (U 2) (V 5) out L0 := outOn_frame hO hfr3 (by simp [emb_eq_iff]) (by simp [emb_eq_iff])
    refine (Runs.seqE g1 (Runs.seqE g2 (Runs.seqE g3 (Runs.seq (c2 := 3 * (t0 + j + m * N) + 1 + 1 +
      (40 * (Wd + 1) + 11 + 1 + 3)) hrep fun ρ hρ => ?_)))).cost (by unfold oneFieldCost; simp [hσ1, hσ2, hJB]; try omega)
    obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, a7, a8⟩ := hρ
    have hc := wclear_spec (cap := cap) (V 2) (t0 + j + m * N) ρ a5 (by omega)
    set ρ1 := ρ.setv (V 2) 0 with hρ1
    have hO1 : OutOn ρ1 (U 2) (V 5) out L0 :=
      outOn_frame hO3 (a6.trans (sameExcept_setv ρ (S := [U 1, U 3, U 4, U 6, U 7, U 8, U 9, U 10])
        (Rg := [V 2, V 16, V 17]) (by simp) 0)) (by simp [emb_eq_iff]) (by simp [emb_eq_iff])
    have ha := appendRec_spec cap (Src := U 3) (O := U 2) (CS := V 4) (CO := V 5) (hne (by decide))
      (hner (by decide)) ρ1 (binary (Wd + 1) (encS (fsum (b : ℤ) ls j m))) [] out L0
      (by simp [hρ1, a2.1.1, BinW.frame_frameP]) (by simp [hρ1, a2.1.2]) (by simp [hρ1, a1.zero 4 (by simp)]) hO1
      (by rw [binary_length]; omega)
    rw [binary_length] at ha
    set ρ2 := ((ρ1.sets (U 2) (overlay (out ++ frame (binary (Wd + 1) (encS (fsum (b : ℤ) ls j m)))) L0)).seth (U 2)
      (out ++ frame (binary (Wd + 1) (encS (fsum (b : ℤ) ls j m)))).length).setv (V 5)
      (out ++ frame (binary (Wd + 1) (encS (fsum (b : ℤ) ls j m)))).length with hρ2
    have e19 : ρ2.val (V 19) = t0 + j := by
      simp [hρ2, hρ1]; rw [a6.val (by simp [emb_eq_iff]), hfr3.val (by simp [emb_eq_iff]), hJB]
    have hi := WXExec.inc cap (V 19) ρ2 (by rw [e19]; omega)
    have hfr12 : SameExcept ρ (ρ2.setv (V 19) (ρ2.val (V 19) + 1)) [U 2] [V 2, V 5, V 19] := by
      refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ2, hρ1]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp [hρ2, hρ1, Function.update_of_ne hx]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hρ2, hρ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2]
    have hfrall : SameExcept σ (ρ2.setv (V 19) (ρ2.val (V 19) + 1)) (sStreams U) [V 5, V 19] := by
      refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ2, hρ1, a6.cell, hfr3.cell]⟩
      · unfold sStreams at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hx
        have h1 := hfr12.1 x (by simp [n2])
        have h2 := a6.1 x (by simp [n1, n3, n4, n6, n7, n8, n9, n10])
        have h3 := hfr3.1 x (by simp [n3, n4])
        exact ⟨h1.1.trans (h2.1.trans h3.1), h1.2.trans (h2.2.trans h3.2)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        by_cases r2 : r = V 2
        · rw [r2]; simp [hρ2, hρ1, Function.update_of_ne (hner (show (2 : Fin 25) ≠ 19 by decide)),
            Function.update_of_ne (hner (show (2 : Fin 25) ≠ 5 by decide)), hIDX]
        · by_cases r16 : r = V 16
          · rw [r16]; simp [hρ2, hρ1, Function.update_of_ne (hner (show (16 : Fin 25) ≠ 19 by decide)),
              Function.update_of_ne (hner (show (16 : Fin 25) ≠ 5 by decide)),
              Function.update_of_ne (hner (show (16 : Fin 25) ≠ 2 by decide)), a7, hCM]
          · by_cases r17 : r = V 17
            · rw [r17]; simp [hρ2, hρ1, Function.update_of_ne (hner (show (17 : Fin 25) ≠ 19 by decide)),
                Function.update_of_ne (hner (show (17 : Fin 25) ≠ 5 by decide)),
                Function.update_of_ne (hner (show (17 : Fin 25) ≠ 2 by decide)), a8, hCM2]
            · rw [hfr12.val (by simp [r2, hr.1, hr.2]), a6.val (by simp [r2, r16, r17]), hfr3.val (by simp [r2])]
    refine Runs.of (WXExec.seq (WXExec.wm hc) (WXExec.seq (WXExec.wm ha) hi)) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hfrall⟩
    · refine sPre_frame U V a1 (hfr12.weaken (by unfold sStreams; simp) (by unfold sRegs; simp)) ?_ ?_ ?_
      · simp [hρ2, hρ1, emb_eq_iff, a1.wh]
      · simp [hρ2, hρ1, emb_eq_iff, a1.wl]
      · intro k hk
        obtain ⟨v, hv⟩ := a1.words k hk
        have hk2 : U k ∉ [U 2] := by
          simp only [List.mem_singleton, emb_eq_iff]
          rintro rfl; simp at hk
        exact ⟨v, hfr12.numOn hk2 hv⟩
    · refine ⟨by simp [hρ2, fieldRec], by simp [hρ2, fieldRec], by simp [hρ2, fieldRec]⟩
    · simp [hρ2, hρ1]
    · simp [e19]
    · simp [hρ2, hρ1, a7]
    · simp [hρ2, hρ1, a8]
    · exact SInt.SameExcept.sNumOn hfr12 (by simp [emb_eq_iff]) a4
  · intro c hc ρ ⟨a1, a2, a3, a4, a5, a6⟩
    have hcm : c < ls.length := by omega
    obtain ⟨hidx, hfi⟩ := hat c hcm j hj
    set f := (ls.getD c []).getD j 0 with hfdef
    have hfb' := hfb c hc
    have hm1 : 1 ≤ m := by omega
    have hbbm : b ≤ b ^ m := by
      calc b = b ^ 1 := (pow_one b).symm
        _ ≤ b ^ m := Nat.pow_le_pow_right hb1 hm1
    have hcm' : b ^ (c + 1) ≤ b ^ m := Nat.pow_le_pow_right hb1 hc
    have hpc : b ^ (c + 1) = b ^ c * (b - 1) + b ^ c := by
      rw [pow_succ, ← Nat.mul_succ]; congr 1; omega
    have hfs := fsum_bound b hb1 ls j (c + 1) (fun c' hc' => hfb c' (by omega))
    rw [fsum_succ, ← hfdef] at hfs
    have hfm : (f * (b : ℤ) ^ c).natAbs ≤ (b - 1) * b ^ c := by
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]; exact Nat.mul_le_mul_right _ hfb'
    have hidx' : t0 + j + c * N = t0 + c * N + j := by ring
    have hx := fieldBody_spec U V cap Wd M N m fl coef ρ (t0 + j + c * N) f (fsum (b : ℤ) ls j c) ((b : ℤ) ^ c)
      (b : ℤ) (by rw [hidx']; exact hidx) (by simp only [hidx']; exact hfi hidx) (by omega) a1 a5 a2 a3 a4
      (by have := Nat.mul_comm (b - 1) (b ^ c); omega)
      (by rw [mul_comm f]; omega)
      (by rw [← pow_succ, Int.natAbs_pow, Int.natAbs_natCast]; omega)
      (by omega) (by omega)
    refine hx.post fun τ ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨⟨b1, ?_, ?_, b4, ?_, a6.trans (b6.weaken (by simp) (by simp))⟩,
      b6.val (by simp [emb_eq_iff]), b6.val (by simp [emb_eq_iff])⟩
    · rw [fsum_succ, mul_comm ((b : ℤ) ^ c)]; exact b2
    · rw [pow_succ]; exact b3
    · rw [b5]; ring

theorem absSum_tuple (fl : List ℕ) (t0 N : ℕ) (ls : List (List ℤ)) (hN : 0 < N) (hl : ∀ l ∈ ls, l.length = N)
    (hat : TupleAt fl t0 N ls) : absSum fl t0 (ls.length * N) = magL ls := by
  rw [magL_flatten]
  have hfl : ls.flatten.length = ls.length * N := by
    have := flatten_take_length N ls ls.length hl le_rfl
    rwa [List.take_of_length_le le_rfl] at this
  unfold absSum
  rw [← hfl]
  have key : ∀ q < ls.flatten.length, fl.getD (t0 + q) 0 / 2 = (ls.flatten.getD q 0).natAbs := by
    intro q hq
    rw [hfl] at hq
    have hc : q / N < ls.length := by
      rw [Nat.div_lt_iff_lt_mul hN]; exact hq
    have hj : q % N < N := Nat.mod_lt _ hN
    have hq' : q = q / N * N + q % N := (Nat.div_add_mod' q N).symm
    obtain ⟨hidx, hfi⟩ := hat (q / N) hc (q % N) hj
    rw [show t0 + q = t0 + q / N * N + q % N by omega, List.getD_eq_getElem _ _ hidx, hfi hidx, SInt.encS_div,
      ← flat_get N ls hl _ _ hc hj, ← hq']
  have : ((List.range ls.flatten.length).map fun q => fl.getD (t0 + q) 0 / 2) =
      (List.range ls.flatten.length).map fun q => (ls.flatten.getD q 0).natAbs :=
    List.map_congr_left fun q hq => key q (List.mem_range.mp hq)
  rw [this]
  generalize ls.flatten = l
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.map_append, List.sum_append,
      List.map_append, List.sum_append]
    congr 1
    · rw [← ih]; apply congrArg List.sum; apply List.map_congr_left
      intro q hq; rw [List.getD_append _ _ _ _ (List.mem_range.mp hq)]
    · simp

def stackOne : WMX ns nr :=
  .seq (baseP U V)
  (.seq (addR (V 18) (V 19) (V 20))
  (.seq (repK (V 13) (V 14) (oneField U V))
  (.seq (.wm (WM.clear (V 19)))
  (.seq (appendRecX (U 11) (U 2) (V 4) (V 5))
  (.seq (addR (V 23) (V 18) (V 20)) (WMX.inc (V 24)))))))

end Stack

end NearCubicGates.Close.TabMachine
