import Proof.Gates.TabMachine.Stack

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

section Stack2
variable (U : Fin 14 ↪ Fin (ns + 1)) (V : Fin 25 ↪ Fin nr)

/-- The cut's records. -/
def cutRecs (Wd s : ℕ) (coef : ℤ) (ls : List (List ℤ)) : List Bool := (cutL s coef ls).flatMap (fieldRec (Wd + 1))

theorem cutRecs_eq (Wd s : ℕ) (coef : ℤ) (ls : List (List ℤ)) (h : ∀ l ∈ ls, l.length = s + 1) :
    cutRecs Wd s coef ls = ((List.range (s + 1)).map fun j => fsum ((magL ls + 1 : ℕ) : ℤ) ls j ls.length).flatMap
      (fieldRec (Wd + 1)) ++ fieldRec (Wd + 1) coef := by
  unfold cutRecs cutL
  rw [stackL_eq s _ ls h, List.flatMap_append]
  simp

def stackOneCost (Wd M N m n t0 : ℕ) : ℕ :=
  baseCost Wd M n t0 + 1 + (18 * t0 + 3 + 1 + (N * (oneFieldCost Wd n N m (t0 + N) + 8) + 7 * N + 3 + 1 +
    (3 * (t0 + N) + 1 + 1 + (40 * (Wd + 1) + 11 + 1 + (18 * M + 3 + 1 + 3)))))

theorem oneFieldCost_mono (Wd n N m p q : ℕ) (h : p ≤ q) : oneFieldCost Wd n N m p ≤ oneFieldCost Wd n N m q := by
  unfold oneFieldCost; omega

theorem getD_le_magL (ls : List (List ℤ)) (c j : ℕ) : ((ls.getD c []).getD j 0).natAbs ≤ magL ls := by
  unfold magL
  by_cases hc : c < ls.length
  · rw [List.getD_eq_getElem _ _ hc]
    by_cases hj : j < ls[c].length
    · rw [List.getD_eq_getElem _ _ hj]
      have h1 : ls[c][j].natAbs ≤ (ls[c].map Int.natAbs).sum :=
        List.le_sum_of_mem (List.mem_map.2 ⟨_, List.getElem_mem hj, rfl⟩)
      have h2 : (ls[c].map Int.natAbs).sum ≤ (ls.map fun l => (l.map Int.natAbs).sum).sum :=
        List.le_sum_of_mem (List.mem_map.2 ⟨_, List.getElem_mem hc, rfl⟩)
      omega
    · rw [List.getD_eq_default _ _ (show ls[c].length ≤ j by omega)]; simp
  · rw [List.getD_eq_default ls [] (show ls.length ≤ c by omega)]; simp

theorem stackOne_spec (cap Wd s m : ℕ) (fl : List ℕ) (coef : ℤ) (σ : WState ns nr) (t0 g : ℕ)
    (ls : List (List ℤ)) (out L0 : List Bool) (hm : ls.length = m) (hl : ∀ l ∈ ls, l.length = s + 1)
    (hat : TupleAt fl t0 (s + 1) ls) (hk : t0 + m * (s + 1) ≤ fl.length) (hfl : ∀ x ∈ fl, x < 2 ^ (Wd + 1))
    (hbound : (magL ls + 1) ^ (m + 1) < 2 ^ Wd) (hWd : 1 ≤ Wd)
    (hpre : SPre U V Wd (m * (s + 1)) (s + 1) m fl coef σ) (hIDX : σ.val (V 2) = 0) (hJB : σ.val (V 19) = 0)
    (hB0 : σ.val (V 18) = t0) (hMC : σ.val (V 11) = m * (s + 1)) (hMC2 : σ.val (V 12) = 0)
    (hJC : σ.val (V 13) = s + 1) (hJC2 : σ.val (V 14) = 0) (hCM : σ.val (V 16) = m) (hCM2 : σ.val (V 17) = 0)
    (hGC : σ.val (V 24) = g) (hO : OutOn σ (U 2) (V 5) out L0)
    (hcap : (fl.length + 1) * (2 * (Wd + 1) + 1) + 2 * fl.length + 2 * m + 2 * (m * (s + 1)) + t0 + 2 * (s + 1) +
      m * (s + 1) + g + 1 ≤ cap)
    (hcapO : out.length + (s + 2) * (2 * (Wd + 1) + 1) + 1 ≤ cap) :
    Runs cap (stackOne U V) σ (stackOneCost Wd (m * (s + 1)) (s + 1) m fl.length t0) (fun τ =>
      SPre U V Wd (m * (s + 1)) (s + 1) m fl coef τ ∧ OutOn τ (U 2) (V 5) (out ++ cutRecs Wd s coef ls) L0 ∧
        τ.val (V 2) = 0 ∧ τ.val (V 19) = 0 ∧ τ.val (V 18) = t0 + m * (s + 1) ∧ τ.val (V 11) = m * (s + 1) ∧
        τ.val (V 12) = 0 ∧ τ.val (V 13) = s + 1 ∧ τ.val (V 14) = 0 ∧ τ.val (V 16) = m ∧ τ.val (V 17) = 0 ∧
        τ.val (V 24) = g + 1 ∧ SameExcept σ τ (sStreams U) [V 5, V 18, V 24]) := by
  have hne : ∀ {a b : Fin 14}, a ≠ b → U a ≠ U b := fun h => emb_ne U h
  have hner : ∀ {a b : Fin 25}, a ≠ b → V a ≠ V b := fun h => emb_ne V h
  set b := magL ls + 1 with hbdef
  have hb1 : 1 ≤ b := by omega
  have hbb : b ≤ b ^ (m + 1) := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ (m + 1) := Nat.pow_le_pow_right hb1 (by omega)
  have hbm : b ^ m < 2 ^ Wd := lt_of_le_of_lt (Nat.pow_le_pow_right hb1 (by omega)) hbound
  have habs : absSum fl t0 (m * (s + 1)) = magL ls := by
    have := absSum_tuple fl t0 (s + 1) ls (by omega) hl hat
    rw [hm] at this; exact this
  -- (1) the base
  have h1 := baseP_spec U V cap Wd (m * (s + 1)) (s + 1) m fl coef σ t0 hk hpre hIDX hB0 hMC hMC2 hfl
    (by rw [habs, pow_succ]; omega) (by omega)
  rw [habs] at h1
  refine (Runs.seq (c2 := 18 * t0 + 3 + 1 + ((s + 1) * (oneFieldCost Wd fl.length (s + 1) m (t0 + (s + 1)) + 8) +
    7 * (s + 1) + 3 + 1 + (3 * (t0 + (s + 1)) + 1 + 1 + (40 * (Wd + 1) + 11 + 1 + (18 * (m * (s + 1)) + 3 + 1 +
    3))))) h1 fun σ1 hσ1 => ?_).cost (by unfold stackOneCost; omega)
  obtain ⟨a1, a2, a3, a4⟩ := hσ1
  have hv1 : ∀ k : Fin 25, σ1.val (V k) = σ.val (V k) := fun k => a4.val (by simp)
  -- (2) `JB := t₀`
  have h2 := addR_spec cap (A := V 18) (B := V 19) (T := V 20) (hner (by decide)) (hner (by decide))
    (hner (by decide)) σ1 (by rw [hv1]; exact hpre.zero 20 (by simp)) (by rw [hv1, hv1, hJB, hB0]; omega)
  rw [hv1, hv1, hJB, hB0, Nat.zero_add] at h2
  set σ2 := σ1.setv (V 19) t0 with hσ2
  have hfr2 : SameExcept σ1 σ2 [] [V 19] := sameExcept_setv σ1 (by simp) _
  have hv1' : ∀ r, σ1.val r = σ.val r := fun r => a4.val (by simp)
  have hpre2 : SPre U V Wd (m * (s + 1)) (s + 1) m fl coef σ2 :=
    sPre_frame U V a1 (hfr2.weaken (by simp) (by unfold sRegs; simp)) (by simp [hσ2, a1.wh]) (by simp [hσ2, a1.wl])
      (fun k hk => (a1.words k hk).elim fun x hx => ⟨x, BinW.numOn_setv hx _ _⟩)
  have hbW : (b : ℤ).natAbs < 2 ^ Wd := by simp; omega
  have hBs : SNumOn σ2 (U 5) Wd (b : ℤ) := ⟨BinW.numOn_setv a2 _ _, hbW⟩
  have hv2 : ∀ k : Fin 25, k ≠ 19 → σ2.val (V k) = σ.val (V k) := fun k hk => by
    rw [hσ2, WState.setv_val, Function.update_of_ne (hner hk), hv1]
  let F : ℕ → ℤ := fun j => fsum (b : ℤ) ls j m
  let Inv : ℕ → WState ns nr → Prop := fun j ρ =>
    SPre U V Wd (m * (s + 1)) (s + 1) m fl coef ρ ∧
      OutOn ρ (U 2) (V 5) (out ++ ((List.range j).map F).flatMap (fieldRec (Wd + 1))) L0 ∧ ρ.val (V 2) = 0 ∧
      ρ.val (V 19) = t0 + j ∧ ρ.val (V 16) = m ∧ ρ.val (V 17) = 0 ∧ SNumOn ρ (U 5) Wd (b : ℤ) ∧
      SameExcept σ2 ρ (sStreams U) [V 5, V 19, V 13, V 14]
  have hInv : ∀ j ρ (k : Fin 25), k = 13 ∨ k = 14 → ∀ v, Inv j ρ → Inv j (ρ.setv (V k) v) := by
    rintro j ρ k hk v ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩
    have hs : SameExcept ρ (ρ.setv (V k) v) [] [V k] := sameExcept_setv ρ (by simp) v
    have hn : ∀ i : Fin 25, i ∈ [(2 : Fin 25), 5, 19, 16, 17] → i ≠ k := by
      intro i hi; rcases hk with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨sPre_frame U V c1 (hs.weaken (by simp) (by unfold sRegs; rcases hk with rfl | rfl <;> simp))
      (by simpa using c1.wh) (by simpa using c1.wl) (fun k hk => (c1.words k hk).elim fun x hx =>
        ⟨x, BinW.numOn_setv hx _ _⟩), outOn_frame c2 hs (by simp) (by simp [emb_eq_iff, hn 5 (by simp)]), ?_, ?_,
      ?_, ?_, ⟨BinW.numOn_setv c7.1 _ _, c7.2⟩, c8.trans (sameExcept_setv ρ (by rcases hk with rfl | rfl <;> simp) v)⟩
    · rw [WState.setv_val, Function.update_of_ne (hner (hn 2 (by simp)))]; exact c3
    · rw [WState.setv_val, Function.update_of_ne (hner (hn 19 (by simp)))]; exact c4
    · rw [WState.setv_val, Function.update_of_ne (hner (hn 16 (by simp)))]; exact c5
    · rw [WState.setv_val, Function.update_of_ne (hner (hn 17 (by simp)))]; exact c6
  have hrep := Runs.rep (cap := cap) (K := V 13) (K2 := V 14) (body := oneField U V) (hner (by decide))
    (oneFieldCost Wd fl.length (s + 1) m (t0 + (s + 1))) (s + 1) Inv (by omega)
    (fun j ρ v hI => hInv j ρ 13 (Or.inl rfl) v hI) (fun j ρ v hI => hInv j ρ 14 (Or.inr rfl) v hI) ?_ σ2
    ⟨hpre2, by simpa using (outOn_frame hO (a4.comp' hfr2) (by simp [emb_eq_iff]) (by simp [emb_eq_iff])),
      by rw [hv2 2 (by decide)]; exact hIDX, by simp [hσ2], by rw [hv2 16 (by decide)]; exact hCM,
      by rw [hv2 17 (by decide)]; exact hCM2, hBs, SameExcept.refl _ _ _⟩
    (by rw [hv2 13 (by decide)]; exact hJC) (by rw [hv2 14 (by decide)]; exact hJC2)
  · refine Runs.seqE h2 (Runs.seq (c2 := 3 * (t0 + (s + 1)) + 1 + 1 + (40 * (Wd + 1) + 11 + 1 +
      (18 * (m * (s + 1)) + 3 + 1 + 3))) hrep fun ρ hρ => ?_)
    obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, c9, c10⟩ := hρ
    have hvρ : ∀ k : Fin 25, k ≠ 5 → k ≠ 19 → k ≠ 13 → k ≠ 14 → ρ.val (V k) = σ.val (V k) := fun k h5 h19 h13 h14 => by
      rw [c8.val (by simp [emb_eq_iff, h5, h19, h13, h14])]; exact hv2 k h19
    have hc := wclear_spec (cap := cap) (V 19) (t0 + (s + 1)) ρ c4 (by omega)
    set ρ1 := ρ.setv (V 19) 0 with hρ1
    have hs1 : SameExcept ρ ρ1 [] [V 19] := sameExcept_setv ρ (by simp) 0
    set out' := out ++ ((List.range (s + 1)).map F).flatMap (fieldRec (Wd + 1)) with hout'
    have hlen' : out'.length = out.length + (s + 1) * (2 * (Wd + 1) + 1) := by
      rw [hout', List.length_append, fieldRecs_length]; simp
    have ha := appendRec_spec cap (Src := U 11) (O := U 2) (CS := V 4) (CO := V 5) (hne (by decide))
      (hner (by decide)) ρ1 (binary (Wd + 1) (encS coef)) [] out' L0
      (by simp [hρ1, c1.coef.1, BinW.frame_frameP]) (by simp [hρ1, c1.coef.2])
      (by simp [hρ1, c1.zero 4 (by simp)]) (outOn_frame c2 hs1 (by simp) (by simp [emb_eq_iff]))
      (by rw [hlen', binary_length]; nlinarith)
    rw [binary_length] at ha
    set ρ2 := ((ρ1.sets (U 2) (overlay (out' ++ frame (binary (Wd + 1) (encS coef))) L0)).seth (U 2)
      (out' ++ frame (binary (Wd + 1) (encS coef))).length).setv (V 5)
      (out' ++ frame (binary (Wd + 1) (encS coef))).length with hρ2
    have e18 : ρ2.val (V 18) = t0 := by
      simp [hρ2, hρ1]; rw [hvρ 18 (by decide) (by decide) (by decide) (by decide), hB0]
    have e23 : ρ2.val (V 23) = m * (s + 1) := by simp [hρ2, hρ1, c1.ms]
    have hd := addR_spec cap (A := V 23) (B := V 18) (T := V 20) (hner (by decide)) (hner (by decide))
      (hner (by decide)) ρ2 (by simp [hρ2, hρ1, c1.zero 20 (by simp)]) (by rw [e18, e23]; omega)
    rw [e18, e23] at hd
    set ρ3 := ρ2.setv (V 18) (t0 + m * (s + 1)) with hρ3
    have e24 : ρ3.val (V 24) = g := by
      simp [hρ3, hρ2, hρ1]; rw [hvρ 24 (by decide) (by decide) (by decide) (by decide), hGC]
    have hi := WXExec.inc cap (V 24) ρ3 (by rw [e24]; omega)
    set ρ4 := ρ3.setv (V 24) (ρ3.val (V 24) + 1) with hρ4
    have hfr4 : SameExcept ρ ρ4 [U 2] [V 5, V 18, V 19, V 24] := by
      refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ4, hρ3, hρ2, hρ1]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp [hρ4, hρ3, hρ2, hρ1, Function.update_of_ne hx]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hρ4, hρ3, hρ2, hρ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
          Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.2.2]
    have hv4 : ∀ k : Fin 25, k ≠ 5 → k ≠ 18 → k ≠ 19 → k ≠ 24 → ρ4.val (V k) = ρ.val (V k) := fun k a b c d =>
      hfr4.val (by simp [emb_eq_iff, a, b, c, d])
    refine Runs.of (WXExec.seq (WXExec.wm hc) (WXExec.seq (WXExec.wm ha) (WXExec.seq hd hi)))
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine sPre_frame U V c1 (hfr4.weaken (by unfold sStreams; simp) (by unfold sRegs; simp)) ?_ ?_ ?_
      · rw [hfr4.sh (by simp [emb_eq_iff])]; exact c1.wh
      · rw [hfr4.st (by simp [emb_eq_iff])]; exact c1.wl
      · intro k hk
        obtain ⟨v, hv⟩ := c1.words k hk
        have hk2 : U k ∉ [U 2] := by
          simp only [List.mem_singleton, emb_eq_iff]
          rintro rfl; simp at hk
        exact ⟨v, hfr4.numOn hk2 hv⟩
    · have e : out' ++ frame (binary (Wd + 1) (encS coef)) = out ++ cutRecs Wd s coef ls := by
        rw [cutRecs_eq Wd s coef ls hl, hm, hout', List.append_assoc]; rfl
      refine ⟨?_, ?_, ?_⟩
      · simp [hρ4, hρ3, hρ2, ← e]
      · simp [hρ4, hρ3, hρ2, ← e]
      · simp [hρ4, hρ3, hρ2, ← e]
    · rw [hv4 2 (by decide) (by decide) (by decide) (by decide)]; exact c3
    · simp [hρ4, hρ3, hρ2, hρ1]
    · simp [hρ4, hρ3]
    · rw [hv4 11 (by decide) (by decide) (by decide) (by decide), hvρ 11 (by decide) (by decide) (by decide)
        (by decide), hMC]
    · rw [hv4 12 (by decide) (by decide) (by decide) (by decide), hvρ 12 (by decide) (by decide) (by decide)
        (by decide), hMC2]
    · rw [hv4 13 (by decide) (by decide) (by decide) (by decide)]; exact c9
    · rw [hv4 14 (by decide) (by decide) (by decide) (by decide)]; exact c10
    · rw [hv4 16 (by decide) (by decide) (by decide) (by decide)]; exact c5
    · rw [hv4 17 (by decide) (by decide) (by decide) (by decide)]; exact c6
    · simp [hρ4, e24]
    · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hρ4, hρ3, hρ2, hρ1, c8.cell, hσ2, a4.cell]⟩
      · unfold sStreams at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hx
        have h1 := hfr4.1 x (by simp [n2])
        have h2 := c8.1 x (by unfold sStreams; simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10])
        have h3 := a4.1 x (by simp [n1, n5, n6])
        exact ⟨h1.1.trans (h2.1.trans (by simp [hσ2, h3.1])), h1.2.trans (h2.2.trans (by simp [hσ2, h3.2]))⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        by_cases r19 : r = V 19
        · rw [r19]; simp [hρ4, hρ3, hρ2, hρ1, hJB]
        · by_cases r13 : r = V 13
          · rw [r13, hv4 13 (by decide) (by decide) (by decide) (by decide), c9, hJC]
          · by_cases r14 : r = V 14
            · rw [r14, hv4 14 (by decide) (by decide) (by decide) (by decide), c10, hJC2]
            · rw [hfr4.val (by simp [hr.1, hr.2.1, hr.2.2, r19]), c8.val (by simp [hr.1, r19, r13, r14])]
              by_cases r19' : r = V 19
              · exact absurd r19' r19
              · simp only [hσ2, WState.setv_val, Function.update_of_ne r19]; exact hv1' r
  · intro j hj ρ ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩
    have hlenp : (((List.range j).map F).flatMap (fieldRec (Wd + 1))).length = j * (2 * (Wd + 1) + 1) := by
      rw [fieldRecs_length]; simp
    have hx := oneField_spec U V cap Wd (m * (s + 1)) (s + 1) m fl coef ρ t0 j ls b
      (out ++ ((List.range j).map F).flatMap (fieldRec (Wd + 1))) L0 hm hj hat hb1
      (fun c _ => by have := getD_le_magL ls c j; omega) hbm c1 c3 c4 c5 c6 c7 c2 hWd (by omega)
      (by
        rw [List.length_append, hlenp]
        have : (j + 1) * (2 * (Wd + 1) + 1) ≤ (s + 2) * (2 * (Wd + 1) + 1) := Nat.mul_le_mul_right _ (by omega)
        nlinarith)
    refine (hx.mono (oneFieldCost_mono _ _ _ _ _ _ (by omega)) fun τ ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ => ?_)
    refine ⟨⟨d1, ?_, d3, by rw [d4]; ring, d5, d6, d7, c8.trans (d8.weaken (by simp) (by simp))⟩,
      d8.val (by simp [emb_eq_iff]), d8.val (by simp [emb_eq_iff])⟩
    rw [List.range_succ, List.map_append, List.flatMap_append, ← List.append_assoc]
    simpa using d2

theorem cutRecs_length (Wd s : ℕ) (coef : ℤ) (ls : List (List ℤ)) (h : ∀ l ∈ ls, l.length = s + 1) :
    (cutRecs Wd s coef ls).length = (s + 2) * (2 * (Wd + 1) + 1) := by
  rw [cutRecs_eq Wd s coef ls h, List.length_append, fieldRecs_length]
  simp [fieldRec, frame_length]; ring

/-- **All tuples**: one cut each, in order. -/
def stackAll : WMX ns nr := .seq (repK (V 21) (V 22) (stackOne U V)) (.wm (WM.clear (V 18)))

def stackAllCost (Wd M N m n T : ℕ) : ℕ := T * (stackOneCost Wd M N m n (T * M) + 8) + 7 * T + 3 + 1 + (3 * (T * M) + 1)

theorem stackOneCost_mono (Wd M N m n p q : ℕ) (h : p ≤ q) : stackOneCost Wd M N m n p ≤ stackOneCost Wd M N m n q := by
  unfold stackOneCost baseCost oneFieldCost; nlinarith

theorem stackAll_spec (cap Wd s m : ℕ) (fl : List ℕ) (coef : ℤ) (σ : WState ns nr) (g : ℕ)
    (lss : List (List (List ℤ))) (out L0 : List Bool) (hm : ∀ ls ∈ lss, ls.length = m)
    (hl : ∀ ls ∈ lss, ∀ l ∈ ls, l.length = s + 1)
    (hat : ∀ t (ht : t < lss.length), TupleAt fl (t * (m * (s + 1))) (s + 1) lss[t])
    (hk : lss.length * (m * (s + 1)) ≤ fl.length) (hfl : ∀ x ∈ fl, x < 2 ^ (Wd + 1))
    (hbound : ∀ ls ∈ lss, (magL ls + 1) ^ (m + 1) < 2 ^ Wd) (hWd : 1 ≤ Wd)
    (hpre : SPre U V Wd (m * (s + 1)) (s + 1) m fl coef σ) (hIDX : σ.val (V 2) = 0) (hJB : σ.val (V 19) = 0)
    (hB0 : σ.val (V 18) = 0) (hMC : σ.val (V 11) = m * (s + 1)) (hMC2 : σ.val (V 12) = 0)
    (hJC : σ.val (V 13) = s + 1) (hJC2 : σ.val (V 14) = 0) (hCM : σ.val (V 16) = m) (hCM2 : σ.val (V 17) = 0)
    (hNT : σ.val (V 21) = lss.length) (hNT2 : σ.val (V 22) = 0)
    (hGC : σ.val (V 24) = g) (hO : OutOn σ (U 2) (V 5) out L0)
    (hcap : (fl.length + 1) * (2 * (Wd + 1) + 1) + 2 * fl.length + 2 * m + 2 * (m * (s + 1)) +
      lss.length * (m * (s + 1)) + 2 * (s + 1) + m * (s + 1) + g + lss.length + 1 + 2 * lss.length ≤ cap)
    (hcapO : out.length + lss.length * ((s + 2) * (2 * (Wd + 1) + 1)) + 1 ≤ cap) :
    Runs cap (stackAll U V) σ (stackAllCost Wd (m * (s + 1)) (s + 1) m fl.length lss.length) (fun τ =>
      SPre U V Wd (m * (s + 1)) (s + 1) m fl coef τ ∧
        OutOn τ (U 2) (V 5) (out ++ lss.flatMap (cutRecs Wd s coef)) L0 ∧ τ.val (V 24) = g + lss.length ∧
        SameExcept σ τ (sStreams U) [V 5, V 24]) := by
  have hne : ∀ {a b : Fin 14}, a ≠ b → U a ≠ U b := fun h => emb_ne U h
  have hner : ∀ {a b : Fin 25}, a ≠ b → V a ≠ V b := fun h => emb_ne V h
  set M := m * (s + 1) with hM
  set T := lss.length with hT
  let Inv : ℕ → WState ns nr → Prop := fun t ρ =>
    SPre U V Wd M (s + 1) m fl coef ρ ∧ OutOn ρ (U 2) (V 5) (out ++ (lss.take t).flatMap (cutRecs Wd s coef)) L0 ∧
      ρ.val (V 2) = 0 ∧ ρ.val (V 19) = 0 ∧ ρ.val (V 18) = t * M ∧ ρ.val (V 11) = M ∧ ρ.val (V 12) = 0 ∧
      ρ.val (V 13) = s + 1 ∧ ρ.val (V 14) = 0 ∧ ρ.val (V 16) = m ∧ ρ.val (V 17) = 0 ∧ ρ.val (V 24) = g + t ∧
      SameExcept σ ρ (sStreams U) [V 5, V 18, V 24, V 21, V 22]
  have hInv : ∀ t ρ (k : Fin 25), k = 21 ∨ k = 22 → ∀ v, Inv t ρ → Inv t (ρ.setv (V k) v) := by
    rintro t ρ k hk v ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩
    have hs : SameExcept ρ (ρ.setv (V k) v) [] [V k] := sameExcept_setv ρ (by simp) v
    have hn : ∀ i : Fin 25, i ∈ [(2 : Fin 25), 5, 19, 18, 11, 12, 13, 14, 16, 17, 24] → i ≠ k := by
      intro i hi; rcases hk with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hv : ∀ i : Fin 25, i ∈ [(2 : Fin 25), 5, 19, 18, 11, 12, 13, 14, 16, 17, 24] →
        (ρ.setv (V k) v).val (V i) = ρ.val (V i) := fun i hi => by
      rw [WState.setv_val, Function.update_of_ne (hner (hn i hi))]
    refine ⟨sPre_frame U V c1 (hs.weaken (by simp) (by unfold sRegs; rcases hk with rfl | rfl <;> simp))
      (by simpa using c1.wh) (by simpa using c1.wl) (fun k hk => (c1.words k hk).elim fun x hx =>
        ⟨x, BinW.numOn_setv hx _ _⟩), outOn_frame c2 hs (by simp) (by simp [emb_eq_iff, hn 5 (by simp)]),
      by rw [hv 2 (by simp)]; exact c3, by rw [hv 19 (by simp)]; exact c4, by rw [hv 18 (by simp)]; exact c5,
      by rw [hv 11 (by simp)]; exact c6, by rw [hv 12 (by simp)]; exact c7, by rw [hv 13 (by simp)]; exact c8,
      by rw [hv 14 (by simp)]; exact c9, by rw [hv 16 (by simp)]; exact c10, by rw [hv 17 (by simp)]; exact c11,
      by rw [hv 24 (by simp)]; exact c12, c13.trans (sameExcept_setv ρ (by rcases hk with rfl | rfl <;> simp) v)⟩
  have hrep := Runs.rep (cap := cap) (K := V 21) (K2 := V 22) (body := stackOne U V) (hner (by decide))
    (stackOneCost Wd M (s + 1) m fl.length (T * M)) T Inv (by omega)
    (fun t ρ v hI => hInv t ρ 21 (Or.inl rfl) v hI) (fun t ρ v hI => hInv t ρ 22 (Or.inr rfl) v hI) ?_ σ
    ⟨hpre, by simpa using hO, hIDX, hJB, by simp [hB0], hMC, hMC2, hJC, hJC2, hCM, hCM2, by simp [hGC],
      SameExcept.refl _ _ _⟩ hNT hNT2
  · refine (Runs.seq (c2 := 3 * (T * M) + 1) hrep fun ρ hρ => ?_).cost (by unfold stackAllCost; omega)
    obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩, c14, c15⟩ := hρ
    rw [List.take_of_length_le (le_refl _)] at c2
    have hc := wclear_spec (cap := cap) (V 18) (T * M) ρ c5 (by omega)
    have hs : SameExcept ρ (ρ.setv (V 18) 0) [] [V 18] := sameExcept_setv ρ (by simp) 0
    refine Runs.of (WXExec.wm hc) ⟨sPre_frame U V c1 (hs.weaken (by simp) (by unfold sRegs; simp))
      (by simpa using c1.wh) (by simpa using c1.wl) (fun k hk => (c1.words k hk).elim fun x hx =>
        ⟨x, BinW.numOn_setv hx _ _⟩), outOn_frame c2 hs (by simp) (by simp [emb_eq_iff]), ?_, ?_⟩
    · rw [WState.setv_val, Function.update_of_ne (hner (by decide))]; exact c12
    · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [c13.cell]⟩
      · have := c13.1 x hx; simp [this.1, this.2]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        by_cases r18 : r = V 18
        · rw [r18]; simp [hB0]
        · rw [WState.setv_val, Function.update_of_ne r18]
          by_cases r21 : r = V 21
          · rw [r21, c14, hNT]
          · by_cases r22 : r = V 22
            · rw [r22, c15, hNT2]
            · exact c13.2.1 r (by simp [hr.1, hr.2, r18, r21, r22])
  · intro t ht ρ ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩
    have hlst := List.getElem_mem ht
    have hpl : ((lss.take t).flatMap (cutRecs Wd s coef)).length = t * ((s + 2) * (2 * (Wd + 1) + 1)) := by
      have : ∀ k ≤ T, ((lss.take k).flatMap (cutRecs Wd s coef)).length = k * ((s + 2) * (2 * (Wd + 1) + 1)) := by
        intro k hk
        induction k with
        | zero => simp
        | succ k ih =>
          rw [flatMap_take_succ' lss _ k (by omega), List.length_append, ih (by omega),
            cutRecs_length Wd s coef _ (hl _ (List.getElem_mem (by omega)))]
          ring
      exact this t ht.le
    have htm : t * M + M ≤ T * M := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht
    have hx := stackOne_spec U V cap Wd s m fl coef ρ (t * M) (g + t) lss[t] (out ++ (lss.take t).flatMap
      (cutRecs Wd s coef)) L0 (hm _ hlst) (hl _ hlst) (hat t ht) (by omega) hfl (hbound _ hlst) hWd c1 c3 c4 c5
      c6 c7 c8 c9 c10 c11 c12 c2 (by omega)
      (by
        rw [List.length_append, hpl]
        have : (t + 1) * ((s + 2) * (2 * (Wd + 1) + 1)) ≤ T * ((s + 2) * (2 * (Wd + 1) + 1)) :=
          Nat.mul_le_mul_right _ ht
        nlinarith)
    refine hx.mono (stackOneCost_mono _ _ _ _ _ _ _ (by omega)) fun τ ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11,
      d12, d13⟩ => ⟨⟨d1, ?_, d3, d4, by rw [d5]; ring, d6, d7, d8, d9, d10, d11, by rw [d12]; ring, ?_⟩, ?_, ?_⟩
    · rw [flatMap_take_succ' lss _ t ht, ← List.append_assoc]; exact d2
    · refine c13.trans (d13.weaken (by simp) ?_)
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h]
    · exact d13.val (by simp [emb_eq_iff])
    · exact d13.val (by simp [emb_eq_iff])

end Stack2

end NearCubicGates.Close.TabMachine
