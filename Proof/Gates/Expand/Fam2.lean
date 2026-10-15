import Proof.Gates.Expand.Fam

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

theorem flatMap_frame_binary (Wb : ℕ) (xs : List ℕ) :
    (xs.map (binary Wb)).flatMap frame = xs.flatMap fun x => frame (binary Wb x) := by
  rw [List.flatMap_map]

theorem overlay_rec (out L0 : List Bool) : ∃ junk, overlay (out ++ [false]) L0 = out ++ [false] ++ junk :=
  ⟨L0.drop (out ++ [false]).length, rfl⟩

section LevelSpec
variable {UF : Fin 12 ↪ Fin (ns + 1)} {RF : Fin 14 ↪ Fin nr}

def famLevelCost (Wb V n : ℕ) (outN : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + (((n * (famBodyCost Wb V + (50 * Wb + 30))) + 3) + 1 + ((5 * outN + 3) + 1 +
    (((outN + 1) * (40 * Wb + 11 + (50 * Wb + 30)) + 3) + 1 + (((outN + 1) * (40 * Wb + 11 + (50 * Wb + 30)) + 3) + 1 +
      (5 * (outN * (2 * Wb + 1)) + 3)))))

theorem lvlRecs_lt (V d : ℕ) : ∀ x ∈ lvlRecs V d, x < (d + 1) * 2 ^ V := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  have := (level_mem V d s hs).1
  nlinarith

theorem lvlRecs_length (V d : ℕ) : (lvlRecs V d).length = (level V d).length := by simp [lvlRecs]

theorem len_frames (Wb : ℕ) (xs : List ℕ) : (xs.flatMap fun x => frame (binary Wb x)).length = xs.length * (2 * Wb + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih, frame_length]; ring

theorem take_flatMap_le {α β : Type} (l : List α) (f : α → List β) (i : ℕ) :
    ((l.take i).flatMap f).length ≤ (l.flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.flatMap_append, List.length_append]; omega

/-- The loop invariant over CUR's records (after `DT := (j+1)·T`, from the state `σ1`). -/
def LInv (UF : Fin 12 ↪ Fin (ns + 1)) (RF : Fin 14 ↪ Fin nr) (Wb V j : ℕ) (L0N : List Bool) (σ1 : WState ns nr)
    (i : ℕ) (τ : WState ns nr) : Prop :=
  OutOn τ (UF 1) (RF 5) (((level V j).take i).flatMap fun s => emitted Wb ((j + 1) * 2 ^ V) s V) L0N ∧
    SameExcept σ1 τ [UF 0, UF 1, UF 3, UF 4, UF 5, UF 6] [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 10, RF 11] ∧
    (∃ x, NumOn τ (UF 4) Wb x) ∧ (∃ x, NumOn τ (UF 5) Wb x) ∧ (∃ x, NumOn τ (UF 6) Wb x) ∧
    τ.val (RF 0) = 0 ∧ τ.val (RF 1) = 0 ∧ τ.val (RF 4) = 0 ∧ τ.val (RF 10) = V ∧ τ.val (RF 11) = 0 ∧
    τ.sh (UF 3) = 0 ∧ (τ.st (UF 3)).length ≤ 2 * Wb + 1

/-- The family body meets the record loop's hypothesis. -/
theorem famBodyJ (cap Wb V j : ℕ) (L0N junkC : List Bool) (σ1 : WState ns nr)
    (h1 : NumOn σ1 (UF 7) Wb 1) (hDT : NumOn σ1 (UF 9) Wb ((j + 1) * 2 ^ V))
    (hM : NumOn σ1 (UF 10) Wb (2 ^ V - 1)) (hVW : V + 1 < Wb) (hjW : (j + 3) * 2 ^ V < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapV : 2 * V ≤ cap)
    (hcapN : ((level V j).length + (level V (j + 1)).length + 1) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    BodySpecJ cap Wb (I := UF 0) (Wk := UF 3) (CI := RF 2) (CW := RF 3) (famBody UF RF)
      ((lvlRecs V j).map (binary Wb)) (LInv UF RF Wb V j L0N σ1) (fun _ => famBodyCost Wb V) junkC := by
  intro i hi τ hτ _ _ _ _ hwh _
  obtain ⟨hO, hfr, ⟨x4, h4⟩, ⟨x5, h5⟩, ⟨x6, h6⟩, hf, hr, hcs, hrv, hrv2, -, -⟩ := hτ
  have hil : i < (level V j).length := by simpa [lvlRecs] using hi
  set si := (level V j)[i] with hsi
  have hsi_lt : si < 2 ^ V := (level_mem V j si (List.getElem_mem hil)).1
  have hwsi : ((lvlRecs V j).map (binary Wb))[i] = binary Wb (si + j * 2 ^ V) := by simp [lvlRecs, hsi]
  set τa := atRec (UF 0) (UF 3) (RF 2) τ ((lvlRecs V j).map (binary Wb))[i] ((i + 1) * (2 * Wb + 1)) with hτa
  have fa : SameExcept τ τa [UF 0, UF 3] [RF 2] := by
    rw [hτa]; unfold atRec
    exact SameExcept.trans (SameExcept.trans (sameExcept_sets τ (by simp) _) (sameExcept_seth _ (by simp) _))
      (sameExcept_setv _ (by simp) _)
  have nin : ∀ k : Fin 12, k ∈ ([1, 4, 5, 6, 7, 8, 9, 10] : List (Fin 12)) → UF k ∉ [UF 0, UF 3] := by
    intro k hk hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm <;> have := UF.injective hm <;> subst this <;> simp at hk
  have hWK : NumOn τa (UF 3) Wb (si + j * 2 ^ V) := by
    refine ⟨?_, ?_⟩
    · simp only [hτa, atRec, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]; rw [hwsi]
    · simp [hτa, atRec, Function.update_of_ne (ufN (by decide : (3 : Fin 12) ≠ 0)), hwh]
  have fσ1τa : SameExcept σ1 τa [UF 0, UF 1, UF 3, UF 4, UF 5, UF 6] [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 10, RF 11] :=
    SameExcept.trans hfr (fa.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))
  have cst : ∀ k : Fin 12, k ∈ ([7, 8, 9, 10] : List (Fin 12)) → ∀ x, NumOn σ1 (UF k) Wb x → NumOn τa (UF k) Wb x := by
    intro k hk x hx
    refine fσ1τa.numOn ?_ hx
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm <;> have := UF.injective hm <;> subst this <;> simp at hk
  have hOa : OutOn τa (UF 1) (RF 5) (((level V j).take i).flatMap fun s => emitted Wb ((j + 1) * 2 ^ V) s V) L0N :=
    ⟨by rw [fa.st (nin 1 (by decide))]; exact hO.1, by rw [fa.sh (nin 1 (by decide))]; exact hO.2.1,
      by rw [fa.val (by simp [rfN])]; exact hO.2.2⟩
  have e1 : ((level V j).take i).flatMap (fun s => emitted Wb ((j + 1) * 2 ^ V) s V) ++
      emitted Wb ((j + 1) * 2 ^ V) si V = ((level V j).take (i + 1)).flatMap fun s => emitted Wb ((j + 1) * 2 ^ V) s V := by
    rw [WordPrograms.flatMap_take_succ' _ _ i hil]
  have hfb := famBody_spec (UF := UF) (RF := RF) cap Wb V j ((j + 1) * 2 ^ V) si _ L0N τa hWK
    ⟨x4, fa.numOn (nin 4 (by decide)) h4⟩ ⟨x5, fa.numOn (nin 5 (by decide)) h5⟩
    ⟨x6, fa.numOn (nin 6 (by decide)) h6⟩ (cst 7 (by decide) 1 h1) (cst 9 (by decide) _ hDT)
    (cst 10 (by decide) _ hM)
    (by rw [fa.val (by simp [rfN])]; exact hf) (by rw [fa.val (by simp [rfN])]; exact hr)
    (by rw [fa.val (by simp [rfN])]; exact hcs) (by rw [fa.val (by simp [rfN])]; exact hrv)
    (by rw [fa.val (by simp [rfN])]; exact hrv2) hOa hsi_lt hVW
    (by rw [show 2 ^ (V + 1) + (j + 1) * 2 ^ V = (j + 3) * 2 ^ V by ring]; exact hjW) hcap hcapV (by
      refine le_trans ?_ hcapN
      have e2 : (((level V j).take (i + 1)).flatMap fun s => emitted Wb ((j + 1) * 2 ^ V) s V).length ≤
          (level V (j + 1)).length * (2 * Wb + 1) := by
        refine le_trans (take_flatMap_le _ _ _) ?_
        rw [emitted_level, len_frames, lvlRecs_length]
      rw [e1]; nlinarith)
  obtain ⟨τ', hrun, hVS, hrv', hrv2'⟩ := hfb
  have hwk1 : τ'.sh (UF 3) = 0 := by
    rw [hVS.fr.sh (by simp [ufN])]; simp [hτa, atRec, Function.update_of_ne (ufN (by decide : (3 : Fin 12) ≠ 0)), hwh]
  have hwk2 : (τ'.st (UF 3)).length ≤ 2 * Wb + 1 := by
    rw [hVS.fr.st (by simp [ufN]), hWK.1]; simp [frame_length]
  refine ⟨τ', hrun, ⟨?_, ?_, ⟨si, hVS.S⟩, ⟨_, hVS.P⟩, hVS.E, hVS.f, hVS.r, hVS.cs, hrv', hrv2', hwk1, hwk2⟩, ?_⟩
  · rw [← e1]; exact hVS.out
  · exact SameExcept.trans fσ1τa (hVS.fr.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))
  · exact ⟨hVS.fr.st (by simp [ufN]), hVS.fr.sh (by simp [ufN]), hVS.fr.val (by simp [rfN]),
      hVS.fr.val (by simp [rfN]), hwk1, hwk2⟩

/-- The family phase after the loop over CUR (NXT holds the next level, still open). -/
structure MID (UF : Fin 12 ↪ Fin (ns + 1)) (RF : Fin 14 ↪ Fin nr) (Wb V j : ℕ) (outF L0F L0N : List Bool)
    (σ0 σ : WState ns nr) : Prop where
  curh : σ.sh (UF 0) = 0
  nxt : OutOn σ (UF 1) (RF 5) ((lvlRecs V (j + 1)).flatMap fun x => frame (binary Wb x)) L0N
  fam : OutOn σ (UF 2) (RF 6) (outF ++ famUpTo Wb V j) L0F
  wkh : σ.sh (UF 3) = 0
  wkl : (σ.st (UF 3)).length ≤ 2 * Wb + 1
  S : ∃ x, NumOn σ (UF 4) Wb x
  P : ∃ x, NumOn σ (UF 5) Wb x
  E : ∃ x, NumOn σ (UF 6) Wb x
  one : NumOn σ (UF 7) Wb 1
  T : NumOn σ (UF 8) Wb (2 ^ V)
  dtn : NumOn σ (UF 9) Wb ((j + 1) * 2 ^ V)
  mask : NumOn σ (UF 10) Wb (2 ^ V - 1)
  regs : ∀ k : Fin 14, k ∈ ([0, 1, 2, 3, 4, 7, 11, 12, 13] : List (Fin 14)) → σ.val (RF k) = 0
  rv : σ.val (RF 10) = V
  fr : SameExcept σ0 σ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9]
    [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13]

def famLoopCost (Wb V n : ℕ) : ℕ := (41 * Wb + 3) + 1 + ((n * (famBodyCost Wb V + (50 * Wb + 30))) + 3)

theorem famLoop_spec (cap Wb V j : ℕ) (outF L0F : List Bool) (σ0 σ : WState ns nr)
    (h : FLS UF RF Wb V j outF L0F σ0 σ) (hVW : V + 1 < Wb) (hjW : (j + 3) * 2 ^ V < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapV : 2 * V ≤ cap)
    (hcapN : ((level V j).length + (level V (j + 1)).length + 1) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    Runs cap (.seq (BinW.add (UF 9) (UF 8) (RF 0) (RF 1)) (recLoop (UF 0) (UF 3) (RF 2) (RF 3) (famBody UF RF))) σ
      (famLoopCost Wb V (level V j).length) (MID UF RF Wb V j outF L0F (σ.st (UF 1)) σ0) := by
  have a1 := BinW.add_spec cap Wb (ufN (by decide : (9 : Fin 12) ≠ 8)) (rfN (by decide : (0 : Fin 14) ≠ 1)) σ _ _
    h.dtn h.T (h.regs 0 (by decide)) (h.regs 1 (by decide))
    (by rw [show j * 2 ^ V + 2 ^ V = (j + 1) * 2 ^ V by ring]
        exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hjW) hcap
  rw [show j * 2 ^ V + 2 ^ V = (j + 1) * 2 ^ V by ring] at a1
  set σ1 := σ.sets (UF 9) (frame (binary Wb ((j + 1) * 2 ^ V))) with hσ1
  have f01 : SameExcept σ σ1 [UF 9] [] := sameExcept_sets σ (by simp) _
  obtain ⟨junkC, hcur⟩ := h.cur
  set L0N := σ.st (UF 1) with hL0N
  have nin9 : ∀ k : Fin 12, k ≠ 9 → UF k ∉ [UF 9] := by
    intro k hk hm; simp only [List.mem_singleton] at hm; exact hk (UF.injective hm)
  have hInv0 : LInv UF RF Wb V j L0N σ1 0 σ1 := by
    refine ⟨⟨?_, ?_, ?_⟩, SameExcept.refl _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hσ1, overlay, Function.update_of_ne (ufN (by decide : (1 : Fin 12) ≠ 9))]; rfl
    · simp [hσ1, h.nxth]
    · simp [hσ1, h.regs 5 (by decide)]
    · obtain ⟨x, hx⟩ := h.S; exact ⟨x, f01.numOn (nin9 4 (by decide)) hx⟩
    · obtain ⟨x, hx⟩ := h.P; exact ⟨x, f01.numOn (nin9 5 (by decide)) hx⟩
    · obtain ⟨x, hx⟩ := h.E; exact ⟨x, f01.numOn (nin9 6 (by decide)) hx⟩
    · simpa [hσ1] using h.regs 0 (by decide)
    · simpa [hσ1] using h.regs 1 (by decide)
    · simpa [hσ1] using h.regs 4 (by decide)
    · simpa [hσ1] using h.rv
    · simpa [hσ1] using h.regs 11 (by decide)
    · simpa [hσ1] using h.wkh
    · rw [f01.st (nin9 3 (by decide))]; exact h.wkl
  have hb := famBodyJ (UF := UF) (RF := RF) cap Wb V j L0N junkC σ1 (f01.numOn (nin9 7 (by decide)) h.one)
    (numOn_sets_self σ _ Wb _ h.dtn.2) (f01.numOn (nin9 10 (by decide)) h.mask) hVW hjW hcap hcapV hcapN
  have hw : ∀ w ∈ (lvlRecs V j).map (binary Wb), w.length = Wb := by
    intro w hw; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw; simp
  have hlenws : ((lvlRecs V j).map (binary Wb)).length = (level V j).length := by simp [lvlRecs]
  have hcurL : σ1.st (UF 0) = recStream ((lvlRecs V j).map (binary Wb)) ++ junkC := by
    rw [f01.st (nin9 0 (by decide)), hcur]
  obtain ⟨τ2, hInvN, _, hcw2, hloop⟩ := recLoopJ_spec (cap := cap) (L := Wb) (ufN (by decide : (0 : Fin 12) ≠ 3))
    (rfN (by decide : (2 : Fin 14) ≠ 3)) hw (by omega) (by rw [hlenws]; nlinarith) hb σ1 hInv0 hcurL
    (by rw [f01.sh (nin9 0 (by decide))]; exact h.curh) (by simpa [hσ1] using h.regs 2 (by decide))
    (by simpa [hσ1] using h.regs 3 (by decide)) (by rw [f01.sh (nin9 3 (by decide))]; exact h.wkh)
    (by rw [f01.st (nin9 3 (by decide))]; exact h.wkl)
  rw [hlenws] at hInvN hloop
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
  obtain ⟨hO2, hfr2, hS2, hP2, hE2, hf2, hr2, hcs2, hrv2, hrv22, hwk2a, hwk2b⟩ := hInvN
  refine ⟨_, WXExec.seq a1 hloop, ?_⟩
  set ρ2 := (τ2.setv (RF 2) 0).seth (UF 0) 0 with hρ2
  have f2 : SameExcept τ2 ρ2 [UF 0] [RF 2] := by
    rw [hρ2]; exact SameExcept.trans (sameExcept_setv _ (by simp) _) (sameExcept_seth _ (by simp) _)
  have fσρ2 : SameExcept σ ρ2 [UF 0, UF 1, UF 3, UF 4, UF 5, UF 6, UF 9]
      [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 10, RF 11] :=
    SameExcept.trans (SameExcept.trans
      (f01.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr))
      (hfr2.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto)))
      (f2.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))
  have ninS : ∀ k : Fin 12, k ∈ ([2, 7, 8, 10] : List (Fin 12)) →
      UF k ∉ [UF 0, UF 1, UF 3, UF 4, UF 5, UF 6, UF 9] := by
    intro k hk hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm <;> have := UF.injective hm <;> subst this <;> simp at hk
  have ninR : ∀ k : Fin 14, k ∈ ([6, 7, 12, 13] : List (Fin 14)) →
      RF k ∉ [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 10, RF 11] := by
    intro k hk hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm <;> have := RF.injective hm <;> subst this <;> simp at hk
  have hnxt : OutOn ρ2 (UF 1) (RF 5) ((lvlRecs V (j + 1)).flatMap fun x => frame (binary Wb x)) L0N := by
    have e : ((level V j).take (level V j).length).flatMap (fun s => emitted Wb ((j + 1) * 2 ^ V) s V) =
        (lvlRecs V (j + 1)).flatMap fun x => frame (binary Wb x) := by
      rw [List.take_length, emitted_level]
    rw [← e]
    exact ⟨by rw [f2.st (by simp [ufN])]; exact hO2.1, by rw [f2.sh (by simp [ufN])]; exact hO2.2.1,
      by rw [f2.val (by simp [rfN])]; exact hO2.2.2⟩
  refine ⟨by simp [hρ2], hnxt, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fσρ2.st (ninS 2 (by decide))]; exact h.fam.1
  · rw [fσρ2.sh (ninS 2 (by decide))]; exact h.fam.2.1
  · rw [fσρ2.val (ninR 6 (by decide))]; exact h.fam.2.2
  · rw [f2.sh (by simp [ufN])]; exact hwk2a
  · rw [f2.st (by simp [ufN])]; exact hwk2b
  · obtain ⟨x, hx⟩ := hS2; exact ⟨x, f2.numOn (by simp [ufN]) hx⟩
  · obtain ⟨x, hx⟩ := hP2; exact ⟨x, f2.numOn (by simp [ufN]) hx⟩
  · obtain ⟨x, hx⟩ := hE2; exact ⟨x, f2.numOn (by simp [ufN]) hx⟩
  · exact fσρ2.numOn (ninS 7 (by decide)) h.one
  · exact fσρ2.numOn (ninS 8 (by decide)) h.T
  · exact f2.numOn (by simp [ufN]) (hfr2.numOn (by simp [ufN]) (numOn_sets_self σ _ Wb _ h.dtn.2))
  · exact fσρ2.numOn (ninS 10 (by decide)) h.mask
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [f2.val (by simp [rfN])]; exact hf2
    · rw [f2.val (by simp [rfN])]; exact hr2
    · simp [hρ2]
    · rw [f2.val (by simp [rfN])]; exact hcw2
    · rw [f2.val (by simp [rfN])]; exact hcs2
    · rw [fσρ2.val (ninR 7 (by decide))]; exact h.regs 7 (by decide)
    · rw [f2.val (by simp [rfN])]; exact hrv22
    · rw [fσρ2.val (ninR 12 (by decide))]; exact h.regs 12 (by decide)
    · rw [fσρ2.val (ninR 13 (by decide))]; exact h.regs 13 (by decide)
  · rw [f2.val (by simp [rfN])]; exact hrv2
  · exact SameExcept.trans h.fr (fσρ2.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))

def famTailCost (Wb n : ℕ) : ℕ :=
  (5 * (n * (2 * Wb + 1)) + 3) + 1 + ((n * (40 * Wb + 11 + (50 * Wb + 30)) + 3) + 1 +
    ((n * (40 * Wb + 11 + (50 * Wb + 30)) + 3) + 1 + (5 * (n * (2 * Wb + 1)) + 3)))

theorem famTail_spec (cap Wb V j : ℕ) (outF L0F L0N : List Bool) (σ0 σ : WState ns nr)
    (h : MID UF RF Wb V j outF L0F L0N σ0 σ) (hW1 : 1 ≤ Wb)
    (hcapN : ((level V (j + 1)).length + 1) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap)
    (hcapF : (outF ++ famUpTo Wb V (j + 1)).length + 1 ≤ cap) :
    Runs cap (.seq (closeOutX (UF 1) (RF 5)) (.seq (copyAll (UF 1) (UF 3) (UF 2) (RF 12) (RF 13) (RF 4) (RF 6))
      (.seq (copyAll (UF 1) (UF 3) (UF 0) (RF 12) (RF 13) (RF 4) (RF 7)) (closeOutX (UF 0) (RF 7))))) σ
      (famTailCost Wb (level V (j + 1)).length)
      (FLS UF RF Wb V (j + 1) outF L0F σ0) := by
  set xs := lvlRecs V (j + 1) with hxs
  set outN := xs.flatMap fun x => frame (binary Wb x) with houtN
  have hlenN : outN.length = (level V (j + 1)).length * (2 * Wb + 1) := by
    rw [houtN, len_frames, hxs, lvlRecs_length]
  have hxl : xs.length = (level V (j + 1)).length := by rw [hxs, lvlRecs_length]
  -- close NXT
  have c1 := closeOut_spec cap σ outN L0N h.nxt (by rw [hlenN]; nlinarith)
  set ρ1 := ((σ.sets (UF 1) (overlay (outN ++ [false]) L0N)).seth (UF 1) 0).setv (RF 5) 0 with hρ1
  have f1 : SameExcept σ ρ1 [UF 1] [RF 5] := by
    rw [hρ1]; exact SameExcept.trans (SameExcept.trans (sameExcept_sets _ (by simp) _) (sameExcept_seth _ (by simp) _))
      (sameExcept_setv _ (by simp) _)
  obtain ⟨junkN, hjN⟩ := overlay_rec outN L0N
  have hNXT : ρ1.st (UF 1) = recStream (xs.map (binary Wb)) ++ junkN := by
    rw [hρ1]; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [hjN, houtN, ← flatMap_frame_binary]; rfl
  have nin1 : ∀ k : Fin 12, k ≠ 1 → UF k ∉ [UF 1] := by
    intro k hk hm; simp only [List.mem_singleton] at hm; exact hk (UF.injective hm)
  have rin1 : ∀ k : Fin 14, k ≠ 5 → RF k ∉ [RF 5] := by
    intro k hk hm; simp only [List.mem_singleton] at hm; exact hk (RF.injective hm)
  suffices hr : Runs cap (.seq (closeOutX (UF 1) (RF 5)) (.seq (copyAll (UF 1) (UF 3) (UF 2) (RF 12) (RF 13) (RF 4) (RF 6))
      (.seq (copyAll (UF 1) (UF 3) (UF 0) (RF 12) (RF 13) (RF 4) (RF 7)) (closeOutX (UF 0) (RF 7))))) σ
      ((5 * outN.length + 3) + 1 + ((xs.length * (40 * Wb + 11 + (50 * Wb + 30)) + 3) + 1 +
        ((xs.length * (40 * Wb + 11 + (50 * Wb + 30)) + 3) + 1 + (5 * outN.length + 3))))
      (FLS UF RF Wb V (j + 1) outF L0F σ0) by
    exact hr.cost (by rw [hlenN, hxl]; unfold famTailCost; omega)
  have hFAM1 : OutOn ρ1 (UF 2) (RF 6) (outF ++ famUpTo Wb V j) L0F :=
    ⟨by rw [f1.st (nin1 2 (by decide))]; exact h.fam.1, by rw [f1.sh (nin1 2 (by decide))]; exact h.fam.2.1,
      by rw [f1.val (rin1 6 (by decide))]; exact h.fam.2.2⟩
  refine Runs.seqE (WXExec.wm c1) (Runs.seq (copyAll_spec cap (I := UF 1) (Wk := UF 3) (O := UF 2) (CI := RF 12)
    (CW := RF 13) (CS := RF 4) (CO := RF 6) (by simp [ufN]) (by simp [rfN]) Wb hW1 xs ρ1 junkN
    _ L0F hNXT (by simp [hρ1]) (by rw [f1.val (rin1 12 (by decide))]; exact h.regs 12 (by decide))
    (by rw [f1.val (rin1 13 (by decide))]; exact h.regs 13 (by decide))
    (by rw [f1.val (rin1 4 (by decide))]; exact h.regs 4 (by decide))
    (by rw [f1.sh (nin1 3 (by decide))]; exact h.wkh) (by rw [f1.st (nin1 3 (by decide))]; exact h.wkl) hFAM1
    (by rw [hxl]; nlinarith) (by
      have := hcapF
      rw [famUpTo_succ, ← List.append_assoc, List.length_append, len_frames] at this
      rw [List.length_append] at this ⊢; omega)) (fun ρ2 ⟨hF2, hw2a, hw2b, f2⟩ => ?_))
  -- copy NXT to CUR
  have hCUR2 : OutOn ρ2 (UF 0) (RF 7) [] (ρ2.st (UF 0)) := by
    refine outOn_start ρ2 (UF 0) (RF 7) ?_ ?_
    · rw [f2.sh (by simp [ufN]), f1.sh (nin1 0 (by decide))]; exact h.curh
    · rw [f2.val (by simp [rfN]), f1.val (rin1 7 (by decide))]; exact h.regs 7 (by decide)
  have hNXT2 : ρ2.st (UF 1) = recStream (xs.map (binary Wb)) ++ junkN := by
    rw [f2.st (by simp [ufN])]; exact hNXT
  refine Runs.seq (copyAll_spec cap (I := UF 1) (Wk := UF 3) (O := UF 0) (CI := RF 12) (CW := RF 13) (CS := RF 4)
    (CO := RF 7) (by simp [ufN]) (by simp [rfN]) Wb hW1 xs ρ2 junkN
    [] (ρ2.st (UF 0)) hNXT2 (by rw [f2.sh (by simp [ufN])]; simp [hρ1])
    (by rw [f2.val (by simp [rfN]), f1.val (rin1 12 (by decide))]; exact h.regs 12 (by decide))
    (by rw [f2.val (by simp [rfN]), f1.val (rin1 13 (by decide))]; exact h.regs 13 (by decide))
    (by rw [f2.val (by simp [rfN]), f1.val (rin1 4 (by decide))]; exact h.regs 4 (by decide))
    hw2a hw2b hCUR2 (by rw [hxl]; nlinarith) (by simp; rw [hxl]; nlinarith)) (fun ρ3 ⟨hC3, hw3a, hw3b, f3⟩ => ?_)
  -- close CUR
  rw [List.nil_append] at hC3
  have c4 := closeOut_spec cap ρ3 _ _ hC3 (by rw [len_frames, hxl]; nlinarith)
  rw [← houtN] at c4
  refine ⟨_, WXExec.wm c4, ?_⟩
  set ρ4 := ((ρ3.sets (UF 0) (overlay ((xs.flatMap fun x => frame (binary Wb x)) ++ [false]) (ρ2.st (UF 0)))).seth
    (UF 0) 0).setv (RF 7) 0 with hρ4
  have f4 : SameExcept ρ3 ρ4 [UF 0] [RF 7] := by
    rw [hρ4]; exact SameExcept.trans (SameExcept.trans (sameExcept_sets _ (by simp) _) (sameExcept_seth _ (by simp) _))
      (sameExcept_setv _ (by simp) _)
  have f14 : SameExcept σ ρ4 [UF 0, UF 1, UF 2, UF 3] [RF 5, RF 6, RF 7] :=
    SameExcept.trans (SameExcept.trans (SameExcept.trans
      (f1.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))
      (f2.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto)))
      (f3.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto)))
      (f4.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))
  have ninA : ∀ k : Fin 12, k ∈ ([4, 5, 6, 7, 8, 9, 10] : List (Fin 12)) → UF k ∉ [UF 0, UF 1, UF 2, UF 3] := by
    intro k hk hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm <;> have := UF.injective hm <;> subst this <;> simp at hk
  have rinA : ∀ k : Fin 14, k ∈ ([0, 1, 2, 3, 4, 10, 11, 12, 13] : List (Fin 14)) → RF k ∉ [RF 5, RF 6, RF 7] := by
    intro k hk hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm <;> have := RF.injective hm <;> subst this <;> simp at hk
  refine ⟨?_, by simp [hρ4], ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨junkC, hjC⟩ := overlay_rec (xs.flatMap fun x => frame (binary Wb x)) (ρ2.st (UF 0))
    refine ⟨junkC, ?_⟩
    simp only [hρ4, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [hjC, ← flatMap_frame_binary]; rfl
  · rw [f4.sh (by simp [ufN]), f3.sh (by simp [ufN]), f2.sh (by simp [ufN])]; simp [hρ1]
  · rw [f4.st (by simp [ufN]), f3.st (by simp [ufN]), famUpTo_succ, ← List.append_assoc]; exact hF2.1
  · rw [f4.sh (by simp [ufN]), f3.sh (by simp [ufN]), famUpTo_succ, ← List.append_assoc]; exact hF2.2.1
  · rw [f4.val (by simp [rfN]), f3.val (by simp [rfN]), famUpTo_succ, ← List.append_assoc]; exact hF2.2.2
  · rw [f4.sh (by simp [ufN])]; exact hw3a
  · rw [f4.st (by simp [ufN])]; exact hw3b
  · obtain ⟨x, hx⟩ := h.S; exact ⟨x, f14.numOn (ninA 4 (by decide)) hx⟩
  · obtain ⟨x, hx⟩ := h.P; exact ⟨x, f14.numOn (ninA 5 (by decide)) hx⟩
  · obtain ⟨x, hx⟩ := h.E; exact ⟨x, f14.numOn (ninA 6 (by decide)) hx⟩
  · exact f14.numOn (ninA 7 (by decide)) h.one
  · exact f14.numOn (ninA 8 (by decide)) h.T
  · rw [show (j + 1) * 2 ^ V = (j + 1) * 2 ^ V from rfl]; exact f14.numOn (ninA 9 (by decide)) h.dtn
  · exact f14.numOn (ninA 10 (by decide)) h.mask
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [f14.val (rinA 0 (by decide))]; exact h.regs 0 (by decide)
    · rw [f14.val (rinA 1 (by decide))]; exact h.regs 1 (by decide)
    · rw [f14.val (rinA 2 (by decide))]; exact h.regs 2 (by decide)
    · rw [f14.val (rinA 3 (by decide))]; exact h.regs 3 (by decide)
    · rw [f14.val (rinA 4 (by decide))]; exact h.regs 4 (by decide)
    · rw [f4.val (by simp [rfN]), f3.val (by simp [rfN]), f2.val (by simp [rfN])]; simp [hρ1]
    · simp [hρ4]
    · rw [f14.val (rinA 11 (by decide))]; exact h.regs 11 (by decide)
    · rw [f14.val (rinA 12 (by decide))]; exact h.regs 12 (by decide)
    · rw [f14.val (rinA 13 (by decide))]; exact h.regs 13 (by decide)
  · rw [f14.val (rinA 10 (by decide))]; exact h.rv
  · exact SameExcept.trans h.fr (f14.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))

/-- **One level step**: from level `j` to level `j + 1`. -/
theorem famLevel_spec (cap Wb V j : ℕ) (outF L0F : List Bool) (σ0 σ : WState ns nr)
    (h : FLS UF RF Wb V j outF L0F σ0 σ) (hVW : V + 1 < Wb) (hjW : (j + 3) * 2 ^ V < 2 ^ Wb)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapV : 2 * V ≤ cap)
    (hcapN : ((level V j).length + (level V (j + 1)).length + 1) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap)
    (hcapF : (outF ++ famUpTo Wb V (j + 1)).length + 1 ≤ cap) :
    Runs cap (famLevel UF RF) σ (famLoopCost Wb V (level V j).length + 1 + famTailCost Wb (level V (j + 1)).length)
      (FLS UF RF Wb V (j + 1) outF L0F σ0) :=
  Runs.seq (famLoop_spec cap Wb V j outF L0F σ0 σ h hVW hjW hcap hcapV hcapN)
    (fun τ hτ => famTail_spec cap Wb V j outF L0F (σ.st (UF 1)) σ0 τ hτ (by omega) (by nlinarith) hcapF)

end LevelSpec

end NearCubicGates.Close.Expand
