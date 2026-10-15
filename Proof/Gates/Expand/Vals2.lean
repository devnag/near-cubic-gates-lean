import Proof.Gates.Expand.Vals

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
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

theorem famRecs_lt (V D : ℕ) : ∀ x ∈ famRecs V D, x < (D + 1) * 2 ^ V := by
  intro x hx
  simp only [famRecs, List.mem_flatMap, List.mem_range] at hx
  obtain ⟨d, hd, hx⟩ := hx
  have := lvlRecs_lt V d x hx
  exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ (by omega))

section Phase
variable {L : Lay ns nr}

/-- The loop invariant of the values phase. -/
def VInv (L : Lay ns nr) (Wb W V : ℕ) {V' : ℕ} (F : Formula V') (inp : List Bool) (rl : ℕ) (xs : List ℕ)
    (L0 : List Bool) (σ0 : WState ns nr) (i : ℕ) (τ : WState ns nr) : Prop :=
  (∃ t, EvAt L.U L.R Wb (2 ^ W) (2 ^ W - 1) t inp 0 [] τ) ∧ τ.val (L.R 11) = 0 ∧ τ.val (L.Y 0) = rl ∧
    τ.val (L.Y 1) = 0 ∧ (∃ x, NumOn τ (L.UF 5) Wb x) ∧ (∃ x, NumOn τ (L.UF 6) Wb x) ∧
    τ.val (L.RF 0) = 0 ∧ τ.val (L.RF 1) = 0 ∧ τ.val (L.RF 4) = 0 ∧ τ.val (L.RF 11) = 0 ∧
    OutOn τ (L.X 0) (L.Y 2) ((xs.take i).flatMap fun x => frame (binary Wb (valRec V W F x))) L0 ∧
    τ.sh (L.UF 3) = 0 ∧ (τ.st (L.UF 3)).length ≤ 2 * Wb + 1 ∧
    SameExcept σ0 τ (L.U 9 :: L.UF 3 :: L.UF 2 :: L.UF 5 :: L.UF 6 :: L.X 0 :: evS L.U)
      (L.RF 0 :: L.RF 1 :: L.RF 2 :: L.RF 3 :: L.RF 11 :: L.Y 2 :: (evR L.R ++ [L.R 11]))

theorem len_frames_g (Wb : ℕ) (g : ℕ → ℕ) (xs : List ℕ) :
    (xs.flatMap fun x => frame (binary Wb (g x))).length = xs.length * (2 * Wb + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih, frame_length]; ring

theorem EvAt.transport {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr} {Wb m k t hd : ℕ} {inp : List Bool}
    {xs : List ℕ} {σ τ : WState ns nr} {S : List (Fin (ns + 1))} {Rg : List (Fin nr)}
    (h : EvAt U R Wb m k t inp hd xs σ) (f : SameExcept σ τ S Rg) (hS : ∀ i, U i ∉ S) (hR : ∀ j, R j ∉ Rg) :
    EvAt U R Wb m k t inp hd xs τ :=
  ⟨⟨fun i hi => by obtain ⟨x, hx⟩ := h.ev.num i hi; exact ⟨x, f.numOn (hS i) hx⟩, f.numOn (hS 6) h.ev.mm,
    f.numOn (hS 7) h.ev.km, f.numOn (hS 8) h.ev.one, f.numOn (hS 9) h.ev.pt,
    fun j hj => by rw [f.val (hR j)]; exact h.ev.zero j hj⟩,
    by rw [f.st (hS 0)]; exact h.inp, by rw [f.sh (hS 0)]; exact h.hd, f.numOn (hS 1) h.stk⟩

theorem valBodyJ (cap Wb W V D : ℕ) (r : FormulaReq) (rl : ℕ) (L0 junk : List Bool) (σ0 : WState ns nr)
    (hMk : NumOn σ0 (L.UF 10) Wb (2 ^ V - 1)) (hrl : rl = 2 * (formulaWord r).length + 1)
    (hW : VOK Wb W) (hVW : V < Wb) (hWlt : 2 ^ W < 2 ^ Wb) (hDW : (D + 1) * 2 ^ V * 2 ^ W ≤ 2 ^ Wb)
    (hdepth : (2 ^ W) ^ ((toks r.2).length + 2) ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapL : 2 ^ ((formulaWord r).length + 4) ≤ cap)
    (hcapO : ((fam V D).length + 1) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    BodySpecJ cap Wb (I := L.UF 2) (Wk := L.UF 3) (CI := L.RF 2) (CW := L.RF 3) (valBody L)
      ((famRecs V D).map (binary Wb)) (VInv L Wb W V r.2 (frame (formulaWord r)) rl (famRecs V D) L0 σ0)
      (fun _ => valBodyCost Wb (evalCost Wb (hcost Wb (tokBits r.2) (maxExp r.2) r.1) r.1 (toks r.2).length
        (formulaWord r).length)) junk := by
  intro i hi τ hτ _ _ _ _ hwh _
  obtain ⟨⟨t, hE⟩, h11, hRL, hRL2, h5, h6, hR0, hR1, hR4, hR11, hO, -, -, hfr⟩ := hτ
  have hil : i < (famRecs V D).length := by simpa using hi
  set rec := (famRecs V D)[i] with hrecd
  have hwsi : ((famRecs V D).map (binary Wb))[i] = binary Wb rec := by simp [hrecd]
  set τa := atRec (L.UF 2) (L.UF 3) (L.RF 2) τ ((famRecs V D).map (binary Wb))[i] ((i + 1) * (2 * Wb + 1)) with hτa
  have fa : SameExcept τ τa [L.UF 2, L.UF 3] [L.RF 2] := by
    rw [hτa]; unfold atRec
    exact SameExcept.trans (SameExcept.trans (sameExcept_sets τ (by simp) _) (sameExcept_seth _ (by simp) _))
      (sameExcept_setv _ (by simp) _)
  have nU : ∀ k : Fin 10, L.U k ∉ [L.UF 2, L.UF 3] := by
    intro k hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm <;> exact L.dUUF _ _ hm
  have nR : ∀ k : Fin 12, L.R k ∉ [L.RF 2] := by
    intro k hm; simp only [List.mem_singleton] at hm; exact L.dRRF _ _ hm
  have nRF : ∀ k : Fin 14, k ≠ 2 → L.RF k ∉ [L.RF 2] := by
    intro k hk hm; simp only [List.mem_singleton] at hm; exact hk (L.RF.injective hm)
  have nY : ∀ k : Fin 8, L.Y k ∉ [L.RF 2] := by
    intro k hm; simp only [List.mem_singleton] at hm; exact L.dRFY _ _ hm.symm
  have nUF : ∀ k : Fin 12, k ≠ 2 → k ≠ 3 → L.UF k ∉ [L.UF 2, L.UF 3] := by
    intro k h2 h3 hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm <;> have := L.UF.injective hm <;> simp_all
  have nX : ∀ k : Fin 4, L.X k ∉ [L.UF 2, L.UF 3] := by
    intro k hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm <;> exact L.dUFX _ _ hm.symm
  have hWK : NumOn τa (L.UF 3) Wb rec := by
    refine ⟨?_, ?_⟩
    · simp only [hτa, atRec, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]; rw [hwsi]
    · simp [hτa, atRec, Function.update_of_ne (L.ufN (by decide : (3 : Fin 12) ≠ 2)), hwh]
  have hrec : (rec + 1) * 2 ^ W ≤ 2 ^ Wb := by
    have := famRecs_lt V D rec (List.getElem_mem hil)
    have h2 : (rec + 1) * 2 ^ W ≤ (D + 1) * 2 ^ V * 2 ^ W := Nat.mul_le_mul_right _ (by omega)
    omega
  have hMa : NumOn τa (L.UF 10) Wb (2 ^ V - 1) := by
    refine fa.numOn (nUF 10 (by decide) (by decide)) (hfr.numOn ?_ hMk)
    intro hm; simp only [List.mem_cons, evS, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
    · exact L.dUUF _ _ hm.symm
    all_goals first | exact absurd (L.UF.injective hm) (by decide) | exact L.dUFX _ _ hm | exact L.dUUF _ _ hm.symm
  have hlenPre : (((famRecs V D).take i).flatMap fun x => frame (binary Wb (valRec V W r.2 x))).length + 2 * Wb + 2
      ≤ cap := by
    rw [len_frames_g, List.length_take, famRecs_length]
    have : min i (fam V D).length ≤ (fam V D).length := min_le_right _ _
    nlinarith
  have fS : ∀ k : Fin 10, L.U k ∉ [L.UF 2, L.UF 3] := nU
  have hEa := hE.transport fa fS nR
  have hvb := valBody_spec (L := L) cap Wb W V r rec _ L0 τa ⟨t, hEa⟩ (by rw [fa.val (nR 11)]; exact h11)
    (by rw [fa.val (nY 0), hRL, hrl]) (by rw [fa.val (nY 1)]; exact hRL2) hWK hMa
    (by obtain ⟨x, hx⟩ := h5; exact ⟨x, fa.numOn (nUF 5 (by decide) (by decide)) hx⟩)
    (by obtain ⟨x, hx⟩ := h6; exact ⟨x, fa.numOn (nUF 6 (by decide) (by decide)) hx⟩)
    (by rw [fa.val (nRF 0 (by decide))]; exact hR0) (by rw [fa.val (nRF 1 (by decide))]; exact hR1)
    (by rw [fa.val (nRF 4 (by decide))]; exact hR4) (by rw [fa.val (nRF 11 (by decide))]; exact hR11)
    ⟨by rw [fa.st (nX 0)]; exact hO.1, by rw [fa.sh (nX 0)]; exact hO.2.1, by rw [fa.val (nY 2)]; exact hO.2.2⟩
    hW hVW hWlt hrec hdepth hcap hcapL hlenPre
  obtain ⟨τ', hrun, ⟨t', hE'⟩, h11', hRL', hRL2', h5', h6', hR0', hR1', hR4', hR11', hO', hfr'⟩ := hvb
  have nWK : L.UF 3 ∉ L.U 9 :: L.UF 5 :: L.UF 6 :: L.X 0 :: evS L.U := by
    intro hm; simp only [List.mem_cons, evS, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
    all_goals first | exact absurd (L.UF.injective hm) (by decide) | exact L.dUFX _ _ hm | exact L.dUUF _ _ hm.symm
  have nFAM : L.UF 2 ∉ L.U 9 :: L.UF 5 :: L.UF 6 :: L.X 0 :: evS L.U := by
    intro hm; simp only [List.mem_cons, evS, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
    all_goals first | exact absurd (L.UF.injective hm) (by decide) | exact L.dUFX _ _ hm | exact L.dUUF _ _ hm.symm
  have nCI : ∀ k : Fin 14, k = 2 ∨ k = 3 → L.RF k ∉ L.RF 0 :: L.RF 1 :: L.RF 11 :: L.Y 2 :: (evR L.R ++ [L.R 11]) := by
    intro k hk hm
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm
    · have := L.RF.injective hm; rcases hk with rfl | rfl <;> simp at this
    · have := L.RF.injective hm; rcases hk with rfl | rfl <;> simp at this
    · have := L.RF.injective hm; rcases hk with rfl | rfl <;> simp at this
    · exact L.dRFY _ _ hm
    · exact L.notMem_evR k (List.mem_append_left _ hm)
    · exact L.notMem_evR k (List.mem_append_right _ (by simp [hm]))
  have hwk' : τ'.sh (L.UF 3) = 0 := by
    rw [hfr'.sh nWK]; simp [hτa, atRec, Function.update_of_ne (L.ufN (by decide : (3 : Fin 12) ≠ 2)), hwh]
  have hwl' : (τ'.st (L.UF 3)).length ≤ 2 * Wb + 1 := by rw [hfr'.st nWK, hWK.1]; simp [frame_length]
  refine ⟨τ', hrun, ⟨⟨t', hE'⟩, h11', by rw [hRL', fa.val (nY 0)]; exact hRL, hRL2', h5', h6', hR0', hR1', hR4', hR11', ?_,
    hwk', hwl', ?_⟩, ⟨hfr'.st nFAM, hfr'.sh nFAM, hfr'.val (nCI 2 (Or.inl rfl)), hfr'.val (nCI 3 (Or.inr rfl)), hwk', hwl'⟩⟩
  · rw [WordPrograms.flatMap_take_succ' _ _ i hil]; exact hO'
  · refine SameExcept.trans (SameExcept.trans hfr (se_sub fa (by simp [List.cons_subset]) (by simp [List.cons_subset])))
      (se_sub hfr' ?_ ?_)
    · intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
    · intro x hx; simp only [List.mem_cons] at hx ⊢; tauto

/-- The values phase's result. -/
structure VDone (L : Lay ns nr) (Wb W V D : ℕ) {V' : ℕ} (F : Formula V') (inp : List Bool) (rl : ℕ)
    (σ0 σ : WState ns nr) : Prop where
  ev : ∃ t, EvAt L.U L.R Wb (2 ^ W) (2 ^ W - 1) t inp 0 [] σ
  r11 : σ.val (L.R 11) = 0
  rl : σ.val (L.Y 0) = rl
  rl2 : σ.val (L.Y 1) = 0
  val : ∃ junk, σ.st (L.X 0) = recStream ((famRecs V D).map fun x => binary Wb (valRec V W F x)) ++ junk
  valh : σ.sh (L.X 0) = 0
  cv : σ.val (L.Y 2) = 0
  fr : SameExcept σ0 σ (L.U 9 :: L.UF 3 :: L.UF 2 :: L.UF 5 :: L.UF 6 :: L.X 0 :: evS L.U)
      (L.RF 0 :: L.RF 1 :: L.RF 2 :: L.RF 3 :: L.RF 11 :: L.Y 2 :: (evR L.R ++ [L.R 11]))
  wkh : σ.sh (L.UF 3) = 0
  wkl : (σ.st (L.UF 3)).length ≤ 2 * Wb + 1
  famh : σ.sh (L.UF 2) = 0
  ci : σ.val (L.RF 2) = 0
  cw : σ.val (L.RF 3) = 0
  n5 : ∃ x, NumOn σ (L.UF 5) Wb x
  n6 : ∃ x, NumOn σ (L.UF 6) Wb x
  regs : σ.val (L.RF 0) = 0 ∧ σ.val (L.RF 1) = 0 ∧ σ.val (L.RF 4) = 0 ∧ σ.val (L.RF 11) = 0
  famst : σ.st (L.UF 2) = σ0.st (L.UF 2)

def valPhaseCost (Wb N c : ℕ) : ℕ := (N * (c + (50 * Wb + 30)) + 3) + 1 + (5 * (N * (2 * Wb + 1)) + 3)

theorem valPhase_spec (cap Wb W V D : ℕ) (r : FormulaReq) (σ : WState ns nr)
    (hE : ∃ t, EvAt L.U L.R Wb (2 ^ W) (2 ^ W - 1) t (frame (formulaWord r)) 0 [] σ) (h11 : σ.val (L.R 11) = 0)
    (hRL : σ.val (L.Y 0) = 2 * (formulaWord r).length + 1) (hRL2 : σ.val (L.Y 1) = 0)
    (hFAM : ∃ junk, σ.st (L.UF 2) = recStream ((famRecs V D).map (binary Wb)) ++ junk) (hFh : σ.sh (L.UF 2) = 0)
    (hCI : σ.val (L.RF 2) = 0) (hCW : σ.val (L.RF 3) = 0) (hwh : σ.sh (L.UF 3) = 0)
    (hwl : (σ.st (L.UF 3)).length ≤ 2 * Wb + 1)
    (h5 : ∃ x, NumOn σ (L.UF 5) Wb x) (h6 : ∃ x, NumOn σ (L.UF 6) Wb x)
    (hR0 : σ.val (L.RF 0) = 0) (hR1 : σ.val (L.RF 1) = 0) (hR4 : σ.val (L.RF 4) = 0) (hR11 : σ.val (L.RF 11) = 0)
    (hMk : NumOn σ (L.UF 10) Wb (2 ^ V - 1)) (hVh : σ.sh (L.X 0) = 0) (hCV : σ.val (L.Y 2) = 0)
    (hW : VOK Wb W) (hVW : V < Wb) (hWlt : 2 ^ W < 2 ^ Wb) (hDW : (D + 1) * 2 ^ V * 2 ^ W ≤ 2 ^ Wb)
    (hdepth : (2 ^ W) ^ ((toks r.2).length + 2) ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapL : 2 ^ ((formulaWord r).length + 4) ≤ cap)
    (hcapO : ((fam V D).length + 1) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    Runs cap (valPhase L) σ (valPhaseCost Wb (fam V D).length (valBodyCost Wb (evalCost Wb
        (hcost Wb (tokBits r.2) (maxExp r.2) r.1) r.1 (toks r.2).length (formulaWord r).length)))
      (VDone L Wb W V D r.2 (frame (formulaWord r)) (2 * (formulaWord r).length + 1) σ) := by
  obtain ⟨junk, hFst⟩ := hFAM
  set L0 := σ.st (L.X 0) with hL0
  have hb := valBodyJ (L := L) cap Wb W V D r (2 * (formulaWord r).length + 1) L0 junk σ hMk rfl hW hVW hWlt hDW
    hdepth hcap hcapL hcapO
  have hw : ∀ w ∈ (famRecs V D).map (binary Wb), w.length = Wb := by
    intro w hw; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw; simp
  have hlen : ((famRecs V D).map (binary Wb)).length = (fam V D).length := by simp [famRecs_length]
  have hInv0 : VInv L Wb W V r.2 (frame (formulaWord r)) (2 * (formulaWord r).length + 1) (famRecs V D) L0 σ 0 σ :=
    ⟨hE, h11, hRL, hRL2, h5, h6, hR0, hR1, hR4, hR11, ⟨by simp [hL0, overlay], by simpa using hVh, by simpa using hCV⟩,
      hwh, hwl, SameExcept.refl _ _ _⟩
  obtain ⟨τ, hInvN, hst, hcw, hloop⟩ := recLoopJ_spec (cap := cap) (L := Wb) (L.ufN (by decide : (2 : Fin 12) ≠ 3))
    (L.rfN (by decide : (2 : Fin 14) ≠ 3)) hw (by omega) (by rw [hlen]; nlinarith) hb σ hInv0 hFst hFh hCI hCW hwh hwl
  rw [hlen] at hInvN hloop
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
  obtain ⟨hEN, h11N, hRLN, hRL2N, h5N, h6N, hR0N, hR1N, hR4N, hR11N, hON, hwkN, hwlN, hfrN⟩ := hInvN
  rw [show (famRecs V D).take (fam V D).length = famRecs V D by rw [← famRecs_length, List.take_length]] at hON
  refine Runs.seq ⟨_, hloop, rfl⟩ (fun ρ hρ => ?_)
  subst hρ
  set ρ1 := (τ.setv (L.RF 2) 0).seth (L.UF 2) 0 with hρ1
  have f1 : SameExcept τ ρ1 [L.UF 2] [L.RF 2] := by
    rw [hρ1]; exact SameExcept.trans (sameExcept_setv _ (by simp) _) (sameExcept_seth _ (by simp) _)
  have hO1 : OutOn ρ1 (L.X 0) (L.Y 2) ((famRecs V D).flatMap fun x => frame (binary Wb (valRec V W r.2 x))) L0 :=
    ⟨by rw [f1.st (by simp [L.dUFX 2 0, (L.dUFX 2 0).symm])]; exact hON.1,
      by rw [f1.sh (by simp [(L.dUFX 2 0).symm])]; exact hON.2.1,
      by rw [f1.val (by simp [(L.dRFY 2 2).symm])]; exact hON.2.2⟩
  refine (closeNum cap ρ1 _ L0 hO1 (by rw [len_frames_g, famRecs_length]; nlinarith)).mono
    (by rw [len_frames_g, famRecs_length]) (fun ρ2 ⟨hst2, hsh2, hcv2, f2⟩ => ?_)
  have nX : ∀ k : Fin 12, L.UF k ∉ [L.X 0] := by
    intro k hm; simp only [List.mem_singleton] at hm; exact L.dUFX k 0 hm
  have nU : ∀ k : Fin 10, L.U k ∉ [L.UF 2] := by
    intro k hm; simp only [List.mem_singleton] at hm; exact L.dUUF k 2 hm
  have nU2 : ∀ k : Fin 10, L.U k ∉ [L.X 0] := by
    intro k hm; simp only [List.mem_singleton] at hm; exact L.dUX k 0 hm
  have nR1 : ∀ k : Fin 12, L.R k ∉ [L.RF 2] := by
    intro k hm; simp only [List.mem_singleton] at hm; exact L.dRRF k 2 hm
  have nR2 : ∀ k : Fin 12, L.R k ∉ [L.Y 2] := by
    intro k hm; simp only [List.mem_singleton] at hm; exact L.dRY k 2 hm
  obtain ⟨t, hEt⟩ := hEN
  refine ⟨⟨t, (hEt.transport f1 nU nR1).transport f2 nU2 nR2⟩, ?_, ?_, ?_, ?_, hsh2, hcv2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [f2.val (nR2 11), f1.val (nR1 11)]; exact h11N
  · rw [f2.val (by simp [(L.Y.injective.ne (by decide : (0 : Fin 8) ≠ 2))]),
      f1.val (by simp [(L.dRFY 2 0).symm])]; exact hRLN
  · rw [f2.val (by simp [(L.Y.injective.ne (by decide : (1 : Fin 8) ≠ 2))]),
      f1.val (by simp [(L.dRFY 2 1).symm])]; exact hRL2N
  · obtain ⟨jk, hj⟩ := overlay_rec ((famRecs V D).flatMap fun x => frame (binary Wb (valRec V W r.2 x))) L0
    refine ⟨jk, ?_⟩
    rw [hst2, hj]; simp [recStream, List.flatMap_map]
  · exact SameExcept.trans (SameExcept.trans hfrN (se_sub f1 (by simp [List.cons_subset]) (by simp [List.cons_subset])))
      (se_sub f2 (by simp [List.cons_subset]) (by simp [List.cons_subset]))
  · rw [f2.sh (nX 3), f1.sh (by simp [L.ufN (by decide : (3 : Fin 12) ≠ 2)])]; exact hwkN
  · rw [f2.st (nX 3), f1.st (by simp [L.ufN (by decide : (3 : Fin 12) ≠ 2)])]; exact hwlN
  · rw [f2.sh (nX 2)]; simp [hρ1]
  · rw [f2.val (by simp [L.dRFY 2 2])]; simp [hρ1]
  · rw [f2.val (by simp [L.dRFY 3 2]), f1.val (by simp [L.rfN (by decide : (3 : Fin 14) ≠ 2)])]; exact hcw
  · obtain ⟨x, hx⟩ := h5N; exact ⟨x, f2.numOn (nX 5) (f1.numOn (by simp [L.ufN (by decide : (5 : Fin 12) ≠ 2)]) hx)⟩
  · obtain ⟨x, hx⟩ := h6N; exact ⟨x, f2.numOn (nX 6) (f1.numOn (by simp [L.ufN (by decide : (6 : Fin 12) ≠ 2)]) hx)⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [f2.val (by simp [L.dRFY 0 2]), f1.val (by simp [L.rfN (by decide : (0 : Fin 14) ≠ 2)])]; exact hR0N
    · rw [f2.val (by simp [L.dRFY 1 2]), f1.val (by simp [L.rfN (by decide : (1 : Fin 14) ≠ 2)])]; exact hR1N
    · rw [f2.val (by simp [L.dRFY 4 2]), f1.val (by simp [L.rfN (by decide : (4 : Fin 14) ≠ 2)])]; exact hR4N
    · rw [f2.val (by simp [L.dRFY 11 2]), f1.val (by simp [L.rfN (by decide : (11 : Fin 14) ≠ 2)])]; exact hR11N
  · rw [f2.st (nX 2), hρ1]; simp [hst, hFst]

end Phase

end NearCubicGates.Close.Expand
