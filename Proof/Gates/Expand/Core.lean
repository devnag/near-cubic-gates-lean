import Proof.Gates.Expand.Layout

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

/-- Non-membership of a layout stream/register in a concrete list, by indices. -/
macro "lay_ne" : tactic =>
  `(tactic| (
      simp only [evS, evR, bl, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, Fin.ext_iff, U_val,
        UF_val, MB_val, X_val, PB_val, ORC_val, O_val, R_val, RF_val, Y_val, MR_val, PG_val, PR_val, OP_val, CI_val,
        CW_val, G_val, GR_val, MS_0, MS_1, MS_2, not_or, ne_eq]
      try simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
      omega))

/-- The registers that survive the core. -/
def Keep (q : Fin NR) : Prop := q ≠ RF 8 ∧ q ≠ RF 10 ∧ q ≠ Y 0

theorem heads_after {σ τ : WState NS NR} {S : List (Fin (NS + 1))} {Rg : List (Fin NR)} (hs : ∀ i, σ.sh i = 0)
    (f : SameExcept σ τ S Rg) (hS : ∀ x ∈ S, τ.sh x = 0) : ∀ i, τ.sh i = 0 := fun i =>
  if h : i ∈ S then hS i h else by rw [f.sh h, hs i]

theorem regs_after {σ τ : WState NS NR} {S : List (Fin (NS + 1))} {Rg : List (Fin NR)}
    (hr : ∀ q, Keep q → σ.val q = 0) (f : SameExcept σ τ S Rg) (hR : ∀ q ∈ Rg, Keep q → τ.val q = 0) :
    ∀ q, Keep q → τ.val q = 0 := fun q hq =>
  if h : q ∈ Rg then hR q h hq else by rw [f.val h, hr q hq]

def core : WMX NS NR :=
  .seq (famPhase UF RF) (.seq (valPhase Lc) (.seq (mobPhase MB MS MR)
    (printPhase PB PG PR O OP ORC (MB 17) CI CW)))

/-- The core's start. -/
structure Ready (r : FormulaReq) (W Wb : ℕ) (σ : WState NS NR) : Prop where
  fs0 : FS0 UF RF Wb r.1 σ
  rd : σ.val (RF 8) = r.2.degree
  ev : ∃ t, EvAt U R Wb (2 ^ W) (2 ^ W - 1) t (frame (formulaWord r)) 0 [] σ
  rl : σ.val (Y 0) = 2 * (formulaWord r).length + 1
  mv : ∃ v0, MV MB Wb v0 σ ∧ MOK Wb v0 ∧ MConst Wb r.1 W v0 ∧ v0 17 = 0
  pb : ∃ w0, MV PB Wb w0 σ ∧ PConst r.1 W w0 ∧ ∀ j, w0 j < 2 ^ Wb
  oe : σ.st O = []
  heads : ∀ i, σ.sh i = 0
  regs : ∀ q, Keep q → σ.val q = 0

def coreCost (r : FormulaReq) (W Wb : ℕ) : ℕ :=
  famPhaseCost Wb r.1 r.2.degree (fam r.1 r.2.degree).length + 1 +
    (valPhaseCost Wb (fam r.1 r.2.degree).length (valBodyCost Wb (evalCost Wb
        (hcost Wb (tokBits r.2) (maxExp r.2) r.1) r.1 (toks r.2).length (formulaWord r).length)) + 1 +
      (mobPhaseCost Wb ((famRecs r.1 r.2.degree).map (valRec r.1 W r.2)).length (famRecs r.1 r.2.degree).length + 1 +
        printCost Wb r.1 (orcRecs r.1 W ((famRecs r.1 r.2.degree).map (valRec r.1 W r.2)) (famRecs r.1 r.2.degree)).length
          (termsWord (expandM r.2)).length))

/-- The width conditions of the core. -/
structure Widths (r : FormulaReq) (W Wb cap : ℕ) : Prop where
  wt : r.2.weight + 2 ≤ W
  wb : W ≤ Wb
  vw : r.1 + 1 < Wb
  dw : (r.2.degree + 3) * 2 ^ r.1 * 2 ^ W ≤ 2 ^ Wb
  depth : (2 ^ W) ^ ((toks r.2).length + 2) ≤ 2 ^ Wb
  cnt : (famRecs r.1 r.2.degree).length + 1 < 2 ^ Wb
  cap1 : 4 * Wb + 4 ≤ cap
  capV : 2 * r.1 ≤ cap
  capD : 2 * r.2.degree ≤ cap
  capA : ((fam r.1 r.2.degree).length + 2) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap
  capL : 2 ^ ((formulaWord r).length + 4) ≤ cap
  capO : (termsWord (expandM r.2)).length + 2 * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap

@[simp] theorem Lc_U : Lc.U = U := rfl
@[simp] theorem Lc_R : Lc.R = R := rfl
@[simp] theorem Lc_UF : Lc.UF = UF := rfl
@[simp] theorem Lc_RF : Lc.RF = RF := rfl
@[simp] theorem Lc_X : Lc.X = X := rfl
@[simp] theorem Lc_Y : Lc.Y = Y := rfl

theorem keepRF (k : Fin 14) (h8 : k ≠ 8) (h10 : k ≠ 10) : Keep (RF k) :=
  ⟨RF.injective.ne h8, RF.injective.ne h10, rne (by simp; omega)⟩

theorem valRec_lt (V W D Wb : ℕ) {V' : ℕ} (F : Formula V') (hDW : (D + 1) * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) :
    ∀ x ∈ famRecs V D, (x + 1) * 2 ^ W ≤ 2 ^ Wb ∧ valRec V W F x < 2 ^ Wb := by
  intro x hx
  have h1 := famRecs_lt V D x hx
  have h2 : (x + 1) * 2 ^ W ≤ 2 ^ Wb := le_trans (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)) hDW
  refine ⟨h2, ?_⟩
  have hf : (valAlg W (x % 2 ^ V)).eval F < 2 ^ W := (valAlg W _).eval_lt (valAlg_closed W _) F
  unfold valRec; nlinarith

/-- **The core.** -/
theorem core_spec (r : FormulaReq) (W Wb cap : ℕ) (σ : WState NS NR) (h : Ready r W Wb σ) (hw : Widths r W Wb cap) :
    Runs cap core σ (coreCost r W Wb) (fun τ => τ.st O = termsWord (expandM r.2) ∧ (∀ i, τ.sh i = 0) ∧
      (∀ q, Keep q → τ.val q = 0) ∧ τ.val (RF 8) = r.2.degree ∧ τ.val (RF 10) = r.1 ∧
      τ.val (Y 0) = 2 * (formulaWord r).length + 1) := by
  obtain ⟨V, F⟩ := r
  simp only at h hw ⊢
  set D := F.degree with hD
  have hV0 : 0 < 2 ^ V := Nat.two_pow_pos V
  have hW2 : 4 ≤ 2 ^ W := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by have := hw.wt; omega)
  have hwt : F.weight + 2 ≤ W := hw.wt
  have hvw : V + 1 < Wb := hw.vw
  have hcnt : (famRecs V D).length + 1 < 2 ^ Wb := hw.cnt
  have hcapA : ((fam V D).length + 2) * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap := hw.capA
  have hcapO : (termsWord (expandM F)).length + 2 * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap := hw.capO
  have hcap1 : 4 * Wb + 4 ≤ cap := hw.cap1
  have hdw : (D + 3) * 2 ^ V * 2 ^ W ≤ 2 ^ Wb := hw.dw
  have hP : 0 < (D + 3) * 2 ^ V := by positivity
  have hDW : (D + 3) * 2 ^ V < 2 ^ Wb := by nlinarith [Nat.mul_le_mul_left ((D + 3) * 2 ^ V) hW2]
  have hDW1 : (D + 1) * 2 ^ V * 2 ^ W ≤ 2 ^ Wb := le_trans (by gcongr; omega) hdw
  have hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb := le_trans (by gcongr; omega) hdw
  have hWlt : 2 ^ W < 2 ^ Wb := by nlinarith [Nat.mul_le_mul_right (2 ^ W) (show 1 ≤ (D + 3) * 2 ^ V by omega)]
  -- 1. the family phase
  refine Runs.seq (famPhase_spec cap Wb V D σ h.fs0 h.rd (h.regs _ (keepRF 9 (by decide) (by decide))) hvw hDW
    hcap1 hw.capV hw.capD hcapA) (fun τ1 h1 => ?_)
  obtain ⟨hF, hRD1, hRD21⟩ := h1
  -- 2. the values phase
  obtain ⟨t, hEt⟩ := h.ev
  have nUF : ∀ i, U i ∉ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9] := by
    intro i; have := i.isLt; lay_ne
  have nRF : ∀ j, R j ∉ [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13] := by
    intro j; have := j.isLt; lay_ne
  have kY : ∀ k : Fin 8, k ≠ 0 → Keep (Y k) := fun k hk =>
    ⟨rne (by simp; omega), rne (by simp; omega), Y.injective.ne hk⟩
  have kR : ∀ j : Fin 12, Keep (R j) := fun j => ⟨rne (by have := j.isLt; simp; omega),
    rne (by have := j.isLt; simp; omega), rne (by have := j.isLt; simp; omega)⟩
  have nYRF : ∀ k : Fin 8, Y k ∉ [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13] := by
    intro k; have := k.isLt; lay_ne
  have hX0 : X 0 ∉ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9] := by lay_ne
  refine Runs.seq (valPhase_spec (L := Lc) cap Wb W V D ⟨V, F⟩ τ1
    ⟨t, by simpa using hEt.transport hF.fr nUF nRF⟩
    (by simp; rw [hF.fr.val (nRF 11)]; exact h.regs _ (kR 11))
    (by simp; rw [hF.fr.val (nYRF 0)]; exact h.rl)
    (by simp; rw [hF.fr.val (nYRF 1)]; exact h.regs _ (kY 1 (by decide)))
    (by simpa using hF.fam) (by simpa using hF.famh)
    (by simpa using hF.regs 2 (by decide)) (by simpa using hF.regs 3 (by decide))
    (by simpa using hF.wkh) (by simpa using hF.wkl) (by simpa using hF.P) (by simpa using hF.E)
    (by simpa using hF.regs 0 (by decide)) (by simpa using hF.regs 1 (by decide))
    (by simpa using hF.regs 4 (by decide)) (by simpa using hF.regs 11 (by decide))
    (by simpa using hF.mask) (by simp; rw [hF.fr.sh hX0]; exact h.heads _)
    (by simp; rw [hF.fr.val (nYRF 2)]; exact h.regs _ (kY 2 (by decide)))
    ⟨by omega, hw.wb⟩ (by omega) hWlt hDW1 hw.depth (by omega) hw.capL
    (by nlinarith)) (fun τ2 h2 => ?_)
  -- 3. the Möbius phase
  obtain ⟨v0, hmv, hok, hc, h17⟩ := h.mv
  have nMB1 : ∀ i, MB i ∉ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9] := by
    intro i; have := i.isLt; lay_ne
  have nMB2 : ∀ i, MB i ∉ (U 9 :: UF 3 :: UF 2 :: UF 5 :: UF 6 :: X 0 :: evS U) := by
    intro i; have := i.isLt; lay_ne
  have hv2 := h2.fr
  simp only [Lc_U, Lc_R, Lc_UF, Lc_RF, Lc_X, Lc_Y] at hv2
  set vals := (famRecs V D).map (valRec V W F) with hvals
  have hvl := valRec_lt V W D Wb F hDW1
  obtain ⟨junkV, hjV⟩ := h2.val
  obtain ⟨junkF, hjF⟩ := hF.fam
  have nORC1 : ORC ∉ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9] := by lay_ne
  have nORC2 : ORC ∉ (U 9 :: UF 3 :: UF 2 :: UF 5 :: UF 6 :: X 0 :: evS U) := by lay_ne
  have nMR1 : ∀ k, MR k ∉ [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13] := by
    intro k; have := k.isLt; lay_ne
  have nMR2 : ∀ k, MR k ∉ (RF 0 :: RF 1 :: RF 2 :: RF 3 :: RF 11 :: Y 2 :: (evR R ++ [R 11])) := by
    intro k; have := k.isLt; lay_ne
  have kMR : ∀ k, Keep (MR k) := fun k => ⟨rne (by have := k.isLt; simp; omega),
    rne (by have := k.isLt; simp; omega), rne (by have := k.isLt; simp; omega)⟩
  refine Runs.seq (mobPhase_spec (MB := MB) (MS := MS) (MR := MR) cap Wb V W hMS vals (famRecs V D)
    (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact (hvl y hy).2)
    (fun x hx => (hvl x hx).1) junkV junkF τ2 v0 ((hmv.frame' hF.fr nMB1).frame' hv2 nMB2) hok hc
    (by rw [MS_1]; simpa [hvals, List.map_map, Function.comp_def] using hjV)
    (by rw [MS_1]; simpa using h2.valh)
    (by rw [MS_0]; have := h2.famst; simp only [Lc_UF] at this; rw [this, hjF])
    (by rw [MS_0]; simpa using h2.famh)
    (by rw [MS_2, hv2.sh nORC2, hF.fr.sh nORC1]; exact h.heads _)
    (fun k => by rw [hv2.val (nMR2 k), hF.fr.val (nMR1 k)]; exact h.regs _ (kMR k))
    (by omega) hTW (by rw [h17]; omega) (by omega)
    (by simp only [hvals, List.length_map, famRecs_length]; nlinarith)
    (by simp only [famRecs_length]; nlinarith)) (fun τ3 h3 => ?_)
  obtain ⟨w3, hw3, w17, ⟨junkO, hjO⟩, horch, hMR3, fr3, hms0, hms1⟩ := h3
  -- 4. the print phase
  set orc := orcRecs V W vals (famRecs V D) with horc
  have hop := orc_print F W hw.wt
  rw [← hD] at hop
  have horcl : orc.length ≤ (famRecs V D).length := by
    rw [horc]; unfold orcRecs; exact List.length_filterMap_le _ _
  have hSall : ∀ x : Fin (NS + 1), x ∉ [UF 0, UF 1, UF 2, UF 3, UF 4, UF 5, UF 6, UF 9] →
      x ∉ (U 9 :: UF 3 :: UF 2 :: UF 5 :: UF 6 :: X 0 :: evS U) →
      x ∉ [MB 0, MB 1, MB 2, MB 3, MB 4, MB 5, MB 6, MB 7, MB 8, MB 9, MB 17, MS 0, MS 1, MS 2] →
      τ3.st x = σ.st x ∧ τ3.sh x = σ.sh x := fun x h1 h2' h3 =>
    ⟨by rw [fr3.st h3, hv2.st h2', hF.fr.st h1], by rw [fr3.sh h3, hv2.sh h2', hF.fr.sh h1]⟩
  have hRall : ∀ q : Fin NR, q ∉ [RF 0, RF 1, RF 2, RF 3, RF 4, RF 5, RF 6, RF 7, RF 10, RF 11, RF 12, RF 13] →
      q ∉ (RF 0 :: RF 1 :: RF 2 :: RF 3 :: RF 11 :: Y 2 :: (evR R ++ [R 11])) →
      q ∉ [MR 0, MR 3, MR 4, MR 5, MR 8] → τ3.val q = σ.val q := fun q h1 h2' h3 => by
    rw [fr3.val h3, hv2.val h2', hF.fr.val h1]
  have zreg : ∀ q : Fin NR, 43 ≤ q.val → q.val ≤ 54 → τ3.val q = 0 := by
    intro q h1 h2'
    rw [hRall q (by lay_ne) (by lay_ne) (by lay_ne)]
    exact h.regs q ⟨rne (by simp; omega), rne (by simp; omega), rne (by simp; omega)⟩
  have sPB : ∀ x : Fin (NS + 1), 45 ≤ x.val → x.val ≤ 59 → τ3.st x = σ.st x ∧ τ3.sh x = σ.sh x := by
    intro x h1 h2'
    exact hSall x (by lay_ne) (by lay_ne) (by lay_ne)
  obtain ⟨w0, hw0, hc0, hok0⟩ := h.pb
  have hw0' : MV PB Wb w0 τ3 := fun i => by
    have := sPB (PB i) (by simp) (by simp; omega)
    exact ⟨by rw [this.1, (hw0 i).1], by rw [this.2, (hw0 i).2]⟩
  have hcntl : w3 17 = orc.length := by rw [w17, h17, zero_add]
  have hcntlt : orc.length < 2 ^ Wb := by omega
  have hLo : (natWord orc.length ++ orc.flatMap (recOut V W)).length = (termsWord (expandM F)).length := by
    rw [hop.1, hop.2]; rfl
  refine (printPhase_spec pplay V W τ3 w0 hw0' hc0 hok0 orc.length
    (by rw [← hcntl]; exact hw3 17) hcntlt orc junkO (by rw [← MS_2]; exact hjO) (by rw [← MS_2]; exact horch)
    (zreg CI (by simp) (by simp)) (zreg CW (by simp) (by simp)) (by rw [(sPB O (by simp) (by simp)).1, h.oe])
    (by rw [(sPB O (by simp) (by simp)).2, h.heads]) (zreg OP (by simp) (by simp))
    (fun k => zreg (PG k) (by simp) (by simp; omega)) (fun k => zreg (PR k) (by simp; omega) (by simp; omega))
    (by
      intro x hx
      rw [horc] at hx; unfold orcRecs at hx
      obtain ⟨y, hy, hxy⟩ := List.mem_filterMap.mp hx
      split_ifs at hxy with h0
      cases hxy
      have := (hvl y hy).1
      have := accOf_lt V W vals y
      nlinarith)
    hTW (by omega) (termsWord (expandM F)).length (le_of_eq hLo) (by omega) hcapO
    (by
      rw [famRecs_length] at horcl
      have h1 := Nat.mul_le_mul_right (2 * Wb + 1) horcl
      have h2 : ((fam V D).length + 2) * (2 * Wb + 1) = (fam V D).length * (2 * Wb + 1) + 2 * (2 * Wb + 1) := by ring
      omega)).post (fun τ4 h4 => ?_)
  obtain ⟨hO4, hOh4, ⟨w4, hw4⟩, fr4⟩ := h4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hO4, hop.1, hop.2]; rfl
  · refine heads_after (heads_after (heads_after (heads_after h.heads hF.fr ?_) hv2 ?_) fr3 ?_) fr4 ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact hF.curh
      · exact hF.nxth
      · exact hF.famh
      · exact hF.wkh
      · obtain ⟨_, hx⟩ := hF.S; exact hx.2
      · obtain ⟨_, hx⟩ := hF.P; exact hx.2
      · obtain ⟨_, hx⟩ := hF.E; exact hx.2
      · obtain ⟨_, hx⟩ := hF.DT; exact hx.2
    · obtain ⟨t2, he2⟩ := h2.ev
      simp only [evS, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact he2.ev.pt.2
      · simpa using h2.wkh
      · simpa using h2.famh
      · obtain ⟨_, hx⟩ := h2.n5; exact hx.2
      · obtain ⟨_, hx⟩ := h2.n6; exact hx.2
      · simpa using h2.valh
      · exact he2.hd
      · exact he2.stk.2
      · obtain ⟨_, hx⟩ := he2.ev.num 2 (by decide); exact hx.2
      · obtain ⟨_, hx⟩ := he2.ev.num 3 (by decide); exact hx.2
      · obtain ⟨_, hx⟩ := he2.ev.num 4 (by decide); exact hx.2
      · obtain ⟨_, hx⟩ := he2.ev.num 5 (by decide); exact hx.2
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals first | exact (hw3 _).2 | exact hms0 | exact hms1 | exact horch
    · simp only [bl, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals first | exact hOh4 | exact (hw4 _).2
  · refine regs_after (regs_after (regs_after (regs_after h.regs hF.fr ?_) hv2 ?_) fr3 ?_) fr4 (by simp)
    · intro q hq hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hF.regs _ (by decide) | exact absurd rfl hk.2.1
    · obtain ⟨t2, he2⟩ := h2.ev
      intro q hq hk
      simp only [evR, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      · exact h2.regs.1
      · exact h2.regs.2.1
      · exact h2.ci
      · exact h2.cw
      · exact h2.regs.2.2.2
      · exact h2.cv
      all_goals first | exact he2.ev.zero _ (by decide) | exact h2.r11
    · intro q hq _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact hMR3 _
  · rw [fr4.val (by simp), fr3.val (by lay_ne), hv2.val (by lay_ne)]; exact hRD1
  · rw [fr4.val (by simp), fr3.val (by lay_ne), hv2.val (by lay_ne)]; exact hF.rv
  · rw [fr4.val (by simp), fr3.val (by lay_ne)]; simpa using h2.rl

end NearCubicGates.Close.Expand.Layout
