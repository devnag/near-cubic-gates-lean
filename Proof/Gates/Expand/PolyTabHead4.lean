import Proof.Gates.Expand.PolyTabHead3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicWires.RepairRepresentation (natWord)
open StablePartition.Workspace (overlay)
open NearCubicWires.RepairRepresentation

variable (E : ExpandMachine) (a : WilliamsAlgorithm)

local notation "WSE" => WState (NSx (te E) (Qa a)) NRk

/-- The request table's records. -/
def TBk (r : TabReq) : List Bool := recStream (((preN r).map (· % 2 ^ (Wk E r + 1))).map (binary (Wk E r + 1)))

/-- After the request table. -/
structure BMid1 (r : TabReq) (g : Fin 64 → ℕ) (ρ τ : WSE) : Prop where
  ev : ∃ v : Fin 10 → ℕ, EvV U0 RB (Wk E r + 1) (frame (tabWord r)) (encN (preN r)).length 0 v τ ∧ v 8 = 1 ∧ v 3 = 0 ∧
    v 4 = 0 ∧ v 9 = 0
  s3 : τ.st (sS 3) = TBk E r
  s3h : τ.sh (sS 3) = 0
  rx : ∀ j : Fin 64, j.val < 52 → j.val ∉ [9, 39] → τ.val (rX j) = g j
  r9 : τ.val (rX 9) = 0
  r39 : τ.val (rX 39) = 0
  fr : SameExcept ρ τ (sS 3 :: sS 0 :: List.ofFn ubv) RXL

theorem rB_ne_RB (j : Fin 12) (k : Fin 64) (hk : k.val < 52) : RB j ≠ rX k := RB_ne j k hk

theorem phB1_spec (r : TabReq) (cap : ℕ) (hcap : capB E r ≤ cap) (g : Fin 64 → ℕ) (ρ : WSE) (h : BIn E a r g ρ) :
    Runs cap (.seq (initB (sS 0) sS0_ne) st6b) ρ
      ((9 * (initCost (Wk E r + 1) + 1) + (41 * (Wk E r + 1) + 7)) + 1 + tcCost (Wk E r + 1) (preN r))
      (BMid1 E a r g ρ) := by
  unfold capB at hcap
  have q1 := Nat.two_pow_pos (Lt r)
  have q2 := Nat.two_pow_pos r.k
  set Wb := Wk E r + 1 with hWb
  obtain ⟨τ1, e1, hv1, hS1⟩ := initB_spec cap (sS 0) sS0_ne Wb (Wk_two E r) ρ (fun i => h.bl _ (nSA1_ubv E a i))
    (by rw [h.rx, h.regs.h42]) (by rw [h.rx, h.regs.z 51 (by decide)])
    (fun j => by
      show ρ.val (rX ⟨52 + j.val, _⟩) = 0
      rw [h.rx]; exact h.regs.z _ (by have := j.isLt; simp; omega)) (by omega)
  rw [h.s0, h.s0h, frame_tabWord] at hv1
  have hb3 : τ1.st (sS 3) = [] ∧ τ1.sh (sS 3) = 0 := by
    have hn : sS 3 ∉ List.ofFn (ubv (te := te E) (qa := Qa a)) := fun hm => by
      obtain ⟨i, e⟩ := List.mem_ofFn.mp hm; have := congrArg Fin.val e; simp at this; omega
    rw [hS1.st hn, hS1.sh hn]; exact h.bl _ (nSA1_sS E a 3 (by decide))
  have hT : TcInv Wb (preN r) (encN (preN r) ++ frame (formulaWord ⟨r.V, r.F⟩)) τ1 0 τ1 :=
    ⟨⟨v0, by simpa [encN] using hv1, by simp [v0], by simp [v0], by simp [v0], by simp [v0]⟩,
      ⟨by rw [hb3.1]; simp [tbOut, overlay], by rw [hb3.2]; simp [tbOut], by
        rw [hS1.val (by simp), h.rx, h.regs.z 39 (by decide)]; simp [tbOut]⟩,
      by rw [hS1.val (by simp), h.rx, h.regs.z 29 (by decide)], SameExcept.refl _ _ _⟩
  have hH := hdr cap r (by omega)
  have hlen := preN_length r
  obtain ⟨τ2, e2, ⟨v, hv, hv8, hv3, hv4, hv9⟩, h3, h3h, h39, h29, h9, hS2⟩ := st6b_spec cap Wb (by omega) (preN r)
    (frame (formulaWord ⟨r.V, r.F⟩)) τ1 τ1 hT (by rw [hS1.val (by simp), h.rx, h.regs.h9]) hH.fit (by omega)
    (by omega)
  refine ⟨τ2, WXExec.seq e1 e2, ⟨v, by rw [frame_tabWord]; exact hv, hv8, hv3, hv4, hv9⟩, by rw [h3, TBk, List.map_map]; rfl,
    h3h, fun j hj hj' => ?_, h9, h39, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
    have hn : rX j ∉ rX 9 :: rX 39 :: List.ofFn (RB : Fin 12 ↪ Fin NRk) := by
      simp only [List.mem_cons, List.mem_ofFn, not_or]
      refine ⟨rX_ne (fun e => hj'.1 (by rw [e]; rfl)), rX_ne (fun e => hj'.2 (by rw [e]; rfl)), fun ⟨i, e⟩ => ?_⟩
      exact RB_ne i j hj e
    rw [hS2.val hn, hS1.val (by simp), h.rx]
  · refine se_ext (S' := sS 3 :: sS 0 :: List.ofFn ubv) (R' := rX 9 :: rX 39 :: List.ofFn RB)
      (hS1.weaken (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) (fun _ h => by simp at h)) hS2
      (fun x hx => hx) (fun q hq => ?_)
    simp only [List.mem_cons, List.mem_ofFn] at hq
    rcases hq with rfl | rfl | ⟨i, rfl⟩
    · exact rX_mem _
    · exact rX_mem _
    · exact rX_mem _

/-- After the H points. -/
structure BMid2 (r : TabReq) (g : Fin 64 → ℕ) (ρ τ : WSE) : Prop where
  ev : ∃ v : Fin 10 → ℕ, EvV U0 RB (Wk E r + 1) (frame (tabWord r)) (encN (preN r)).length 0 v τ ∧ v 4 = 0 ∧ v 8 = 1 ∧
    v 9 = 0
  z57 : τ.st (sZ 57) = recStream ((hsK E r).map (binary (Wk E r + 1)))
  z57h : τ.sh (sZ 57) = 0
  s3 : τ.st (sS 3) = TBk E r
  s3h : τ.sh (sS 3) = 0
  rx : ∀ j : Fin 64, j.val < 52 → j.val ∉ [9, 39, 2, 5, 19] → τ.val (rX j) = g j
  r0 : ∀ j : Fin 64, j.val ∈ [9, 39, 5, 19] → τ.val (rX j) = 0
  r2 : τ.val (rX 2) = pV r
  fr : SameExcept ρ τ (sZ 57 :: sS 3 :: sS 0 :: List.ofFn ubv) RXL

theorem phB2_spec (r : TabReq) (cap : ℕ) (hcap : capB E r ≤ cap) (g : Fin 64 → ℕ) (ρ τ : WSE) (h : BIn E a r g ρ)
    (hm : BMid1 E a r g ρ τ) :
    Runs cap st7b τ (2 ^ r.k * (hCost (Wk E r + 1) r + 4) + 1 + 1 + (5 * (2 ^ r.k * (2 * (Wk E r + 1) + 1)) + 3))
      (BMid2 E a r g ρ) := by
  unfold capB at hcap
  have q1 := Nat.two_pow_pos (Lt r)
  have q2 := Nat.two_pow_pos r.k
  set Wb := Wk E r + 1 with hWb
  obtain ⟨v, hv, hv8, hv3, hv4, hv9⟩ := hm.ev
  have hW : r.k + 1 ≤ Wb := by have := Wk_ge E r; omega
  have b57 : τ.st (sZ 57) = [] ∧ τ.sh (sZ 57) = 0 := by
    have hn : sZ 57 ∉ sS 3 :: sS 0 :: List.ofFn (ubv (te := te E) (qa := Qa a)) := by
      simp only [List.mem_cons, List.mem_ofFn, not_or]
      exact ⟨by polyTabNe, by polyTabNe, fun ⟨i, e⟩ => by have := congrArg Fin.val e; simp at this; omega⟩
    rw [hm.fr.st hn, hm.fr.sh hn]; exact h.bl _ (nSA1_sZ E a 57)
  have hv' : EvV U0 RB Wb (encN (preN r) ++ frame (formulaWord ⟨r.V, r.F⟩)) (encN (preN r)).length 0 v τ := by
    rw [← frame_tabWord]; exact hv
  have hHS : HS Wb r (encN (preN r) ++ frame (formulaWord ⟨r.V, r.F⟩)) (encN (preN r)).length
      (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) τ 0 0 0 (pN r + 1) (2 ^ r.k) τ :=
    ⟨⟨v, hv', hv3, hv4, hv8, hv9⟩, ⟨by rw [b57.1]; simp [hOut, overlay], by rw [b57.2]; simp [hOut],
      by rw [hm.r39]; simp [hOut]⟩, by rw [hm.rx 5 (by decide) (by decide), h.regs.z 5 (by decide)],
      by rw [hm.rx 2 (by decide) (by decide), h.regs.h2], by rw [hm.rx 0 (by decide) (by decide), h.regs.z 0 (by decide)],
      by rw [hm.rx 1 (by decide) (by decide), h.regs.z 1 (by decide)], hm.r9,
      by rw [hm.rx 3 (by decide) (by decide), h.regs.z 3 (by decide)],
      by rw [hm.rx 4 (by decide) (by decide), h.regs.z 4 (by decide)],
      by rw [hm.rx 6 (by decide) (by decide), h.regs.z 6 (by decide)],
      by rw [hm.rx 29 (by decide) (by decide), h.regs.z 29 (by decide)], hm.s3, hm.s3h,
      by rw [hm.rx 19 (by decide) (by decide), h.regs.h19], SameExcept.refl _ _ _⟩
  have hlen := preN_length r
  obtain ⟨τ2, e2, hE⟩ := st7b_spec cap Wb E r hW _ _ τ τ hHS (by omega)
  obtain ⟨⟨v', hv'', hv4', hv8', hv9'⟩, z57, z57h, z39, z5, z0, z1, z9, z3, z4, z6, z29, z19, tb, tbh, fr, r2⟩ := hE
  refine ⟨τ2, e2, ⟨v', by rw [frame_tabWord]; exact hv'', hv4', hv8', hv9'⟩, z57, z57h, tb, tbh, fun j hj hj' => ?_,
    fun j hj => ?_, r2, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
    have hn : rX j ∉ rX 2 :: rX 5 :: rX 39 :: rX 19 :: List.ofFn (RB : Fin 12 ↪ Fin NRk) := by
      simp only [List.mem_cons, List.mem_ofFn, not_or]
      refine ⟨rX_ne (fun e => hj'.2.2.1 (by rw [e]; rfl)), rX_ne (fun e => hj'.2.2.2.1 (by rw [e]; rfl)),
        rX_ne (fun e => hj'.2.1 (by rw [e]; rfl)), rX_ne (fun e => hj'.2.2.2.2 (by rw [e]; rfl)), fun ⟨i, e⟩ => ?_⟩
      exact RB_ne i j hj e
    rw [fr.val hn]; exact hm.rx j hj (by simp; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with h | h | h | h
    · have : j = 9 := Fin.ext h
      subst this; exact z9
    · have : j = 39 := Fin.ext h
      subst this; exact z39
    · have : j = 5 := Fin.ext h
      subst this; exact z5
    · have : j = 19 := Fin.ext h
      subst this; exact z19
  · refine se_ext (S' := sZ 57 :: List.ofFn ubv) (R' := rX 2 :: rX 5 :: rX 39 :: rX 19 :: List.ofFn RB)
      (hm.fr.weaken (fun x hx => List.mem_cons_of_mem _ hx) (fun _ h => h)) fr (fun x hx => ?_) (fun q hq => ?_)
    · simp only [List.mem_cons, List.mem_ofFn] at hx ⊢
      rcases hx with rfl | ⟨i, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))
    · simp only [List.mem_cons, List.mem_ofFn] at hq
      rcases hq with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ <;> exact rX_mem _

theorem sb_s4 : sS 4 ∈ SB E a := by simp [SB]
theorem sb_ubv (x : Fin (NSx (te E) (Qa a) + 1)) (hx : x ∈ List.ofFn ubv) : x ∈ SB E a :=
  List.mem_append_right _ hx
theorem sb_of_mid2 (x : Fin (NSx (te E) (Qa a) + 1)) (hx : x ∈ sZ 57 :: sS 3 :: sS 0 :: List.ofFn ubv) : x ∈ SB E a := by
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | hx
  · simp [SB]
  · simp [SB]
  · simp [SB]
  · exact sb_ubv E a x hx
theorem sb_of_ts (x : Fin (NSx (te E) (Qa a) + 1)) (hx : x ∈ sS 4 :: List.ofFn ubv) : x ∈ SB E a := by
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact sb_s4 E a
  · exact sb_ubv E a x hx
theorem rvl_rxl (q : Fin NRk) (hq : q ∈ (RVL : List (Fin NRk))) : q ∈ (RXL : List (Fin NRk)) := by
  unfold RVL at hq
  simp only [List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at hq
  rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩ <;> exact rX_mem _

theorem G_le_Wk (r : TabReq) : r.G ≤ Wk E r := by unfold Wk; omega

theorem lt_pow_Wk (r : TabReq) (x : ℕ) (hx : x ≤ Wk E r) : x < 2 ^ (Wk E r + 1) :=
  lt_of_le_of_lt hx (lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by omega)))

theorem phB3_spec (r : TabReq) (cap : ℕ) (hcap : capB E r ≤ cap) (g : Fin 64 → ℕ) (ρ τ : WSE) (h : BIn E a r g ρ)
    (hm : BMid2 E a r g ρ τ) :
    Runs cap (.seq vLoop (closeOutX (sS 4) (rX 20))) τ
      ((r.V * (vBlockCost (Wk E r + 1) (preN r).length r.G r.n r.k r.s + 4) + 1) + 1 +
        (5 * (vtRecs (Wk E r + 1) E r r.V).length + 3)) (BEnd E a r g ρ) := by
  unfold capB at hcap
  have q1 := Nat.two_pow_pos (Lt r)
  have q2 := Nat.two_pow_pos r.k
  set Wb := Wk E r + 1 with hWb
  obtain ⟨v, hv, hv4, hv8, hv9⟩ := hm.ev
  have hv' : EvV U0 RB Wb (encN (preN r) ++ frame (formulaWord ⟨r.V, r.F⟩)) (encN (preN r)).length 0 v τ := by
    rw [← frame_tabWord]; exact hv
  have b4 : τ.st (sS 4) = [] ∧ τ.sh (sS 4) = 0 := by
    have hn : sS 4 ∉ sZ 57 :: sS 3 :: sS 0 :: List.ofFn (ubv (te := te E) (qa := Qa a)) := by
      simp only [List.mem_cons, List.mem_ofFn, not_or]
      exact ⟨by polyTabNe, by polyTabNe, by polyTabNe, fun ⟨i, e⟩ => by have := congrArg Fin.val e; simp at this; omega⟩
    rw [hm.fr.st hn, hm.fr.sh hn]; exact h.bl _ (nSA1_sS E a 4 (by decide))
  have gz : ∀ j : Fin 64, j.val ∈ [0, 1, 3, 4, 6, 7, 16, 17, 20, 21, 22, 23, 24, 29] → τ.val (rX j) = 0 := fun j hj => by
    rw [hm.rx j (by simp at hj; omega) (by simp at hj ⊢; omega)]
    exact h.regs.z j (by simp at hj ⊢; omega)
  have hTS : TS Wb (encN (preN r) ++ frame (formulaWord ⟨r.V, r.F⟩)) (encN (preN r)).length
      (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) τ [] τ :=
    ⟨⟨v, hv', hv8, hv9, trivial⟩, ⟨by rw [b4.1]; simp [overlay], by rw [b4.2]; rfl, gz 20 (by decide)⟩,
      gz 0 (by decide), gz 1 (by decide), hm.r0 9 (by decide), gz 3 (by decide), gz 4 (by decide), gz 6 (by decide),
      hm.r0 5 (by decide), gz 29 (by decide), gz 7 (by decide), hm.s3, hm.s3h, SameExcept.refl _ _ _⟩
  have hR : VRegs r τ := ⟨gz 16 (by decide), gz 17 (by decide), gz 21 (by decide), gz 23 (by decide),
    gz 24 (by decide), gz 22 (by decide), by rw [hm.rx 15 (by decide) (by decide), h.regs.h15],
    by rw [hm.rx 25 (by decide) (by decide), h.regs.h25], by rw [hm.rx 11 (by decide) (by decide), h.regs.h11],
    by rw [hm.rx 12 (by decide) (by decide), h.regs.h12]⟩
  have hW0 := Wk_ge0 E r
  have hBW : 2 * 2 ^ r.B + 1 < 2 ^ Wb := by
    have : 2 ^ (r.B + 2) ≤ 2 ^ Wb := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 ^ (r.B + 2) = 4 * 2 ^ r.B := by rw [pow_add]; ring
    have := Nat.two_pow_pos r.B
    omega
  have hlen := preN_length r
  obtain ⟨τ4, e4, hT4, hR4, h26', hK4⟩ := vLoop_spec cap Wb E r (by omega) _ _ τ [] hBW
    (lt_pow_Wk E r _ (by unfold Dm at hW0; omega)) (lt_pow_Wk E r _ (G_le_Wk E r)) τ hTS
    (by rw [hm.rx 43 (by decide) (by decide), h.regs.h43]) hR
    (by rw [hm.rx 26 (by decide) (by decide), h.regs.h26]) (by simp; omega)
  have hvl := vtRecs_length Wb E r r.V le_rfl
  obtain ⟨⟨v4, hv4', hv48, hv49, -⟩, ho4, z0, z1, z9, z3, z4, z6, z5, z29, z7, tb, tbh, fr4⟩ := hT4
  have hVX : r.V * ((r.k + r.s + 2) * (2 * Wb + 1)) ≤ (r.V + 1) * ((r.k + r.s + 2) * (2 * Wb + 1)) :=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  have e5 := closeOut_spec cap τ4 (vtRecs Wb E r r.V) [] (by simpa using ho4) (by rw [hvl]; omega)
  set τ5 := ((τ4.sets (sS 4) (overlay (vtRecs Wb E r r.V ++ [false]) [])).seth (sS 4) 0).setv (rX 20) 0 with hτ5
  have hS5 : SameExcept τ4 τ5 [sS 4] [rX 20] := se_out τ4 _ _ _ _ _
  refine ⟨τ5, WXExec.seq e4 (WXExec.wm e5) |>.mono (by simp [hvl]), ⟨v4, ?_, hv48, hv49⟩, ?_, by simp [hτ5], ?_, ?_,
    fun j hj hj' => ?_, fun j hj => ?_, ?_⟩
  · rw [frame_tabWord]
    exact evv_transfer hv4' (fun i => ⟨hS5.st (nm1 (ne4 i)), hS5.sh (nm1 (ne4 i))⟩)
      (fun j => hS5.val (nm1 (RB_ne j 20 (by decide))))
  · simp only [hτ5, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, overlay, List.drop_nil,
      List.append_nil, vtRecs_VTn, recStream]
    rfl
  · have hn : sZ 57 ∉ sS 4 :: List.ofFn (ubv (te := te E) (qa := Qa a)) := by
      simp only [List.mem_cons, List.mem_ofFn, not_or]
      exact ⟨by polyTabNe, fun ⟨i, e⟩ => by have := congrArg Fin.val e; simp at this; omega⟩
    rw [hS5.st (nm1 (by polyTabNe)), fr4.st hn, hm.z57]
  · have hn : sZ 57 ∉ sS 4 :: List.ofFn (ubv (te := te E) (qa := Qa a)) := by
      simp only [List.mem_cons, List.mem_ofFn, not_or]
      exact ⟨by polyTabNe, fun ⟨i, e⟩ => by have := congrArg Fin.val e; simp at this; omega⟩
    rw [hS5.sh (nm1 (by polyTabNe)), fr4.sh hn, hm.z57h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj'
    have n20 : rX j ∉ [rX 20] := nm1 (rX_ne (fun e => hj'.2.2.2.2.2.1 (by rw [e]; rfl)))
    rw [hS5.val n20]
    by_cases hk : j.val ∈ [5, 20, 16, 17, 21, 23, 24, 43, 26]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with e | e | e | e | e | e | e | e | e
      · omega
      · omega
      · have : j = 16 := Fin.ext e
        subst this; rw [hR4.z16, h.regs.z 16 (by decide)]
      · have : j = 17 := Fin.ext e
        subst this; rw [hR4.z17, h.regs.z 17 (by decide)]
      · have : j = 21 := Fin.ext e
        subst this; rw [hR4.z21, h.regs.z 21 (by decide)]
      · have : j = 23 := Fin.ext e
        subst this; rw [hR4.z44, h.regs.z 23 (by decide)]
      · have : j = 24 := Fin.ext e
        subst this; rw [hR4.z24, h.regs.z 24 (by decide)]
      · omega
      · omega
    · rw [hK4 j hk]
      by_cases j39 : j.val = 39
      · have : j = 39 := Fin.ext j39
        subst this; rw [hm.r0 39 (by decide), h.regs.z 39 (by decide)]
      · exact hm.rx j hj (by simp; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with e | e | e | e | e
    · have : j = 9 := Fin.ext e
      subst this; rw [hS5.val (nm1 (by polyTabNe)), hK4 9 (by decide)]; exact hm.r0 9 (by decide)
    · have : j = 19 := Fin.ext e
      subst this; rw [hS5.val (nm1 (by polyTabNe)), hK4 19 (by decide)]; exact hm.r0 19 (by decide)
    · have : j = 26 := Fin.ext e
      subst this; rw [hS5.val (nm1 (by polyTabNe))]; exact h26'
    · have : j = 20 := Fin.ext e
      subst this; simp [hτ5]
    · have : j = 5 := Fin.ext e
      subst this; rw [hS5.val (nm1 (by polyTabNe))]; exact z5
  · exact se_ext (S' := [sS 4]) (R' := [rX 20]) (se_ext (S' := sS 4 :: List.ofFn ubv) (R' := RVL)
      (hm.fr.weaken (sb_of_mid2 E a) (fun _ h => h)) fr4 (sb_of_ts E a) (fun q _ => rvl_rxl q ‹_›)) hS5
      (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sb_s4 E a)
      (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact rX_mem _)

theorem phB_spec (r : TabReq) (cap : ℕ) (hcap : capB E r ≤ cap) (g : Fin 64 → ℕ) (ρ : WSE) (h : BIn E a r g ρ) :
    Runs cap (phB E a) ρ (phBCost E r) (BEnd E a r g ρ) := by
  obtain ⟨τ1, e1, m1⟩ := phB1_spec E a r cap hcap g ρ h
  obtain ⟨τ2, e2, m2⟩ := phB2_spec E a r cap hcap g ρ τ1 h m1
  obtain ⟨τ3, e3, m3⟩ := phB3_spec E a r cap hcap g ρ τ2 h m2
  exact ⟨τ3, WXExec.seq e1 (WXExec.seq e2 e3), m3⟩

end NearCubicGates.Close.Expand.PolyTab
