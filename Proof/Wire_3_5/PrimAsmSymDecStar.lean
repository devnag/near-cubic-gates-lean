import Proof.Wire_3_5.PrimAsmSymDecCounts
import Proof.Wire_3_5.PrimAsmGapNums
import Proof.Wire_3_5.PrimAsmCapNum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

/-! ## The blocks -/

def SGb : Fin 20 ↪ Fin LNR := ⟨fun i => ⟨250 + i.val, by have := i.isLt; unfold LNR; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩
def Gb : Fin 24 ↪ Fin LNR := ⟨fun i => ⟨270 + i.val, by have := i.isLt; unfold LNR; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩
def Hb : Fin 32 ↪ Fin LNR := ⟨fun i => ⟨337 + i.val, by have := i.isLt; unfold LNR; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩
def xT : Fin LNR := ⟨296, by decide⟩

theorem SGb_val (i : Fin 20) : (SGb i).val = 250 + i.val := rfl
theorem Gb_val (i : Fin 24) : (Gb i).val = 270 + i.val := rfl
theorem Hb_val (i : Fin 32) : (Hb i).val = 337 + i.val := rfl

/-- A register outside the three blocks and the copy scratch. -/
def Outside (r : Fin LNR) : Prop := (r.val < 250 ∨ 294 ≤ r.val) ∧ r.val ≠ 296 ∧ (r.val < 337 ∨ 369 ≤ r.val)

theorem out_SGb {r : Fin LNR} (h : Outside r) (i : Fin 20) : SGb i ≠ r := fun e => by
  have := congrArg Fin.val e; rw [SGb_val] at this; have := i.isLt; unfold Outside at h; omega
theorem out_Gb {r : Fin LNR} (h : Outside r) (i : Fin 24) : Gb i ≠ r := fun e => by
  have := congrArg Fin.val e; rw [Gb_val] at this; have := i.isLt; unfold Outside at h; omega
theorem out_Hb {r : Fin LNR} (h : Outside r) (i : Fin 32) : Hb i ≠ r := fun e => by
  have := congrArg Fin.val e; rw [Hb_val] at this; have := i.isLt; unfold Outside at h; omega
theorem out_xT {r : Fin LNR} (h : Outside r) : xT ≠ r := fun e => by
  have := congrArg Fin.val e; unfold Outside at h; simp [xT] at this; omega

/-- `CapNum.capM_spec`'s capacity conditions at `(C, m, q, r, s)`. -/
structure CapNeed (C : Ledger.CapParams) (m : Mode) (q r s cap : ℕ) : Prop where
  hc1 : 1 ≤ cap
  hr : r ≤ cap
  hs : s ≤ cap
  hq : q ≤ cap
  hL1 : Ledger.Lq q ≤ cap
  h48 : r ^ 48 ≤ cap
  h32 : s ^ 32 ≤ cap
  h64 : q ^ 64 ≤ cap
  h4832 : r ^ 48 * s ^ 32 ≤ cap
  hrsq : r ^ 48 * s ^ 32 * q ^ 64 ≤ cap
  hC : CapNum.cMain C m ≤ cap
  hnum : Ledger.capMainNum C m r s q ≤ cap
  hLK : Ledger.Lq q ^ Ledger.capExp32 m ≤ cap
  hsum : Ledger.capMainNum C m r s q + Ledger.Lq q ^ Ledger.capExp32 m ≤ cap
  hroot1 : 2 ^ 32 * Ledger.capMainPow C m r s q + 1 ≤ cap
  h3 : r ^ 3 ≤ cap
  h3q : r ^ 3 * q ≤ cap
  hCe : CapNum.cEnc C ≤ cap
  hE : Ledger.capEncPow C r q ≤ cap
  hroot2 : 2 ^ 2 * Ledger.capEncPow C r q + 1 ≤ cap

/-! ## The program -/

variable (cap : ℕ) (x : ℕ)

/-- **The call's star numbers, sparse count and cap** (mode `sym`). -/
def starCapW (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR dN (SGb 0) xT) (.seq (StarNums.starNumsM cr fe SGb)
  (.seq (FinalPass.Hash4.wcopyR (SGb 1) (Gb 0) xT) (.seq (SparseNum.sparseM ζ Cδ Gb)
  (.seq (FinalPass.Hash4.wcopyR dN (Hb 0) xT) (.seq (FinalPass.Hash4.wcopyR (SGb 3) (Hb 1) xT)
  (.seq (FinalPass.Hash4.wcopyR (Gb 12) (Hb 2) xT) (.seq (FinalPass.Hash4.wcopyR (SGb 1) (Hb 3) xT)
  (CapNum.capM C Hb))))))))

/-- Its cost bound. -/
def starCapCost (n cr fe t sp L cap : ℕ) : ℕ :=
  (18 * n + 3) + 1 + (StarNums.starCost n cr fe + 1 + ((18 * L + 3) + 1 + ((t + 5) * (40 * UnaryPow.sq cap) + 1 +
    ((18 * n + 3) + 1 + ((18 * cap + 3) + 1 + ((18 * sp + 3) + 1 + ((18 * L + 3) + 1 +
      ((cap + 2) * 200 + 1500) * UnaryPow.sq cap)))))))

theorem starOut_outside (σ : WState (LNS x) LNR) (P : Shared.StarParams) (fe : ℕ) (r : Fin LNR)
    (h : ∀ i : Fin 20, SGb i ≠ r) : (StarNums.starOut σ SGb P fe).val r = σ.val r := by
  simp [StarNums.starOut, Function.update_of_ne (h _).symm]

theorem starCap_spec (cr fe : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (σ : WState (LNS x) LNR) (hn : σ.val dN = P.n)
    (hSG : ∀ i, σ.val (SGb i) = 0) (hG : ∀ i, σ.val (Gb i) = 0) (hH : ∀ i, σ.val (Hb i) = 0) (hx : σ.val xT = 0)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : CapNeed C .sym P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap) :
    ∃ τ c, WExec cap (starCapW x cr fe ζ Cδ C) σ τ c ∧
      τ.val (SGb 1) = Ledger.Lq P.n ∧ τ.val (SGb 3) = P.r ∧ τ.val (SGb 4) = P.s ∧ τ.val (SGb 5) = P.b ∧
      τ.val (SGb 6) = P.r / 2 ∧ τ.val (SGb 8) = P.s * (P.r / 2) ∧ τ.val (SGb 9) = P.k ∧
      τ.val (SGb 10) = fe * Ledger.Lq P.n ∧ τ.val (Gb 12) = Ledger.rowBSparse h0 h1 2 Cδ P.n ∧
      τ.val (Hb 13) = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n ∧
      (∀ r, Outside r → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧
      c ≤ starCapCost P.n cr fe (Ledger.rowBt h0 h1 P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) (Ledger.Lq P.n) cap := by
  obtain ⟨sp, hsp⟩ : ∃ v, v = Ledger.rowBSparse h0 h1 2 Cδ P.n := ⟨_, rfl⟩
  rw [← hsp] at hcC ⊢
  have hSGne : ∀ (i : Fin 20) (j : Fin 24), SGb i ≠ Gb j := fun i j e => by
    have := congrArg Fin.val e; rw [SGb_val, Gb_val] at this; have := i.isLt; omega
  have hSHne : ∀ (i : Fin 20) (j : Fin 32), SGb i ≠ Hb j := fun i j e => by
    have := congrArg Fin.val e; rw [SGb_val, Hb_val] at this; have := i.isLt; omega
  have hGHne : ∀ (i : Fin 24) (j : Fin 32), Gb i ≠ Hb j := fun i j e => by
    have := congrArg Fin.val e; rw [Gb_val, Hb_val] at this; have := i.isLt; omega
  have hxS : ∀ i, SGb i ≠ xT := fun i e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [xT] at this; omega
  have hxG : ∀ i, Gb i ≠ xT := fun i e => by have := congrArg Fin.val e; rw [Gb_val] at this; simp [xT] at this; omega
  have hxH : ∀ i, Hb i ≠ xT := fun i e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [xT] at this; omega
  have hdS : ∀ i, SGb i ≠ dN := fun i e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [dN] at this; omega
  have hdH : ∀ i, Hb i ≠ dN := fun i e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [dN] at this; omega
  have hdx : dN ≠ xT := by decide
  have hn2 : P.n ≤ cap := hcC.hq
  -- 1: SGb 0 := n
  have e1 := FinalPass.Hash4.wcopyR_spec cap dN (SGb 0) xT (hdS 0).symm hdx (hxS 0) σ (hSG 0) hx (by rw [hn]; omega)
  rw [hn] at e1
  obtain ⟨σ1, g1⟩ : ∃ y, y = σ.setv (SGb 0) P.n := ⟨_, rfl⟩
  rw [← g1] at e1
  -- 2: the star numbers
  have e2 := StarNums.starNums_spec cap cr fe SGb P hrP σ1 (by rw [g1]; simp) (fun i hi => by
    rw [g1]; simp [Function.update_apply, SGb.injective.ne hi, hSG]) hcS
  obtain ⟨σ2, g2⟩ : ∃ y, y = StarNums.starOut σ1 SGb P fe := ⟨_, rfl⟩
  rw [← g2] at e2
  have ⟨v1, v3, v4, v5, v6, _, v8, v9, v10⟩ := StarNums.starOut_val σ1 SGb P fe
  rw [← g2] at v1 v3 v4 v5 v6 v8 v9 v10
  have o2 : ∀ r, (∀ i : Fin 20, SGb i ≠ r) → σ2.val r = σ1.val r := fun r h => by
    rw [g2]; exact starOut_outside x σ1 P fe r h
  have o1 : ∀ r, SGb 0 ≠ r → σ1.val r = σ.val r := fun r h => by rw [g1]; simp [Function.update_of_ne h.symm]
  have o21 : ∀ r, (∀ i : Fin 20, SGb i ≠ r) → σ2.val r = σ.val r := fun r h => by rw [o2 r h, o1 r (h 0)]
  -- 3: Gb 0 := L
  have gL : σ2.val (SGb 1) = Ledger.Lq P.n := v1
  have e3 := FinalPass.Hash4.wcopyR_spec cap (SGb 1) (Gb 0) xT (hSGne 1 0) (hxS 1) (hxG 0) σ2
    (by rw [o21 _ (fun i => hSGne i 0), hG]) (by rw [o21 _ hxS, hx]) (by rw [gL]; exact hcC.hL1)
  rw [gL] at e3
  obtain ⟨σ3, g3⟩ : ∃ y, y = σ2.setv (Gb 0) (Ledger.Lq P.n) := ⟨_, rfl⟩
  rw [← g3] at e3
  have o3 : ∀ r, Gb 0 ≠ r → σ3.val r = σ2.val r := fun r h => by rw [g3]; simp [Function.update_of_ne h.symm]
  -- 4: the sparse count
  have e4 := SparseNum.sparse_spec cap h0 h1 Cδ Gb σ3 P.n (by rw [g3]; simp) (fun i hi => by
      rw [o3 _ (Gb.injective.ne hi).symm, o21 _ (fun k => hSGne k i), hG]) hcP
  rw [← hsp] at e4
  obtain ⟨σ4, g4⟩ : ∃ y, y = (σ3.setv (Gb 11) (Ledger.rowBLambda h0 h1 2 P.n)).setv (Gb 12) sp := ⟨_, rfl⟩
  rw [← g4] at e4
  have o4 : ∀ r, Gb 11 ≠ r → Gb 12 ≠ r → σ4.val r = σ3.val r := fun r a b => by
    rw [g4]; simp [Function.update_of_ne a.symm, Function.update_of_ne b.symm]
  have vsp : σ4.val (Gb 12) = sp := by rw [g4]; simp
  have oS4 : ∀ i, σ4.val (SGb i) = σ2.val (SGb i) := fun i => by
    rw [o4 _ (hSGne i 11).symm (hSGne i 12).symm, o3 _ (hSGne i 0).symm]
  have oH4 : ∀ j, σ4.val (Hb j) = σ.val (Hb j) := fun j => by
    rw [o4 _ (hGHne 11 j) (hGHne 12 j), o3 _ (hGHne 0 j), o21 _ (fun i => hSHne i j)]
  have ox4 : σ4.val xT = 0 := by rw [o4 _ (hxG 11) (hxG 12), o3 _ (hxG 0), o21 _ hxS, hx]
  have odN4 : σ4.val dN = P.n := by
    rw [o4 _ (by decide) (by decide), o3 _ (by decide), o21 _ (fun i => hdS i), hn]
  -- 5-8: the cap's inputs
  have e5 := FinalPass.Hash4.wcopyR_spec cap dN (Hb 0) xT (hdH 0).symm hdx (hxH 0) σ4 (by rw [oH4, hH])
    ox4 (by rw [odN4]; omega)
  rw [odN4] at e5
  obtain ⟨σ5, g5⟩ : ∃ y, y = σ4.setv (Hb 0) P.n := ⟨_, rfl⟩
  rw [← g5] at e5
  have o5 : ∀ r, Hb 0 ≠ r → σ5.val r = σ4.val r := fun r h => by rw [g5]; simp [Function.update_of_ne h.symm]
  have e6 := FinalPass.Hash4.wcopyR_spec cap (SGb 3) (Hb 1) xT (hSHne 3 1) (hxS 3) (hxH 1) σ5
    (by rw [o5 _ (Hb.injective.ne (by decide)), oH4, hH]) (by rw [o5 _ (hxH 0), ox4])
    (by rw [o5 _ (hSHne 3 0).symm, oS4, v3]; exact hcC.hr)
  rw [o5 _ (hSHne 3 0).symm, oS4, v3] at e6
  obtain ⟨σ6, g6⟩ : ∃ y, y = σ5.setv (Hb 1) P.r := ⟨_, rfl⟩
  rw [← g6] at e6
  have o6 : ∀ r, Hb 1 ≠ r → σ6.val r = σ5.val r := fun r h => by rw [g6]; simp [Function.update_of_ne h.symm]
  have e7 := FinalPass.Hash4.wcopyR_spec cap (Gb 12) (Hb 2) xT (hGHne 12 2) (hxG 12) (hxH 2) σ6
    (by rw [o6 _ (Hb.injective.ne (by decide)), o5 _ (Hb.injective.ne (by decide)), oH4, hH])
    (by rw [o6 _ (hxH 1), o5 _ (hxH 0), ox4])
    (by rw [o6 _ (hGHne 12 1).symm, o5 _ (hGHne 12 0).symm, vsp]; exact hcC.hs)
  rw [o6 _ (hGHne 12 1).symm, o5 _ (hGHne 12 0).symm, vsp] at e7
  obtain ⟨σ7, g7⟩ : ∃ y, y = σ6.setv (Hb 2) sp := ⟨_, rfl⟩
  rw [← g7] at e7
  have o7 : ∀ r, Hb 2 ≠ r → σ7.val r = σ6.val r := fun r h => by rw [g7]; simp [Function.update_of_ne h.symm]
  have e8 := FinalPass.Hash4.wcopyR_spec cap (SGb 1) (Hb 3) xT (hSHne 1 3) (hxS 1) (hxH 3) σ7
    (by rw [o7 _ (Hb.injective.ne (by decide)), o6 _ (Hb.injective.ne (by decide)),
      o5 _ (Hb.injective.ne (by decide)), oH4, hH])
    (by rw [o7 _ (hxH 2), o6 _ (hxH 1), o5 _ (hxH 0), ox4])
    (by rw [o7 _ (hSHne 1 2).symm, o6 _ (hSHne 1 1).symm, o5 _ (hSHne 1 0).symm, oS4, gL]; exact hcC.hL1)
  rw [o7 _ (hSHne 1 2).symm, o6 _ (hSHne 1 1).symm, o5 _ (hSHne 1 0).symm, oS4, gL] at e8
  obtain ⟨σ8, g8⟩ : ∃ y, y = σ7.setv (Hb 3) (Ledger.Lq P.n) := ⟨_, rfl⟩
  rw [← g8] at e8
  have o8 : ∀ r, Hb 3 ≠ r → σ8.val r = σ7.val r := fun r h => by rw [g8]; simp [Function.update_of_ne h.symm]
  have o85 : ∀ r, Hb 0 ≠ r → Hb 1 ≠ r → Hb 2 ≠ r → Hb 3 ≠ r → σ8.val r = σ4.val r := fun r a b c d => by
    rw [o8 r d, o7 r c, o6 r b, o5 r a]
  -- 9: the cap
  have e9 := CapNum.capM_spec cap C .sym Hb σ8 P.n P.r sp
    (by rw [o8 _ (Hb.injective.ne (by decide)), o7 _ (Hb.injective.ne (by decide)),
      o6 _ (Hb.injective.ne (by decide)), g5]; simp)
    (by rw [o8 _ (Hb.injective.ne (by decide)), o7 _ (Hb.injective.ne (by decide)), g6]; simp)
    (by rw [o8 _ (Hb.injective.ne (by decide)), g7]; simp) (by rw [g8]; simp)
    (by rw [o85 _ (Hb.injective.ne (by decide)) (Hb.injective.ne (by decide)) (Hb.injective.ne (by decide))
      (Hb.injective.ne (by decide)), oH4, hH]; rfl)
    (fun i hi => by
      have n0 : Hb 0 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      have n1 : Hb 1 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      have n2 : Hb 2 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      have n3 : Hb 3 ≠ Hb i := Hb.injective.ne (fun e => by subst e; simp at hi)
      rw [o85 _ n0 n1 n2 n3, oH4, hH])
    hcC.hc1 hcC.hr hcC.hs hcC.hq hcC.hL1 hcC.h48 hcC.h32 hcC.h64 hcC.h4832 hcC.hrsq hcC.hC hcC.hnum hcC.hLK
    hcC.hsum hcC.hroot1 hcC.h3 hcC.h3q hcC.hCe hcC.hE hcC.hroot2
  obtain ⟨σ9, g9⟩ : ∃ y, y = σ8.setv (Hb 13) (Ledger.rowBCap C .sym P.r sp P.n) := ⟨_, rfl⟩
  rw [← g9] at e9
  have o9 : ∀ r, Hb 13 ≠ r → σ9.val r = σ8.val r := fun r h => by rw [g9]; simp [Function.update_of_ne h.symm]
  have oAll : ∀ r, (∀ i : Fin 20, SGb i ≠ r) → (∀ j : Fin 24, Gb j ≠ r) → (∀ k : Fin 32, Hb k ≠ r) →
      σ9.val r = σ.val r := fun r a b c => by
    rw [o9 r (c 13), o85 r (c 0) (c 1) (c 2) (c 3), o4 r (b 11) (b 12), o3 r (b 0), o21 r a]
  have vS9 : ∀ i, σ9.val (SGb i) = σ2.val (SGb i) := fun i => by
    rw [o9 _ (hSHne i 13).symm, o85 _ (hSHne i 0).symm (hSHne i 1).symm (hSHne i 2).symm (hSHne i 3).symm, oS4]
  refine ⟨σ9, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vS9, gL]
  · rw [vS9, v3]
  · rw [vS9, v4]
  · rw [vS9, v5]
  · rw [vS9, v6]
  · rw [vS9, v8]
  · rw [vS9, v9]
  · rw [vS9, v10]; rfl
  · rw [o9 _ (hGHne 12 13).symm, o85 _ (hGHne 12 0).symm (hGHne 12 1).symm (hGHne 12 2).symm (hGHne 12 3).symm, vsp]
  · rw [g9]; simp
  · intro r hr
    exact oAll r (out_SGb hr) (out_Gb hr) (out_Hb hr)
  · simp only [g9, g8, g7, g6, g5, g4, g3, g2, g1, StarNums.starOut, WState.setv_st]
  · simp only [g9, g8, g7, g6, g5, g4, g3, g2, g1, StarNums.starOut, WState.setv_sh]
  · simp only [g9, g8, g7, g6, g5, g4, g3, g2, g1, StarNums.starOut, WState.setv_cell]
  · have := hcC.hr
    unfold starCapCost
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
