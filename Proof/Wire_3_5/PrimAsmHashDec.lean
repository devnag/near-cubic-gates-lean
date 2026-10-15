import Proof.Wire_3_5.PrimAsmSymDecFB
import Proof.Wire_3_5.PrimAsmSymDecRun
import Proof.Wire_3_5.PrimAsmThrDataIface3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith

theorem rv_dF : dF.val = 323 := rfl
theorem rv_dC : dC.val = 324 := rfl
theorem rv_dP : dP.val = 325 := rfl
theorem rv_dT : dT.val = 326 := rfl
theorem rv_dK : dK.val = 327 := rfl
theorem rv_CR : CR.val = 372 := rfl
theorem rv_xT : xT.val = 296 := rfl
theorem rv_dA' : dA.val = 321 := rfl

section HashA
variable (cap : ℕ) (x : ℕ)

/-- Phase A: `n` from the request (the request rewound), then the star numbers (`SGb 8 = kh`). -/
def hAW (cr : ℕ) : WM (LNS x) LNR :=
  .seq (preAW x) (.seq (readNatM true (sk x 0) dF dC dN dP dT) (.seq (preBW x)
    (.seq (FinalPass.Hash4.wcopyR dN (SGb 0) xT) (StarNums.starNumsM cr 0 SGb))))

/-- Phase A's exit state. -/
def hAOut (σ : WState (LNS x) LNR) (w : List Bool) (P : Shared.StarParams) : WState (LNS x) LNR :=
  StarNums.starOut (((((σ.setv LEN w.length).seth (sk x 0)
    (([] : List Bool).length + stp true * (RepairRepresentation.natWord P.n).length)).setv dN (0 + P.n)).seth
    (sk x 0) 0).setv (SGb 0) P.n) SGb P 0

/-- Phase A's cost. -/
def hACost (n wl cr cap : ℕ) : ℕ :=
  4 * UnaryPow.sq cap + 1 + ((natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 + (5 * UnaryPow.sq cap + 1 +
    (UnaryPow.sq cap + 1 + StarNums.starCost n cr 0)))

theorem hA_run (cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (σ : WState (LNS x) LNR)
    (w : List Bool) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (hw : w = Data.reqW P.n mb codes cc tl)
    (hst : σ.st (sk x 0) = frame w) (hsh : σ.sh (sk x 0) = 0) (zL : σ.val LEN = 0) (zC : σ.val CR = 0)
    (zT : σ.val TM = 0) (zF : σ.val dF = 0) (zc : σ.val dC = 0) (zN : σ.val dN = 0) (zP : σ.val dP = 0)
    (zt : σ.val dT = 0) (zx : σ.val xT = 0) (zS : ∀ i, σ.val (SGb i) = 0)
    (hc1 : 2 * w.length + 2 ≤ cap) (hc2 : 2 ^ (natBitLength P.n + 1) ≤ cap) (hc3 : (0 + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap) :
    WExec cap (hAW x cr) σ (hAOut x σ w P) (hACost P.n w.length cr cap) := by
  have hl := UnaryPow.lin_le_sq cap
  have hn1 : P.n ≤ cap := by omega
  have e1 := preA_spec cap x w σ hst hsh zL zC zT hc1
  obtain ⟨σ1, h1⟩ : ∃ y, y = σ.setv LEN w.length := ⟨_, rfl⟩
  rw [← h1] at e1
  have he := Data.enc_reqW P.n mb codes cc tl
  have e2 := readNatM_spec cap true (sk x 0) dF dC dN dP dT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) P.n []
    (enc true [mb] ++ (enc true (RepairRepresentation.natWord codes.length) ++
      (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
        (enc true (cc.flatMap RepairRepresentation.natWord) ++ (enc true tl ++ [false]))))))
    σ1 (by rw [h1]; simp only [WState.setv_st]; rw [hst, hw, he]; rfl) (by rw [h1]; simp [hsh])
    (by rw [h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zF]) (by rw [h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zc])
    (by rw [h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zP]) (by rw [h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zt])
    (by rw [h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zN]; omega)
  have v1N : σ1.val dN = 0 := by rw [h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zN]
  rw [v1N] at e2
  obtain ⟨σ2, h2⟩ : ∃ y, y = (σ1.seth (sk x 0) (([] : List Bool).length + stp true *
      (RepairRepresentation.natWord P.n).length)).setv dN (0 + P.n) := ⟨_, rfl⟩
  rw [← h2] at e2
  have hwl : (RepairRepresentation.natWord P.n).length ≤ w.length := by
    rw [hw]; unfold Data.reqW; simp
  have e3 := preB_spec cap x w.length σ2 (by rw [h2, h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val])
    (by rw [h2, h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zC]) (by rw [h2, h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zT])
    (by rw [h2, WState.setv_sh, WState.seth_sh, Function.update_self]; simp only [List.length_nil, stp, if_true]; omega) hc1
  obtain ⟨σ3, h3⟩ : ∃ y, y = σ2.seth (sk x 0) 0 := ⟨_, rfl⟩
  rw [← h3] at e3
  have e4 := SparseNum.copy1 cap dN (SGb 0) xT (by decide) (by decide) (by decide) P.n σ3
    (by rw [h3, h2]; simp) (by rw [h3, h2, h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zS 0])
    (by rw [h3, h2, h1]; simp [Function.update_apply, Fin.ext_iff, rv_dF, rv_dC, rv_dN, rv_dP, rv_dT, rv_LEN, rv_CR, rv_TM, rv_xT, SGb_val, zx]) hn1
  obtain ⟨σ4, h4⟩ : ∃ y, y = σ3.setv (SGb 0) P.n := ⟨_, rfl⟩
  rw [← h4] at e4
  have k4 : ∀ r, r ≠ SGb 0 → r ≠ dN → r ≠ LEN → σ4.val r = σ.val r := by
    intro r a b c
    rw [h4, h3, h2, h1]
    simp only [WState.setv_val, WState.seth_val, Function.update_of_ne a, Function.update_of_ne b,
      Function.update_of_ne c]
  have e5 := StarNums.starNums_spec cap cr 0 SGb P hrP σ4 (by rw [h4]; simp)
    (fun i hi => by
      have n1 : SGb i ≠ dN := fun e => by
        have := congrArg Fin.val e; rw [SGb_val, rv_dN] at this; have := i.isLt; omega
      have n2 : SGb i ≠ LEN := fun e => by
        have := congrArg Fin.val e; rw [SGb_val, rv_LEN] at this; have := i.isLt; omega
      rw [k4 _ (fun e => hi (SGb.injective e)) n1 n2]
      exact zS i) hc3
  have ho : StarNums.starOut σ4 SGb P 0 = hAOut x σ w P := by rw [h4, h3, h2, h1]; rfl
  rw [ho] at e5
  exact WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))

end HashA

section HashC
variable (cap : ℕ) (x : ℕ)

/-- **Reading item `k` of a unary list** (the head at the item's start): the item's value added to `r`, the head past it. -/
theorem readItem_at {ns nr : ℕ} (s : Fin (ns + 1)) (r : Fin nr) (l : List ℕ) (tail : List Bool) (k : ℕ)
    (hk : k < l.length) (v : ℕ) (σ : WState ns nr) (hst : σ.st s = Data.unaryList l ++ tail)
    (hsh : σ.sh s = (Data.unaryList (l.take k)).length) (hv : σ.val r = v) (hc : v + l.getD k 0 ≤ cap) :
    WExec cap (readItemW s r) σ ((σ.seth s (Data.unaryList (l.take (k + 1))).length).setv r (v + l.getD k 0))
      (7 * l.getD k 0 + 3) := by
  have hg : l.getD k 0 = l[k] := by rw [List.getD_eq_getElem _ _ hk]
  have hd : l.drop k = l[k] :: l.drop (k + 1) := List.drop_eq_getElem_cons hk
  have ht : l.take (k + 1) = l.take k ++ [l[k]] := by rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  have hsplit : Data.unaryList l ++ tail = Data.unaryList (l.take k) ++ List.replicate (l.getD k 0) true ++
      false :: (Data.unaryList (l.drop (k + 1)) ++ tail) := by
    have e : Data.unaryList l = Data.unaryList (l.take k) ++ Data.unaryList (l.drop k) := by
      rw [← Data.unaryList_append, List.take_append_drop]
    rw [e, hd, hg, unaryList_cons']
    simp only [List.append_assoc, List.cons_append]
  have h := readItem_spec cap s r (Data.unaryList (l.take k)) (Data.unaryList (l.drop (k + 1)) ++ tail) (l.getD k 0) σ
    (by rw [hst, hsplit]) hsh (by rw [hv]; exact hc)
  rw [hv] at h
  have hpos : (Data.unaryList (l.take k)).length + l.getD k 0 + 1 = (Data.unaryList (l.take (k + 1))).length := by
    rw [ht, Data.unaryList_append, List.length_append, hg]
    simp [Data.unaryList]
    omega
  rw [hpos] at h
  exact h

/-- Phase C1: the data tape's first sixteen items (`hashNums`) into `Hb 0 … Hb 15`. -/
def hC1W : WM (LNS x) LNR :=
  (.seq (readItemW (sk x 113) (Hb ⟨0, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨1, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨2, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨3, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨4, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨5, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨6, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨7, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨8, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨9, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨10, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨11, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨12, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨13, by decide⟩)) (.seq (readItemW (sk x 113) (Hb ⟨14, by decide⟩)) (readItemW (sk x 113) (Hb ⟨15, by decide⟩)))))))))))))))))

/-- Phase C1's exit state. -/
def hC1Out (σ : WState (LNS x) LNR) (l : List ℕ) : WState (LNS x) LNR :=
  ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0))).seth (sk x 113) ((Data.unaryList (l.take (8 + 1))).length))).setv (Hb ⟨8, by decide⟩) (0 + l.getD 8 0))).seth (sk x 113) ((Data.unaryList (l.take (9 + 1))).length))).setv (Hb ⟨9, by decide⟩) (0 + l.getD 9 0))).seth (sk x 113) ((Data.unaryList (l.take (10 + 1))).length))).setv (Hb ⟨10, by decide⟩) (0 + l.getD 10 0))).seth (sk x 113) ((Data.unaryList (l.take (11 + 1))).length))).setv (Hb ⟨11, by decide⟩) (0 + l.getD 11 0))).seth (sk x 113) ((Data.unaryList (l.take (12 + 1))).length))).setv (Hb ⟨12, by decide⟩) (0 + l.getD 12 0))).seth (sk x 113) ((Data.unaryList (l.take (13 + 1))).length))).setv (Hb ⟨13, by decide⟩) (0 + l.getD 13 0))).seth (sk x 113) ((Data.unaryList (l.take (14 + 1))).length))).setv (Hb ⟨14, by decide⟩) (0 + l.getD 14 0))).seth (sk x 113) ((Data.unaryList (l.take (15 + 1))).length))).setv (Hb ⟨15, by decide⟩) (0 + l.getD 15 0))

theorem hC1_run (σ : WState (LNS x) LNR) (l : List ℕ) (tail : List Bool) (hl : 16 ≤ l.length)
    (hst : σ.st (sk x 113) = Data.unaryList l ++ tail) (hsh : σ.sh (sk x 113) = 0)
    (zH : ∀ i, σ.val (Hb i) = 0) (hlc : ∀ k, l.getD k 0 ≤ cap) :
    WExec cap (hC1W x) σ (hC1Out x σ l) (34 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl2 := UnaryPow.lin_le_sq cap
  have hlc0 := hlc 0
  have hlc1 := hlc 1
  have hlc2 := hlc 2
  have hlc3 := hlc 3
  have hlc4 := hlc 4
  have hlc5 := hlc 5
  have hlc6 := hlc 6
  have hlc7 := hlc 7
  have hlc8 := hlc 8
  have hlc9 := hlc 9
  have hlc10 := hlc 10
  have hlc11 := hlc 11
  have hlc12 := hlc 12
  have hlc13 := hlc 13
  have hlc14 := hlc 14
  have hlc15 := hlc 15
  unfold hC1W hC1Out
  exact (seqD cap 34 1 (readItem_at cap (sk x 113) (Hb ⟨0, by decide⟩) l tail 0 (by omega) 0 σ (by simp [hst]) (by simp [hsh, Data.unaryList]) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 0; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨1, by decide⟩) l tail 1 (by omega) 0 ((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 1; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨2, by decide⟩) l tail 2 (by omega) 0 ((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 2; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨3, by decide⟩) l tail 3 (by omega) 0 ((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 3; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨4, by decide⟩) l tail 4 (by omega) 0 ((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 4; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨5, by decide⟩) l tail 5 (by omega) 0 ((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 5; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨6, by decide⟩) l tail 6 (by omega) 0 ((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 6; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨7, by decide⟩) l tail 7 (by omega) 0 ((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 7; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨8, by decide⟩) l tail 8 (by omega) 0 ((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 8; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨9, by decide⟩) l tail 9 (by omega) 0 ((((((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0))).seth (sk x 113) ((Data.unaryList (l.take (8 + 1))).length))).setv (Hb ⟨8, by decide⟩) (0 + l.getD 8 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 9; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨10, by decide⟩) l tail 10 (by omega) 0 ((((((((((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0))).seth (sk x 113) ((Data.unaryList (l.take (8 + 1))).length))).setv (Hb ⟨8, by decide⟩) (0 + l.getD 8 0))).seth (sk x 113) ((Data.unaryList (l.take (9 + 1))).length))).setv (Hb ⟨9, by decide⟩) (0 + l.getD 9 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 10; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨11, by decide⟩) l tail 11 (by omega) 0 ((((((((((((((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0))).seth (sk x 113) ((Data.unaryList (l.take (8 + 1))).length))).setv (Hb ⟨8, by decide⟩) (0 + l.getD 8 0))).seth (sk x 113) ((Data.unaryList (l.take (9 + 1))).length))).setv (Hb ⟨9, by decide⟩) (0 + l.getD 9 0))).seth (sk x 113) ((Data.unaryList (l.take (10 + 1))).length))).setv (Hb ⟨10, by decide⟩) (0 + l.getD 10 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 11; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨12, by decide⟩) l tail 12 (by omega) 0 ((((((((((((((((((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0))).seth (sk x 113) ((Data.unaryList (l.take (8 + 1))).length))).setv (Hb ⟨8, by decide⟩) (0 + l.getD 8 0))).seth (sk x 113) ((Data.unaryList (l.take (9 + 1))).length))).setv (Hb ⟨9, by decide⟩) (0 + l.getD 9 0))).seth (sk x 113) ((Data.unaryList (l.take (10 + 1))).length))).setv (Hb ⟨10, by decide⟩) (0 + l.getD 10 0))).seth (sk x 113) ((Data.unaryList (l.take (11 + 1))).length))).setv (Hb ⟨11, by decide⟩) (0 + l.getD 11 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 12; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨13, by decide⟩) l tail 13 (by omega) 0 ((((((((((((((((((((((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0))).seth (sk x 113) ((Data.unaryList (l.take (8 + 1))).length))).setv (Hb ⟨8, by decide⟩) (0 + l.getD 8 0))).seth (sk x 113) ((Data.unaryList (l.take (9 + 1))).length))).setv (Hb ⟨9, by decide⟩) (0 + l.getD 9 0))).seth (sk x 113) ((Data.unaryList (l.take (10 + 1))).length))).setv (Hb ⟨10, by decide⟩) (0 + l.getD 10 0))).seth (sk x 113) ((Data.unaryList (l.take (11 + 1))).length))).setv (Hb ⟨11, by decide⟩) (0 + l.getD 11 0))).seth (sk x 113) ((Data.unaryList (l.take (12 + 1))).length))).setv (Hb ⟨12, by decide⟩) (0 + l.getD 12 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 13; omega)) (by omega) (by omega)
      (seqD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨14, by decide⟩) l tail 14 (by omega) 0 ((((((((((((((((((((((((((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0))).seth (sk x 113) ((Data.unaryList (l.take (8 + 1))).length))).setv (Hb ⟨8, by decide⟩) (0 + l.getD 8 0))).seth (sk x 113) ((Data.unaryList (l.take (9 + 1))).length))).setv (Hb ⟨9, by decide⟩) (0 + l.getD 9 0))).seth (sk x 113) ((Data.unaryList (l.take (10 + 1))).length))).setv (Hb ⟨10, by decide⟩) (0 + l.getD 10 0))).seth (sk x 113) ((Data.unaryList (l.take (11 + 1))).length))).setv (Hb ⟨11, by decide⟩) (0 + l.getD 11 0))).seth (sk x 113) ((Data.unaryList (l.take (12 + 1))).length))).setv (Hb ⟨12, by decide⟩) (0 + l.getD 12 0))).seth (sk x 113) ((Data.unaryList (l.take (13 + 1))).length))).setv (Hb ⟨13, by decide⟩) (0 + l.getD 13 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 14; omega)) (by omega) (by omega)
      (endD cap _ 1 (readItem_at cap (sk x 113) (Hb ⟨15, by decide⟩) l tail 15 (by omega) 0 ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((σ).seth (sk x 113) ((Data.unaryList (l.take (0 + 1))).length))).setv (Hb ⟨0, by decide⟩) (0 + l.getD 0 0))).seth (sk x 113) ((Data.unaryList (l.take (1 + 1))).length))).setv (Hb ⟨1, by decide⟩) (0 + l.getD 1 0))).seth (sk x 113) ((Data.unaryList (l.take (2 + 1))).length))).setv (Hb ⟨2, by decide⟩) (0 + l.getD 2 0))).seth (sk x 113) ((Data.unaryList (l.take (3 + 1))).length))).setv (Hb ⟨3, by decide⟩) (0 + l.getD 3 0))).seth (sk x 113) ((Data.unaryList (l.take (4 + 1))).length))).setv (Hb ⟨4, by decide⟩) (0 + l.getD 4 0))).seth (sk x 113) ((Data.unaryList (l.take (5 + 1))).length))).setv (Hb ⟨5, by decide⟩) (0 + l.getD 5 0))).seth (sk x 113) ((Data.unaryList (l.take (6 + 1))).length))).setv (Hb ⟨6, by decide⟩) (0 + l.getD 6 0))).seth (sk x 113) ((Data.unaryList (l.take (7 + 1))).length))).setv (Hb ⟨7, by decide⟩) (0 + l.getD 7 0))).seth (sk x 113) ((Data.unaryList (l.take (8 + 1))).length))).setv (Hb ⟨8, by decide⟩) (0 + l.getD 8 0))).seth (sk x 113) ((Data.unaryList (l.take (9 + 1))).length))).setv (Hb ⟨9, by decide⟩) (0 + l.getD 9 0))).seth (sk x 113) ((Data.unaryList (l.take (10 + 1))).length))).setv (Hb ⟨10, by decide⟩) (0 + l.getD 10 0))).seth (sk x 113) ((Data.unaryList (l.take (11 + 1))).length))).setv (Hb ⟨11, by decide⟩) (0 + l.getD 11 0))).seth (sk x 113) ((Data.unaryList (l.take (12 + 1))).length))).setv (Hb ⟨12, by decide⟩) (0 + l.getD 12 0))).seth (sk x 113) ((Data.unaryList (l.take (13 + 1))).length))).setv (Hb ⟨13, by decide⟩) (0 + l.getD 13 0))).seth (sk x 113) ((Data.unaryList (l.take (14 + 1))).length))).setv (Hb ⟨14, by decide⟩) (0 + l.getD 14 0)) (by simp [hst]) (by simp) (by simp [Function.update_apply, Fin.ext_iff, Hb_val, rv_dK, rv_XA, rv_XB, rv_TM, zH]) (by have := hlc 15; omega)) rfl (by omega) (by omega)))))))))))))))))

theorem getD_hs16 (hs t : List ℕ) (hhs : hs.length = 16) (i : ℕ) : (hs ++ t).getD (16 + i) 0 = t.getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

/-- Phase C2: the carriers' lengths summed into `XA` (`|carriers| ≤ 2` items), `|tupleG|` into `XB`. -/
def hC2W : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Hb 0) dK TM) (.seq (.ifr dK (.seq (readItemW (sk x 113) XA) (.seq (.dec dK)
    (.ifr dK (readItemW (sk x 113) XA) .skip))) .skip) (readItemW (sk x 113) XB))

theorem hC2_run (σ : WState (LNS x) LNR) (hs xs : List ℕ) (tg : ℕ) (tail : List Bool) (hhs : hs.length = 16)
    (hxs : xs.length ≤ 2) (hst : σ.st (sk x 113) = Data.unaryList (hs ++ (xs ++ [tg])) ++ tail)
    (hsh : σ.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take 16)).length) (h0 : σ.val (Hb 0) = xs.length)
    (zK : σ.val dK = 0) (zA : σ.val XA = 0) (zB : σ.val XB = 0) (zT : σ.val TM = 0)
    (hlc : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hsum : xs.sum + tg + 4 ≤ cap) :
    ∃ τ c, WExec cap (hC2W x) σ τ c ∧ c ≤ 8 * UnaryPow.sq cap ∧ τ.val XA = xs.sum ∧ τ.val XB = tg ∧
      (∀ r, r ≠ dK → r ≠ XA → r ≠ XB → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
      (∀ s', s' ≠ sk x 113 → τ.sh s' = σ.sh s') ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have nKA : dK ≠ XA := by decide
  have nKB : dK ≠ XB := by decide
  have nAB : XA ≠ XB := by decide
  have e1 := SparseNum.copy1 cap (Hb 0) dK TM (by decide) (by decide) (by decide) xs.length σ h0 zK zT (by omega)
  obtain ⟨σ1, h1⟩ : ∃ y, y = σ.setv dK xs.length := ⟨_, rfl⟩
  rw [← h1] at e1
  have g16 : (hs ++ (xs ++ [tg])).getD (16 + 0) 0 = (xs ++ [tg]).getD 0 0 := getD_hs16 hs _ hhs 0
  have g17 : (hs ++ (xs ++ [tg])).getD (16 + 1) 0 = (xs ++ [tg]).getD 1 0 := getD_hs16 hs _ hhs 1
  have g18 : (hs ++ (xs ++ [tg])).getD (16 + 2) 0 = (xs ++ [tg]).getD 2 0 := getD_hs16 hs _ hhs 2
  have hlen : (hs ++ (xs ++ [tg])).length = 16 + xs.length + 1 := by simp [hhs]; omega
  have hst1 : σ1.st (sk x 113) = Data.unaryList (hs ++ (xs ++ [tg])) ++ tail := by rw [h1]; exact hst
  have hsh1 : σ1.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take 16)).length := by rw [h1]; exact hsh
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, t⟩⟩⟩
  · -- no carriers
    simp only [List.nil_append] at g16 g17 g18 hlen hst1 hsh1 hlc ⊢
    have e3 := readItem_at cap (sk x 113) XB (hs ++ [tg]) tail 16 (by simp [hhs]) 0 σ1 hst1 hsh1
      (by rw [h1]; simp [Function.update_apply, nKB.symm, zB]) (by have := hlc 16; omega)
    refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.ifrF (by rw [h1]; simp) (WExec.skip _)) e3), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · have := hlc 16; omega
    · rw [WState.setv_val, Function.update_of_ne nAB, WState.seth_val, h1, WState.setv_val,
        Function.update_of_ne nKA.symm, zA]; rfl
    · simp only [WState.setv_val, Function.update_self, zero_add]
      simpa using g16
    · intro r a b c
      rw [WState.setv_val, Function.update_of_ne c, WState.seth_val, h1, WState.setv_val, Function.update_of_ne a]
    · rw [WState.setv_st, WState.seth_st, h1]; rfl
    · intro s' hs'
      rw [WState.setv_sh, WState.seth_sh, Function.update_of_ne hs', h1]; rfl
    · rw [WState.setv_cell, WState.seth_cell, h1]; rfl
  · -- one carrier
    have e2 := readItem_at cap (sk x 113) XA (hs ++ ([x0] ++ [tg])) tail 16 (by rw [hlen]; simp) 0 σ1 hst1 hsh1
      (by rw [h1]; simp [Function.update_apply, nKA.symm, zA]) (by have := hlc 16; omega)
    obtain ⟨σ2, h2⟩ : ∃ y, y = (σ1.seth (sk x 113) (Data.unaryList ((hs ++ ([x0] ++ [tg])).take (16 + 1))).length).setv
        XA (0 + (hs ++ ([x0] ++ [tg])).getD 16 0) := ⟨_, rfl⟩
    rw [← h2] at e2
    have e3 := SparseNum.dec1 cap dK 1 σ2 (by rw [h2, h1]; simp [Function.update_apply, nKA]) (by omega)
    obtain ⟨σ3, h3⟩ : ∃ y, y = σ2.setv dK (1 - 1) := ⟨_, rfl⟩
    rw [← h3] at e3
    have e4 := readItem_at cap (sk x 113) XB (hs ++ ([x0] ++ [tg])) tail 17 (by rw [hlen]; simp) 0 σ3
      (by rw [h3, h2]; simpa using hst1) (by rw [h3, h2]; simp)
      (by rw [h3, h2, h1]; simp [Function.update_apply, nKB.symm, nAB.symm, zB]) (by have := hlc 17; omega)
    refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.ifrT (by rw [h1]; simp) (WExec.seq e2 (WExec.seq e3
      (WExec.ifrF (by rw [h3]; simp) (WExec.skip _))))) e4), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hlc 16; have := hlc 17; omega
    · rw [WState.setv_val, Function.update_of_ne nAB, WState.seth_val, h3, WState.setv_val,
        Function.update_of_ne nKA.symm, h2, WState.setv_val, Function.update_self]
      have := g16; simp at this ⊢; omega
    · simp only [WState.setv_val, Function.update_self, zero_add]
      have := g17; simpa using this
    · intro r a b c
      rw [WState.setv_val, Function.update_of_ne c, WState.seth_val, h3, WState.setv_val, Function.update_of_ne a,
        h2, WState.setv_val, Function.update_of_ne b, WState.seth_val, h1, WState.setv_val, Function.update_of_ne a]
    · rw [WState.setv_st, WState.seth_st, h3, WState.setv_st, h2, WState.setv_st, WState.seth_st, h1]; rfl
    · intro s' hs'
      rw [WState.setv_sh, WState.seth_sh, Function.update_of_ne hs', h3, WState.setv_sh, h2, WState.setv_sh,
        WState.seth_sh, Function.update_of_ne hs', h1]; rfl
    · rw [WState.setv_cell, WState.seth_cell, h3, WState.setv_cell, h2, WState.setv_cell, WState.seth_cell, h1]; rfl
  · -- two carriers
    have e2 := readItem_at cap (sk x 113) XA (hs ++ ([x0, x1] ++ [tg])) tail 16 (by rw [hlen]; simp) 0 σ1 hst1 hsh1
      (by rw [h1]; simp [Function.update_apply, nKA.symm, zA]) (by have := hlc 16; omega)
    obtain ⟨σ2, h2⟩ : ∃ y, y = (σ1.seth (sk x 113) (Data.unaryList ((hs ++ ([x0, x1] ++ [tg])).take (16 + 1))).length).setv
        XA (0 + (hs ++ ([x0, x1] ++ [tg])).getD 16 0) := ⟨_, rfl⟩
    rw [← h2] at e2
    have e3 := SparseNum.dec1 cap dK 2 σ2 (by rw [h2, h1]; simp [Function.update_apply, nKA]) (by omega)
    obtain ⟨σ3, h3⟩ : ∃ y, y = σ2.setv dK (2 - 1) := ⟨_, rfl⟩
    rw [← h3] at e3
    have e3b := readItem_at cap (sk x 113) XA (hs ++ ([x0, x1] ++ [tg])) tail 17 (by rw [hlen]; simp)
      (0 + (hs ++ ([x0, x1] ++ [tg])).getD 16 0) σ3 (by rw [h3, h2]; simpa using hst1) (by rw [h3, h2]; simp)
      (by rw [h3, h2]; simp [Function.update_apply, nKA.symm]) (by have v16 : (hs ++ ([x0, x1] ++ [tg])).getD 16 0 = x0 := (by simpa using g16); have v17 : (hs ++ ([x0, x1] ++ [tg])).getD 17 0 = x1 := (by simpa using g17); rw [v16, v17]; simp at hsum; omega)
    obtain ⟨σ4, h4⟩ : ∃ y, y = (σ3.seth (sk x 113) (Data.unaryList ((hs ++ ([x0, x1] ++ [tg])).take (17 + 1))).length).setv
        XA (0 + (hs ++ ([x0, x1] ++ [tg])).getD 16 0 + (hs ++ ([x0, x1] ++ [tg])).getD 17 0) := ⟨_, rfl⟩
    rw [← h4] at e3b
    have e4 := readItem_at cap (sk x 113) XB (hs ++ ([x0, x1] ++ [tg])) tail 18 (by rw [hlen]; simp) 0 σ4
      (by rw [h4, h3, h2]; simpa using hst1) (by rw [h4]; simp)
      (by rw [h4, h3, h2, h1]; simp [Function.update_apply, nKB.symm, nAB.symm, zB]) (by have := hlc 18; omega)
    refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.ifrT (by rw [h1]; simp) (WExec.seq e2 (WExec.seq e3
      (WExec.ifrT (by rw [h3]; simp) e3b)))) e4), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hlc 16; have := hlc 17; have := hlc 18; omega
    · rw [WState.setv_val, Function.update_of_ne nAB, WState.seth_val, h4, WState.setv_val, Function.update_self]
      have a16 := g16; have a17 := g17; simp at a16 a17 ⊢; omega
    · simp only [WState.setv_val, Function.update_self, zero_add]
      have := g18; simpa using this
    · intro r a b c
      rw [WState.setv_val, Function.update_of_ne c, WState.seth_val, h4, WState.setv_val, Function.update_of_ne b,
        WState.seth_val, h3, WState.setv_val, Function.update_of_ne a, h2, WState.setv_val, Function.update_of_ne b,
        WState.seth_val, h1, WState.setv_val, Function.update_of_ne a]
    · rw [WState.setv_st, WState.seth_st, h4, WState.setv_st, WState.seth_st, h3, WState.setv_st, h2, WState.setv_st,
        WState.seth_st, h1]; rfl
    · intro s' hs'
      rw [WState.setv_sh, WState.seth_sh, Function.update_of_ne hs', h4, WState.setv_sh, WState.seth_sh,
        Function.update_of_ne hs', h3, WState.setv_sh, h2, WState.setv_sh, WState.seth_sh, Function.update_of_ne hs',
        h1]; rfl
    · rw [WState.setv_cell, WState.seth_cell, h4, WState.setv_cell, WState.seth_cell, h3, WState.setv_cell, h2,
        WState.setv_cell, WState.seth_cell, h1]; rfl
  · simp at hxs

end HashC

section HashD
variable (cap : ℕ) (x : ℕ)

def hbM0 : Fin 5 ↪ Fin LNR := ⟨![G 0, G 58, G 59, G 60, G 61], by decide⟩
def hbP : Fin 4 ↪ Fin LNR := ⟨![G 57, G 54, G 58, G 59], by decide⟩
def hbT1 : Fin 5 ↪ Fin LNR := ⟨![G 56, G 54, G 58, G 59, G 60], by decide⟩
def hbT2 : Fin 5 ↪ Fin LNR := ⟨![G 56, G 55, G 58, G 59, G 60], by decide⟩
@[simp] theorem hbM0_apply (i : Fin 5) : hbM0 i = ![G 0, G 58, G 59, G 60, G 61] i := rfl
@[simp] theorem hbP_apply (i : Fin 4) : hbP i = ![G 57, G 54, G 58, G 59] i := rfl
@[simp] theorem hbT1_apply (i : Fin 5) : hbT1 i = ![G 56, G 54, G 58, G 59, G 60] i := rfl
@[simp] theorem hbT2_apply (i : Fin 5) : hbT2 i = ![G 56, G 55, G 58, G 59, G 60] i := rfl

/-- Phase D1: the aux filter's parameters `errExp = e`, `len = 2Σ|X|`, `cap = (|carriers|+1)·4096·capT` in `G 2, G 1, G 0`. -/
def hD1W : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Hb 13) (G 2) TM) (.seq (FinalPass.Hash4.wcopyR XA (G 1) TM) (.seq (dbl (G 1) TM)
  (.seq (FinalPass.Hash4.wcopyR (Hb 0) (G 0) TM) (.seq (.inc (G 0)) (.seq (StarNums.incN (G 58) 4096)
  (.seq (mulByW hbM0) (.seq (WM.clear (G 58)) (.seq (FinalPass.Hash4.wcopyR (Hb 1) (G 58) TM) (.seq (mulByW hbM0)
    (WM.clear (G 58)))))))))))

def hD1Out (σ : WState (LNS x) LNR) (ee sx nc capT : ℕ) : WState (LNS x) LNR :=
  ((((((((((((((((((((((σ).setv ((G 2)) (ee))).setv ((G 1)) (sx))).setv (G 1) (2 * (sx)))).setv ((G 0)) (nc))).setv (G 0) (nc + 1))).setv (G 58) (4096))).setv (G 0) ((nc + 1) * 4096))).setv (G 58) (0))).setv ((G 58)) (capT))).setv (G 0) ((nc + 1) * 4096 * capT))).setv (G 58) (0))

theorem hD1_run (σ : WState (LNS x) LNR) (ee sx nc capT : ℕ) (h13 : σ.val (Hb 13) = ee) (hA : σ.val XA = sx)
    (h0 : σ.val (Hb 0) = nc) (h1 : σ.val (Hb 1) = capT) (zG : ∀ i, σ.val (G i) = 0) (zT : σ.val TM = 0)
    (hc : ee + 2 * sx + (nc + 1) * 4096 * capT + (nc + 1) * 4096 + capT + 10 ≤ cap) :
    WExec cap (hD1W x) σ (hD1Out x σ ee sx nc capT) (28 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hm1 : (nc + 1) * 4096 ≤ (nc + 1) * 4096 * capT ∨ capT = 0 := by
    rcases Nat.eq_zero_or_pos capT with h | h
    · right; exact h
    · left; exact Nat.le_mul_of_pos_right _ h
  have hm2 : nc + 1 ≤ (nc + 1) * 4096 := by omega
  unfold hD1W hD1Out
  exact (seqD cap 28 1 (copy1 cap (Hb 13) (G 2) TM (by decide) (by decide) (by decide) (ee) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap XA (G 1) TM (by decide) (by decide) (by decide) (sx) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (dbl1 cap (G 1) TM (by decide) (sx) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (Hb 0) (G 0) TM (by decide) (by decide) (by decide) (nc) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (inc1 cap (G 0) (nc) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (incN0 cap (G 58) 4096 _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 3 (mulBy1 cap hbM0 (nc + 1) 4096 _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (clear1 cap (G 58) 4096 _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (Hb 1) (G 58) TM (by decide) (by decide) (by decide) (capT) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) (by omega) (by omega)
      (seqD cap _ 3 (mulBy1 cap hbM0 ((nc + 1) * 4096) capT _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT, hbM0_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (endD cap _ 1 (clear1 cap (G 58) capT _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h13, hA, h0, h1, zG, zT]) (by omega)) rfl (by omega) (by omega))))))))))))

/-- Phase D3: the pool size `|thrPool| = 2Σ|X| + M` (`G 7`, `M = |thrOccs|` W6's `hashNums` entry `8`), the index layout (`G 53 = nE`, `G 52 = G 41 = 1`, `G 55 = 5`),
`2^{2kh}` (`G 54`), `TOT = nE·2^{2kh}·5` (`G 56`), one FILTER row (`dNC = 1`). -/
def hD3W : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (G 1) (G 7) TM) (.seq (addTo (Hb 8) (G 7) TM) (.seq (FinalPass.Hash4.wcopyR (G 21) (G 53) TM)
  (.seq (.inc (G 52)) (.seq (.inc (G 41)) (.seq (StarNums.incN (G 55) 5) (.seq (FinalPass.Hash4.wcopyR (SGb 8) (G 57) TM)
  (.seq (dbl (G 57) (G 58)) (.seq (pow2W hbP) (.seq (WM.clear (G 57)) (.seq (FinalPass.Hash4.wcopyR (G 21) (G 56) TM)
  (.seq (mulByW hbT1) (.seq (mulByW hbT2) (.inc dNC)))))))))))))

def hD3Out (σ : WState (LNS x) LNR) (sx mo nE kh : ℕ) : WState (LNS x) LNR :=
  ((((((((((((((((((((((((((((σ).setv ((G 7)) (2 * sx))).setv (G 7) (2 * sx + mo))).setv ((G 53)) (nE))).setv (G 52) (0 + 1))).setv (G 41) (0 + 1))).setv (G 55) (5))).setv ((G 57)) (kh))).setv (G 57) (2 * (kh)))).setv (G 54) (2 ^ (2 * (kh))))).setv (G 57) (0))).setv ((G 56)) (nE))).setv (G 56) (nE * 2 ^ (2 * (kh))))).setv (G 56) (nE * 2 ^ (2 * (kh)) * 5))).setv (dNC) (0 + 1))

theorem hD3_run (σ : WState (LNS x) LNR) (sx mo nE kh : ℕ) (h1 : σ.val (G 1) = 2 * sx) (hM : σ.val (Hb 8) = mo)
    (h21 : σ.val (G 21) = nE) (h8 : σ.val (SGb 8) = kh) (zG7 : σ.val (G 7) = 0) (zG52 : σ.val (G 52) = 0)
    (zG53 : σ.val (G 53) = 0) (zG41 : σ.val (G 41) = 0) (zG55 : σ.val (G 55) = 0) (zG57 : σ.val (G 57) = 0)
    (zG54 : σ.val (G 54) = 0) (zG56 : σ.val (G 56) = 0) (zG58 : σ.val (G 58) = 0) (zG59 : σ.val (G 59) = 0)
    (zG60 : σ.val (G 60) = 0) (zT : σ.val TM = 0) (zNC : σ.val dNC = 0)
    (hc : 2 * sx + mo + nE + 2 ^ (2 * kh + 1) + nE * 2 ^ (2 * kh) * 5 + 10 ≤ cap) :
    WExec cap (hD3W x) σ (hD3Out x σ sx mo nE kh) (34 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hp : 2 ^ (2 * kh + 1) = 2 * 2 ^ (2 * kh) := by rw [pow_succ]; ring
  have hkh : 2 * kh < 2 ^ (2 * kh) := Nat.lt_two_pow_self
  have hm : nE * 2 ^ (2 * kh) ≤ nE * 2 ^ (2 * kh) * 5 := by omega
  unfold hD3W hD3Out
  exact (seqD cap 34 1 (copy1 cap (G 1) (G 7) TM (by decide) (by decide) (by decide) (2 * sx) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (add1 cap (Hb 8) (G 7) TM (by decide) (by decide) (by decide) (mo) (2 * sx) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (G 21) (G 53) TM (by decide) (by decide) (by decide) (nE) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (inc1 cap (G 52) 0 _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (inc1 cap (G 41) 0 _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (incN0 cap (G 55) 5 _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (SGb 8) (G 57) TM (by decide) (by decide) (by decide) (kh) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (dbl1 cap (G 57) (G 58) (by decide) (kh) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (SymQM.pow2v cap hbP (2 * (kh)) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbP_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbP_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbP_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbP_apply]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (clear1 cap (G 57) (2 * (kh)) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (G 21) (G 56) TM (by decide) (by decide) (by decide) (nE) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) (by omega) (by omega)
      (seqD cap _ 3 (mulBy1 cap hbT1 nE (2 ^ (2 * (kh))) _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT1_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT1_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT1_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT1_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT1_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 3 (mulBy1 cap hbT2 (nE * 2 ^ (2 * (kh))) 5 _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT2_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT2_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT2_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT2_apply]) (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC, hbT2_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (endD cap _ 1 (inc1 cap dNC 0 _ (by simp [Function.update_apply, Fin.ext_iff, G_val, H_val, Hb_val, SGb_val, rv_XA, rv_XB, rv_TM, rv_dNC, h1, hM, h21, h8, zG7, zG52, zG53, zG41, zG55, zG57, zG54, zG56, zG58, zG59, zG60, zT, zNC]) (by omega)) rfl (by omega) (by omega)))))))))))))))

end HashD

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
