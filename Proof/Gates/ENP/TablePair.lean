import Proof.Gates.ENP.TableEval
import Proof.Gates.ENP.ListedStep
import Proof.Gates.CheckedPCPP.NodeEmit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

namespace NearCubicGates.Close.ENP.TEmit

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.EmitNat NearCubicGates.Close.CheckedPCPP.NodeEmit
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicWires.RepairRepresentation

local notation "sCW" => (0 : Fin 4)
local notation "sG" => (1 : Fin 4)
local notation "sARGS" => (2 : Fin 4)
local notation "rR7" => (7 : Fin 40)
local notation "rTN" => (8 : Fin 40)
local notation "rA" => (16 : Fin 40)
local notation "rJJ" => (17 : Fin 40)
local notation "rX" => (18 : Fin 40)
local notation "rY" => (19 : Fin 40)
local notation "rBB" => (20 : Fin 40)
local notation "rW" => (21 : Fin 40)
local notation "rNP" => (22 : Fin 40)
local notation "rF1" => (23 : Fin 40)
local notation "rF2" => (24 : Fin 40)
local notation "rCA" => (25 : Fin 40)

/-- The writer's registers `0..7`. -/
def Rw : Fin 8 ↪ Fin 40 := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

theorem Rw_val (i : Fin 8) : (Rw i).val = i.val := rfl

def tLitT : NodeT 40 := ![([], 4), ([rW], 0), ([rW], 0)]
def tLitF : NodeT 40 := ![([], 2), ([rW], 0), ([], 0)]
def tAnd : NodeT 40 := ![([], 3), ([rF1], 0), ([rF2], 0)]

/-- One pair of a multiplexer group. -/
def pairBody : WMX 3 40 :=
  .seq (halve rX rY rBB) <|
  .seq (.wm (WM.readU sARGS rCA rW)) <|
  .seq (.ifr rBB (.wm (nodeW sG Rw rTN tLitT)) (.wm (nodeW sG Rw rTN tLitF))) <|
  .seq (WMX.inc rNP) <|
  .seq (.ifr rJJ (.wm (.seq (setR rF1 rTN [rNP] 0) (.seq (.dec rF1) (.dec rF1)))) (.wm (setR rF1 rTN [rA] 1))) <|
  .seq (.wm (setR rF2 rTN [rNP] 0)) <| .seq (WMX.dec rF2) <|
  .seq (.wm (nodeW sG Rw rTN tAnd)) <|
  .seq (WMX.inc rNP) <|
  .seq (clearReg rF1) <| .seq (clearReg rF2) <| .seq (clearReg rW) <|
  .seq (.ifr rBB (WMX.dec rBB) WMX.skip) <| .seq (.wm (WM.move rY rX)) (WMX.inc rJJ)

theorem hTR : ∀ i : Fin 8, rTN ≠ Rw i := by decide

/-- The clean-writer condition. -/
theorem clean_of (σ : WState 3 40) (h : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hT : σ.val rTN = 0) :
    Clean Rw rTN σ := ⟨fun i hi => h _ (by have := i.isLt; simp [Rw_val]; omega), hT⟩

theorem Rw7 : Rw 7 = rR7 := rfl

theorem fin40_cases {P : Fin 40 → Prop} (h : ∀ k (hk : k < 40), P ⟨k, hk⟩) : ∀ j, P j := fun j => h j.val j.isLt

theorem native_len_le {n : ℕ} (nd : BooleanNode n) (V : ℕ) (hV : ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V) :
    (PCPPRequestNodeSchema.native nd).length ≤ 6 * V + 9 := by
  rw [native_len]
  simp only [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
  have h0 := natBitLength_le (PCPPRequestNodeSchema.fields nd 0)
  have h1 := natBitLength_le (PCPPRequestNodeSchema.fields nd 1)
  have h2 := natBitLength_le (PCPPRequestNodeSchema.fields nd 2)
  have := hV 0; have := hV 1; have := hV 2
  omega

/-- The cost bound of one pair. -/
def pairCost (u w V : ℕ) : ℕ := 10 * u + 15 * w + 2 * nodeCost V + 100 * (V + 10)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One pair of a multiplexer group** (`sec:all-lengths` stage 2): writes `lit (a_j) w` and `and gIdx np`. -/
theorem pairBody_exec {ℓ : ℕ} (cap : ℕ) (σ : WState 3 40) (u w j np a : ℕ)
    (hX : σ.val rX = u) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0) (hW : σ.val rW = 0) (hF1 : σ.val rF1 = 0)
    (hF2 : σ.val rF2 = 0) (hJ : σ.val rJJ = j) (hNP : σ.val rNP = np) (hA : σ.val rA = a)
    (hj : 1 ≤ j → 1 ≤ np)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hT : σ.val rTN = 0) (hG : σ.sh sG = (σ.st sG).length)
    (hones : ∀ k < w, readTapeBit (σ.st sARGS) (σ.sh sARGS + k) = true)
    (hend : readTapeBit (σ.st sARGS) (σ.sh sARGS + w) = false)
    (hcap : u + w + np + a + j + σ.val rCA + σ.val rR7 + 200 * (np + w + a + 10) ≤ cap) :
    WXExec cap pairBody σ
      (appendO ((((((σ.setv rX (u / 2)).setv rNP (np + 2)).setv rJJ (j + 1)).seth sARGS (σ.sh sARGS + w + 1)).setv
        rCA (σ.val rCA + w + 1))) sG rR7
        (marks (PCPPRequestNodeSchema.native (TCirc.lit (ℓ := ℓ) (decide (u % 2 = 1)) w) ++
          PCPPRequestNodeSchema.native (.and (if j = 0 then 1 + a else np - 1) np : BooleanNode (TCirc.T ℓ)))))
      (pairCost u w (np + w + a + 4)) := by
  have hbl : ∀ x, natBitLength x ≤ x + 1 := natBitLength_le
  set V := np + w + a + 4 with hV
  -- 1. halve
  have h1 := halve_exec (cap := cap) rX rY rBB (by decide) (by decide) (by decide) u σ hX hBB
    (by rw [hY]; omega) (by omega) (by omega)
  set σ1 := ((σ.setv rX 0).setv rY (σ.val rY + u / 2)).setv rBB (u % 2) with hσ1
  -- 2. read w
  have h2 := WXExec.wm (wreadU_spec (cap := cap) sARGS rCA rW (by decide) w σ1
    (by simpa [σ1] using hones) (by simpa [σ1] using hend) (by simp [σ1]; omega) (by simp [σ1, hW]; omega))
  set σ2 := ((σ1.seth sARGS (σ1.sh sARGS + w + 1)).setv rCA (σ1.val rCA + w + 1)).setv rW (σ1.val rW + w) with hσ2
  have hσ2W : σ2.val rW = w := by simp [σ2, σ1, hW]
  have hσ2cl : Clean Rw rTN σ2 := clean_of σ2 (fun r hr => by
    have := hwr r hr
    simp only [σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all) (by simp [σ2, σ1, hT])
  have hσ2G : σ2.sh sG = (σ2.st sG).length := by simp [σ2, σ1, hG]
  -- 3. the literal
  have h3 : WXExec cap (.ifr rBB (.wm (nodeW sG Rw rTN tLitT)) (.wm (nodeW sG Rw rTN tLitF))) σ2
      (appendO σ2 sG rR7 (marks (PCPPRequestNodeSchema.native (TCirc.lit (ℓ := ℓ) (decide (u % 2 = 1)) w))))
      (nodeCost V + 1) := by
    have hB2 : σ2.val rBB = u % 2 := by simp [σ2, σ1]
    by_cases hm : u % 2 = 1
    · have hn := nodeW_spec cap sG Rw rTN hTR tLitT (by intro i; fin_cases i <;> simp [tLitT, FieldOK] <;> decide)
        (.or w w : BooleanNode (TCirc.T ℓ)) σ2
        (by intro i; fin_cases i <;> simp [fieldVal, regSum, tLitT, PCPPRequestNodeSchema.fields, hσ2W])
        (by intro i; fin_cases i <;> simp [tLitT]) V
        (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega) hσ2cl hσ2G
        (by
          have := native_len_le (.or w w : BooleanNode (TCirc.T ℓ)) V
            (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
          simp [σ2, σ1, Rw7]; omega)
      rw [Rw7] at hn
      have hlit : (TCirc.lit (ℓ := ℓ) (decide (u % 2 = 1)) w) = .or w w := by simp [TCirc.lit, hm]
      rw [hlit]
      exact WXExec.ifrT (by rw [hB2, hm]; decide) (WXExec.wm hn)
    · have hm0 : u % 2 = 0 := by omega
      have hn := nodeW_spec cap sG Rw rTN hTR tLitF (by intro i; fin_cases i <;> simp [tLitF, FieldOK] <;> decide)
        (.not w : BooleanNode (TCirc.T ℓ)) σ2
        (by intro i; fin_cases i <;> simp [fieldVal, regSum, tLitF, PCPPRequestNodeSchema.fields, hσ2W])
        (by intro i; fin_cases i <;> simp [tLitF]) V
        (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega) hσ2cl hσ2G
        (by
          have := native_len_le (.not w : BooleanNode (TCirc.T ℓ)) V
            (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
          simp [σ2, σ1, Rw7]; omega)
      rw [Rw7] at hn
      have hlit : (TCirc.lit (ℓ := ℓ) (decide (u % 2 = 1)) w) = .not w := by simp [TCirc.lit, hm]
      rw [hlit]
      exact WXExec.ifrF (by rw [hB2, hm0]) (WXExec.wm hn)
  set L := (marks (PCPPRequestNodeSchema.native (TCirc.lit (ℓ := ℓ) (decide (u % 2 = 1)) w))) with hL
  have hLlen : L.length ≤ 12 * V + 18 := by
    have := native_len_le (TCirc.lit (ℓ := ℓ) (decide (u % 2 = 1)) w) V (by
      intro i; unfold TCirc.lit; split <;> fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
    rw [hL, marks_len]; omega
  set σ3 := appendO σ2 sG rR7 L with hσ3
  -- 4. NP := np + 1
  have h4 := WXExec.inc cap rNP σ3 (by simp [σ3, σ2, σ1, hNP]; omega)
  set σ4 := σ3.setv rNP (σ3.val rNP + 1) with hσ4
  have hNP4 : σ4.val rNP = np + 1 := by simp [σ4, σ3, σ2, σ1, hNP]

  set g := (if j = 0 then 1 + a else np - 1) with hg
  have h5 : WXExec cap (.ifr rJJ (.wm (.seq (setR rF1 rTN [rNP] 0) (.seq (.dec rF1) (.dec rF1))))
      (.wm (setR rF1 rTN [rA] 1))) σ4 (σ4.setv rF1 g) (30 * (np + a + 5)) := by
    have hJ4 : σ4.val rJJ = j := by simp [σ4, σ3, σ2, σ1, hJ]
    have hT4 : σ4.val rTN = 0 := by simp [σ4, σ3, σ2, σ1, hT]
    have hF14 : σ4.val rF1 = 0 := by simp [σ4, σ3, σ2, σ1, hF1]
    by_cases hj0 : j = 0
    · have hs := setR_spec cap (D := rF1) (T := rTN) (by decide) [rA] 1 σ4 (by simp) hT4 (by rw [hF14]; omega)
        (by simp [regSum, σ4, σ3, σ2, σ1, hA]; omega)
      refine WXExec.ifrF (by rw [hJ4, hj0]) (WXExec.wm (WExec.cast cap hs ?_ ?_))
      · simp [regSum, σ4, σ3, σ2, σ1, hA, hg, hj0]; ring_nf
      · simp [regSum, σ4, σ3, σ2, σ1, hA, hF14]; omega
    · have hnp := hj (by omega)
      have hs := setR_spec cap (D := rF1) (T := rTN) (by decide) [rNP] 0 σ4 (by simp) hT4 (by rw [hF14]; omega)
        (by simp [regSum, hNP4]; omega)
      have hs1 := WExec.dec (cap := cap) rF1 (σ4.setv rF1 (regSum σ4 [rNP] + 0)) (by simp [regSum, hNP4]; omega)
      have hs2 := WExec.dec (cap := cap) rF1 ((σ4.setv rF1 (regSum σ4 [rNP] + 0)).setv rF1
        ((σ4.setv rF1 (regSum σ4 [rNP] + 0)).val rF1 - 1)) (by simp [regSum, hNP4]; omega)
      refine WXExec.ifrT (by rw [hJ4]; exact hj0) (WXExec.wm (WExec.cast cap (WExec.seq hs (WExec.seq hs1 hs2)) ?_ ?_))
      · simp [regSum, hNP4, hg, hj0, wsetv_setv]
      · simp [regSum, hNP4, hF14]; omega
  set σ5 := σ4.setv rF1 g with hσ5

  have hT5 : σ5.val rTN = 0 := by simp [σ5, σ4, σ3, σ2, σ1, hT]
  have hF25 : σ5.val rF2 = 0 := by simp [σ5, σ4, σ3, σ2, σ1, hF2]
  have h6 := WXExec.wm (setR_spec cap (D := rF2) (T := rTN) (by decide) [rNP] 0 σ5 (by simp) hT5
    (by rw [hF25]; omega) (by simp [regSum, σ5, hNP4]; omega))
  have h7 := WXExec.dec cap rF2 (σ5.setv rF2 (regSum σ5 [rNP] + 0)) (by simp [regSum, σ5, hNP4]; omega)
  set σ7 := σ5.setv rF2 np with hσ7
  have e7 : (σ5.setv rF2 (regSum σ5 [rNP] + 0)).setv rF2 ((σ5.setv rF2 (regSum σ5 [rNP] + 0)).val rF2 - 1) = σ7 := by
    simp [σ7, regSum, σ5, hNP4, wsetv_setv]
  rw [e7] at h7
  -- 8. the conjunction
  have hσ7cl : Clean Rw rTN σ7 := clean_of σ7 (fun r hr => by
    have := hwr r hr
    simp only [σ7, σ5, σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, appendO_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all) (by simp [σ7, hT5])
  have hσ7G : σ7.sh sG = (σ7.st sG).length := by simp [σ7, σ5, σ4, σ3, σ2, σ1, hG]
  have hn8 := nodeW_spec cap sG Rw rTN hTR tAnd (by intro i; fin_cases i <;> simp [tAnd, FieldOK] <;> decide)
    (.and g np : BooleanNode (TCirc.T ℓ)) σ7
    (by intro i; fin_cases i <;> simp [fieldVal, regSum, tAnd, PCPPRequestNodeSchema.fields, σ7, σ5])
    (by intro i; fin_cases i <;> simp [tAnd]) V
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields, hg] <;> (try split) <;> omega) hσ7cl hσ7G
    (by
      have := native_len_le (.and g np : BooleanNode (TCirc.T ℓ)) V
        (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields, hg] <;> (try split) <;> omega)
      simp [σ7, σ5, σ4, σ3, σ2, σ1, Rw7]; omega)
  rw [Rw7] at hn8
  have h8 := WXExec.wm hn8
  set Gb := marks (PCPPRequestNodeSchema.native (.and g np : BooleanNode (TCirc.T ℓ))) with hGb
  set σ8 := appendO σ7 sG rR7 Gb with hσ8
  -- 9. NP := np + 2
  have h9 := WXExec.inc cap rNP σ8 (by simp [σ8, σ7, σ5, hNP4]; omega)
  set σ9 := σ8.setv rNP (σ8.val rNP + 1) with hσ9

  have h10 := clearReg_exec (cap := cap) rF1 g σ9 (by simp [σ9, σ8, σ7, σ5]) (by rw [hg]; split <;> omega)
  set σ10 := σ9.setv rF1 0 with hσ10
  have h11 := clearReg_exec (cap := cap) rF2 np σ10 (by simp [σ10, σ9, σ8, σ7]) (by omega)
  set σ11 := σ10.setv rF2 0 with hσ11
  have h12 := clearReg_exec (cap := cap) rW w σ11 (by simp [σ11, σ10, σ9, σ8, σ7, σ5, σ4, σ3, σ2, σ1, hW])
    (by omega)
  set σ12 := σ11.setv rW 0 with hσ12
  -- 13. BB := 0
  have hB12 : σ12.val rBB = u % 2 := by simp [σ12, σ11, σ10, σ9, σ8, σ7, σ5, σ4, σ3, σ2, σ1]
  have h13 : WXExec cap (.ifr rBB (WMX.dec rBB) WMX.skip) σ12 (σ12.setv rBB 0) 2 := by
    by_cases hm : u % 2 = 1
    · have := WXExec.ifrT (Q := WMX.skip) (by rw [hB12, hm]; decide)
        (WXExec.dec cap rBB σ12 (by rw [hB12, hm]; omega))
      refine WXExec.cast cap this ?_ le_rfl
      rw [hB12, hm]
    · have hm0 : u % 2 = 0 := by omega
      have := WXExec.ifrF (P := WMX.dec rBB) (by rw [hB12, hm0]) (WXExec.skip cap σ12)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      conv_lhs => rw [← wsetv_same σ12 rBB]
      rw [hB12, hm0]
  set σ13 := σ12.setv rBB 0 with hσ13
  -- 14. X := u / 2
  have hY13 : σ13.val rY = u / 2 := by simp [σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ5, σ4, σ3, σ2, σ1, hY]
  have hX13 : σ13.val rX = 0 := by simp [σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ5, σ4, σ3, σ2, σ1]
  have h14 := WXExec.wm (wmove_spec (cap := cap) rY rX (by decide) (u / 2) σ13 hY13 (by rw [hY13]; omega)
    (by rw [hY13, hX13]; omega))
  set σ14 := (σ13.setv rY 0).setv rX (σ13.val rX + σ13.val rY) with hσ14
  -- 15. JJ := j + 1
  have h15 := WXExec.inc cap rJJ σ14 (by simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ5, σ4, σ3, σ2, σ1, hJ]; omega)
  have hfin : σ14.setv rJJ (σ14.val rJJ + 1) =
      appendO ((((((σ.setv rX (u / 2)).setv rNP (np + 2)).setv rJJ (j + 1)).seth sARGS (σ.sh sARGS + w + 1)).setv
        rCA (σ.val rCA + w + 1))) sG rR7 (L ++ Gb) := by
    apply WState.eq
    · funext k; fin_cases k <;> simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ5, σ4, σ3, σ2, σ1] <;> omega
    · funext k; fin_cases k <;> simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ5, σ4, σ3, σ2, σ1]
    · funext k; revert k; apply fin40_cases; intro k hk
      interval_cases k <;> simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ5, σ4, σ3, σ2, σ1, hX, hY, hBB, hW, hF1, hF2,
        hJ, hNP] <;> omega
    · rfl
  rw [hfin] at h15
  rw [NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
  refine WXExec.mono (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5 (WXExec.seq h6
    (WXExec.seq h7 (WXExec.seq h8 (WXExec.seq h9 (WXExec.seq h10 (WXExec.seq h11 (WXExec.seq h12 (WXExec.seq h13
    (WXExec.seq h14 h15)))))))))))))) ?_
  unfold pairCost
  have : g ≤ V := by rw [hg]; split <;> omega
  have hnc : 30 * (np + a + 5) + 18 * (np + 1) + 4 + 3 * g + 3 * np + 3 * w + 100 ≤ 100 * (V + 10) := by omega
  have hu2 : u / 2 ≤ u := Nat.div_le_self _ _
  simp only [regSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have e1 : σ5.val rF2 = 0 := hF25
  have e2 : σ5.val rNP = np + 1 := by simp [σ5, hNP4]
  rw [e1, e2]
  simp only [List.length_singleton]
  have hgV : (if j = 0 then 1 + a else np - 1) ≤ V := by split <;> omega
  have hgV' : g ≤ V := by rw [hg]; exact hgV
  clear_value g
  omega

end NearCubicGates.Close.ENP.TEmit
