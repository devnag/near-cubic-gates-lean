import Proof.Gates.ENP.TableBlock

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
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

local notation "sCW" => (0 : Fin 4)
local notation "sG" => (1 : Fin 4)
local notation "sARGS" => (2 : Fin 4)
local notation "rR7" => (7 : Fin 40)
local notation "rTN" => (8 : Fin 40)
local notation "rL" => (9 : Fin 40)
local notation "rTT" => (10 : Fin 40)
local notation "rM" => (11 : Fin 40)
local notation "rKK" => (12 : Fin 40)
local notation "rZ" => (13 : Fin 40)
local notation "rBZ" => (14 : Fin 40)
local notation "rLC4" => (15 : Fin 40)
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
local notation "rSC" => (26 : Fin 40)
local notation "rRF" => (27 : Fin 40)
local notation "rRC" => (28 : Fin 40)
local notation "rRV" => (29 : Fin 40)
local notation "rRP" => (30 : Fin 40)
local notation "rRT" => (31 : Fin 40)
local notation "rTAG" => (32 : Fin 40)
local notation "rLC1" => (33 : Fin 40)
local notation "rIMG" => (34 : Fin 40)
local notation "rLC2" => (35 : Fin 40)
local notation "rLC3" => (36 : Fin 40)
local notation "rIMG2" => (37 : Fin 40)
local notation "rT2" => (38 : Fin 40)
local notation "rTMP" => (39 : Fin 40)

/-- The template of a constant-`false` filler. -/
def tZero : NodeT 40 := ![([], 0), ([], 0), ([], 0)]
/-- The template of a translated node: `(TAG, IMG2, IMG)`. -/
def tNode : NodeT 40 := ![([rTAG], 0), ([rIMG2], 0), ([rIMG], 0)]

/-- The native bytes of a constant-`false` node. -/
def zb : List Bool := PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode 0)

theorem zb_eq {n : ℕ} : PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode n) = zb := rfl

theorem zb_length : zb.length = 9 := by decide

/-- `TMP` constant-`false` fillers (consuming `TMP`). -/
def fillLoop : WMX 3 40 := .whr rTMP (.seq (WMX.dec rTMP) (.wm (nodeW sG Rw rTN tZero)))

set_option maxHeartbeats 4000000 in
theorem fillLoop_exec (cap : ℕ) : ∀ (n : ℕ) (σ : WState 3 40), σ.val rTMP = n → Clean Rw rTN σ →
    σ.sh sG = (σ.st sG).length → σ.val rR7 + 18 * n + 30 ≤ cap → n ≤ cap →
    WXExec cap fillLoop σ (appendO (σ.setv rTMP 0) sG rR7 (marks (List.replicate n zb).flatten))
      (n * (nodeCost 0 + 4) + 1)
  | 0, σ, hn, _, _, _, _ => by
    have e : appendO (σ.setv rTMP 0) sG rR7 (marks (List.replicate 0 zb).flatten) = σ := by
      simp only [List.replicate_zero, List.flatten_nil]
      rw [show marks [] = [] from rfl, appendO_nil, ← hn, wsetv_same]
    rw [e]
    exact WXExec.mono (WXExec.whrF hn) (by omega)
  | n + 1, σ, hn, hcl, hG, hc, hnc => by
    have h1 := WXExec.dec cap rTMP σ (by omega)
    set σ1 := σ.setv rTMP (σ.val rTMP - 1) with hσ1
    have hcl1 : Clean Rw rTN σ1 := ⟨fun i hi => by
      have := hcl.1 i hi
      have : Rw i ≠ rTMP := by fin_cases i <;> decide
      simp [σ1, Function.update_of_ne this]; assumption, by simp [σ1, hcl.2]⟩
    have h2 := nodeW_spec cap sG Rw rTN hTR tZero (by intro i; fin_cases i <;> simp [tZero, FieldOK])
      (BooleanNode.const false : BooleanNode 0) σ1
      (by intro i; fin_cases i <;> simp [fieldVal, regSum, tZero, PCPPRequestNodeSchema.fields])
      (by intro i; fin_cases i <;> simp [tZero]) 0
      (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields]) hcl1 (by simp [σ1, hG])
      (by rw [Rw7]; simp [σ1]; rw [show PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode 0) = zb
        from rfl, zb_length]; omega)
    rw [Rw7] at h2
    set σ2 := appendO σ1 sG rR7 (marks zb) with hσ2
    have hcl2 : Clean Rw rTN σ2 := ⟨fun i hi => by
      have := hcl1.1 i hi
      have : Rw i ≠ rR7 := by fin_cases i <;> simp_all <;> decide
      simp [σ2, Function.update_of_ne this]; assumption, by simp [σ2, hcl1.2]⟩
    have ih := fillLoop_exec cap n σ2 (by simp [σ2, σ1, hn]) hcl2 (by simp [σ2, σ1, hG])
      (by simp [σ2, σ1, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_len, zb_length]; omega) (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 (WXExec.wm h2)) ih) ?_ le_rfl)
      (by rw [Nat.succ_mul]; omega)
    have hz : (List.replicate (n + 1) zb).flatten = zb ++ (List.replicate n zb).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    rw [hz, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append, ← appendO_append]
    have e : σ2.setv rTMP 0 = appendO (σ.setv rTMP 0) sG rR7 (marks zb) := by
      rw [hσ2, ← appendO_setv _ _ _ _ (by decide), hσ1, wsetv_setv]
    rw [e]

/-- **A plain block's emission**: `K − 1` fillers, the node `(TAG, IMG2, IMG)`, `NP += K`, the field registers cleared. -/
def emitPlain : WMX 3 40 :=
  .seq (copyReg rKK rTMP rT2) <| .seq (WMX.dec rTMP) <| .seq fillLoop <| .seq (.wm (nodeW sG Rw rTN tNode)) <|
  .seq (.wm (addW rKK rNP rTN)) <| .seq (clearReg rTAG) <| .seq (clearReg rIMG2) (clearReg rIMG)

/-- The cost bound of a plain block. -/
def plainCost (k V : ℕ) : ℕ := 40 * k + k * (nodeCost 0 + 4) + nodeCost V + 10 * V + 30

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem emitPlain_exec {N : ℕ} (cap : ℕ) (σ : WState 3 40) (nd : BooleanNode N) (k np V : ℕ)
    (hTAG : σ.val rTAG = PCPPRequestNodeSchema.fields nd 0) (hIMG2 : σ.val rIMG2 = PCPPRequestNodeSchema.fields nd 1)
    (hIMG : σ.val rIMG = PCPPRequestNodeSchema.fields nd 2) (hV : ∀ i, PCPPRequestNodeSchema.fields nd i ≤ V)
    (hK : σ.val rKK = k) (hk : 1 ≤ k) (hNP : σ.val rNP = np) (hTMP : σ.val rTMP = 0) (hT2 : σ.val rT2 = 0)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hT : σ.val rTN = 0) (hG : σ.sh sG = (σ.st sG).length)
    (hcap : σ.val rR7 + 18 * k + 20 * V + 60 + np + k ≤ cap) :
    WXExec cap emitPlain σ
      (appendO ((((σ.setv rTAG 0).setv rIMG2 0).setv rIMG 0).setv rNP (np + k)) sG rR7
        (marks ((List.replicate (k - 1) zb).flatten ++ PCPPRequestNodeSchema.native nd)))
      (plainCost k V) := by
  have hnl := native_len_le nd V hV
  -- 1, 2. TMP := K − 1
  have h1 := copyReg_exec (cap := cap) rKK rTMP rT2 (by decide) (by decide) (by decide) k σ hK hT2
    (by rw [hTMP]; omega) (by omega)
  set σ1 := σ.setv rTMP (σ.val rTMP + k) with hσ1
  have h2 := WXExec.dec cap rTMP σ1 (by simp [σ1, hTMP]; omega)
  set σ2 := σ1.setv rTMP (σ1.val rTMP - 1) with hσ2
  -- 3. fillers
  have hcl2 : Clean Rw rTN σ2 := clean_of σ2 (fun r hr => by
    have := hwr r hr
    simp only [σ2, σ1, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all) (by simp [σ2, σ1, hT])
  have h3 := fillLoop_exec cap (k - 1) σ2 (by simp [σ2, σ1, hTMP]) hcl2 (by simp [σ2, σ1, hG])
    (by simp [σ2, σ1]; omega) (by omega)
  set σ3 := appendO (σ2.setv rTMP 0) sG rR7 (marks (List.replicate (k - 1) zb).flatten) with hσ3
  have hz : (marks (List.replicate (k - 1) zb).flatten).length = 18 * (k - 1) := by
    rw [NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_len]
    simp [List.length_flatten, zb_length]; ring
  -- 4. the node
  have hcl3 : Clean Rw rTN σ3 := clean_of σ3 (fun r hr => by
    have := hwr r hr
    have hr7 : r ≠ rR7 := by intro h; subst h; simp at hr
    simp only [σ3, σ2, σ1, appendO_val, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all) (by simp [σ3, σ2, σ1, hT])
  have h4 := nodeW_spec cap sG Rw rTN hTR tNode (by intro i; fin_cases i <;> simp [tNode, FieldOK] <;> decide)
    nd σ3 (by intro i; fin_cases i <;> simp [fieldVal, regSum, tNode, σ3, σ2, σ1, hTAG, hIMG2, hIMG])
    (by intro i; fin_cases i <;> simp [tNode]) V hV hcl3 (by simp [σ3, σ2, σ1, hG])
    (by rw [Rw7]; simp [σ3, σ2, σ1, hz]; omega)
  rw [Rw7] at h4
  set σ4 := appendO σ3 sG rR7 (marks (PCPPRequestNodeSchema.native nd)) with hσ4
  -- 5. NP += K
  have h5 := addW_spec (cap := cap) (A := rKK) (W := rNP) (T := rTN) (by decide) (by decide) (by decide) σ4
    (by simp [σ4, σ3, σ2, σ1, hT]) (by simp [σ4, σ3, σ2, σ1, hK, hNP]; omega)
  set σ5 := σ4.setv rNP (σ4.val rNP + σ4.val rKK) with hσ5
  -- 6–8. clear the field registers
  have h6 := clearReg_exec (cap := cap) rTAG _ σ5 rfl (by have := hV 0; simp [σ5, σ4, σ3, σ2, σ1, hTAG]; omega)
  set σ6 := σ5.setv rTAG 0 with hσ6
  have h7 := clearReg_exec (cap := cap) rIMG2 _ σ6 rfl (by have := hV 1; simp [σ6, σ5, σ4, σ3, σ2, σ1, hIMG2]; omega)
  set σ7 := σ6.setv rIMG2 0 with hσ7
  have h8 := clearReg_exec (cap := cap) rIMG _ σ7 rfl (by have := hV 2; simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hIMG]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq (WXExec.wm h4)
    (WXExec.seq (WXExec.wm h5) (WXExec.seq h6 (WXExec.seq h7 h8))))))) ?_ le_rfl) ?_
  · rw [NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1] <;> omega
    · funext i; fin_cases i <;> simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hTMP, hK, hNP] <;> omega
    · rfl
  · unfold plainCost
    have v0 := hV 0
    have v1 := hV 1
    have v2 := hV 2
    have hkm : (k - 1) * (nodeCost 0 + 4) ≤ k * (nodeCost 0 + 4) := Nat.mul_le_mul_right _ (by omega)
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hTAG, hIMG2, hIMG, hK]
    omega

/-! ## Field computations -/

/-- Read a child index `x`; `IMG := BZ + x·K + K − 1` (its image at the current seed). -/
def imgStep (ε : Bool) : WMX 3 40 :=
  .seq (.wm (readNatM ε sCW rRF rRC rRV rRP rRT)) <|
  .seq (.wm (setR rIMG rTN [rBZ, rKK] 0)) <| .seq (WMX.dec rIMG) mulLoop

/-- The cost bound of `imgStep`. -/
def imgCost (x k bz : ℕ) : ℕ :=
  (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) + 18 * (bz + k) + 20 + x * (18 * k + 7)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem imgStep_exec (ε : Bool) (cap : ℕ) (σ : WState 3 40) (x k bz : ℕ) (pre rest : List Bool)
    (hst : σ.st sCW = pre ++ enc ε (natWord x) ++ rest) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG : σ.val rIMG = 0) (hT : σ.val rTN = 0) (hBZ : σ.val rBZ = bz) (hK : σ.val rKK = k) (hk : 1 ≤ k)
    (hcap : 2 ^ (natBitLength x + 1) + bz + x * k + k + 10 ≤ cap) :
    WXExec cap (imgStep ε) σ
      ((σ.seth sCW (pre.length + stp ε * (natWord x).length)).setv rIMG (bz + x * k + k - 1)) (imgCost x k bz) := by
  have hxp : x < 2 ^ (natBitLength x) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hp2 : 2 ^ (natBitLength x + 1) = 2 * 2 ^ natBitLength x := by rw [pow_succ]; ring
  have h1 := WXExec.wm (readNatM_spec (cap := cap) ε sCW rRF rRC rRV rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x pre rest σ hst hsh hRF hRC hRP
    hRT (by rw [hRV]; omega))
  set σ1 := (σ.seth sCW (pre.length + stp ε * (natWord x).length)).setv rRV (σ.val rRV + x) with hσ1
  have h2 := WXExec.wm (setR_spec cap (D := rIMG) (T := rTN) (by decide) [rBZ, rKK] 0 σ1 (by simp) (by simp [σ1, hT])
    (by simp [σ1, hIMG] <;> omega) (by simp [σ1, regSum, hBZ, hK] <;> omega))
  set σ2 := σ1.setv rIMG (regSum σ1 [rBZ, rKK] + 0) with hσ2
  have h3 := WXExec.dec cap rIMG σ2 (by simp [σ2, σ1, regSum, hBZ, hK] <;> omega)
  set σ3 := σ2.setv rIMG (σ2.val rIMG - 1) with hσ3
  have h4 := mulLoop_exec cap x σ3 k (bz + k - 1) (by simp [σ3, σ2, σ1, hRV]) (by simp [σ3, σ2, σ1, hK])
    (by simp [σ3, σ2, σ1, regSum, hBZ, hK]) (by simp [σ3, σ2, σ1, hT]) (by omega) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 h4))) ?_ le_rfl) ?_
  · have he : bz + k - 1 + x * k = bz + x * k + k - 1 := by omega
    rw [he]
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ3, σ2, σ1]
    · funext i; fin_cases i <;> simp [σ3, σ2, σ1]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ3, σ2, σ1, hRV, hIMG]
    · rfl
  · unfold imgCost
    simp only [regSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    have e1 : σ1.val rBZ = bz := by simp [σ1, hBZ]
    have e2 : σ1.val rKK = k := by simp [σ1, hK]
    have e3 : σ1.val rIMG = 0 := by simp [σ1, hIMG]
    rw [e1, e2, e3]
    omega

def bitStep : WMX 3 40 :=
  .seq (copyReg rZ rX rT2) <|
  .seq (.whr rRV (.seq (WMX.dec rRV) (.seq (halve rX rY rBB) (.seq (.wm (WM.move rY rX)) (clearReg rBB))))) <|
  .seq (halve rX rY rBB) <| .seq (.wm (WM.move rBB rIMG2)) (clearReg rY)

theorem shiftLoop_exec (cap : ℕ) : ∀ (n : ℕ) (σ : WState 3 40) (u : ℕ), σ.val rRV = n → σ.val rX = u →
    σ.val rY = 0 → σ.val rBB = 0 → u ≤ cap → n ≤ cap → 1 ≤ cap →
    WXExec cap (.whr rRV (.seq (WMX.dec rRV) (.seq (halve rX rY rBB) (.seq (.wm (WM.move rY rX)) (clearReg rBB)))))
      σ ((σ.setv rRV 0).setv rX (u / 2 ^ n)) (n * (13 * u + 40) + 1)
  | 0, σ, u, hn, hu, _, _, _, _, _ => by
    have e : (σ.setv rRV 0).setv rX (u / 2 ^ 0) = σ := by
      rw [pow_zero, Nat.div_one, ← hu, ← hn, wsetv_same, wsetv_same]
    rw [e]
    exact WXExec.mono (WXExec.whrF hn) (by omega)
  | n + 1, σ, u, hn, hu, hY, hBB, hc, hnc, h1c => by
    have h1 := WXExec.dec cap rRV σ (by omega)
    set σ1 := σ.setv rRV (σ.val rRV - 1) with hσ1
    have h2 := halve_exec (cap := cap) rX rY rBB (by decide) (by decide) (by decide) u σ1 (by simp [σ1, hu])
      (by simp [σ1, hBB]) (by simp [σ1, hY]; omega) (by omega) h1c
    set σ2 := ((σ1.setv rX 0).setv rY (σ1.val rY + u / 2)).setv rBB (u % 2) with hσ2
    have hd : u / 2 ≤ u := Nat.div_le_self _ _
    have h3 := WXExec.wm (wmove_spec (cap := cap) rY rX (by decide) (u / 2) σ2 (by simp [σ2, σ1, hY])
      (by simp [σ2, σ1, hY]; omega) (by simp [σ2, σ1, hY]; omega))
    set σ3 := (σ2.setv rY 0).setv rX (σ2.val rX + σ2.val rY) with hσ3
    have hm : u % 2 ≤ 1 := by omega
    have h4 := clearReg_exec (cap := cap) rBB (u % 2) σ3 (by simp [σ3, σ2]) (by omega)
    set σ4 := σ3.setv rBB 0 with hσ4
    have hdu : u / 2 ≤ cap := by omega
    have ih := shiftLoop_exec cap n σ4 (u / 2) (by simp [σ4, σ3, σ2, σ1, hn]) (by simp [σ4, σ3, σ2, σ1, hY])
      (by simp [σ4, σ3, σ2]) (by simp [σ4]) hdu (by omega) h1c
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 h4)))
      ih) ?_ le_rfl) ?_
    · have hdiv : u / 2 / 2 ^ n = u / 2 ^ (n + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
      rw [hdiv]
      apply WState.eq <;> try rfl
      funext r; revert r; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ4, σ3, σ2, σ1, hY, hBB, hn]
    · have := Nat.mul_le_mul_left n (show 13 * (u / 2) + 40 ≤ 13 * u + 40 by omega)
      have e : (n + 1) * (13 * u + 40) = n * (13 * u + 40) + (13 * u + 40) := by ring
      rw [e]
      omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem bitStep_exec (cap : ℕ) (σ : WState 3 40) (z i : ℕ) (hRV : σ.val rRV = i) (hZ : σ.val rZ = z)
    (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0) (hT2 : σ.val rT2 = 0) (hI : σ.val rIMG2 = 0)
    (hcap : 2 * z + i + 2 ≤ cap) :
    WXExec cap bitStep σ ((σ.setv rRV 0).setv rIMG2 (z.testBit i).toNat) (i * (13 * z + 40) + 40 * z + 40) := by
  have h1 := copyReg_exec (cap := cap) rZ rX rT2 (by decide) (by decide) (by decide) z σ hZ hT2 (by rw [hX]; omega)
    (by omega)
  set σ1 := σ.setv rX (σ.val rX + z) with hσ1
  have h2 := shiftLoop_exec cap i σ1 z (by simp [σ1, hRV]) (by simp [σ1, hX]) (by simp [σ1, hY]) (by simp [σ1, hBB])
    (by omega) (by omega) (by omega)
  set σ2 := (σ1.setv rRV 0).setv rX (z / 2 ^ i) with hσ2
  have hzi : z / 2 ^ i ≤ z := Nat.div_le_self _ _
  have h3 := halve_exec (cap := cap) rX rY rBB (by decide) (by decide) (by decide) (z / 2 ^ i) σ2 (by simp [σ2])
    (by simp [σ2, σ1, hBB]) (by simp [σ2, σ1, hY]; omega) (by omega) (by omega)
  set σ3 := ((σ2.setv rX 0).setv rY (σ2.val rY + z / 2 ^ i / 2)).setv rBB (z / 2 ^ i % 2) with hσ3
  have hm : z / 2 ^ i % 2 ≤ 1 := by omega
  have h4 := WXExec.wm (wmove_spec (cap := cap) rBB rIMG2 (by decide) (z / 2 ^ i % 2) σ3 (by simp [σ3])
    (by simp [σ3]; omega) (by simp [σ3, σ2, σ1, hI]; omega))
  set σ4 := (σ3.setv rBB 0).setv rIMG2 (σ3.val rIMG2 + σ3.val rBB) with hσ4
  have h5 := clearReg_exec (cap := cap) rY (z / 2 ^ i / 2) σ4 (by simp [σ4, σ3, σ2, σ1, hY]) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 h5)))) ?_ le_rfl) ?_
  · have htb : (z.testBit i).toNat = z / 2 ^ i % 2 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have := Nat.mod_two_eq_zero_or_one (z / 2 ^ i)
      rcases this with h | h <;> simp [h]
    rw [htb]
    apply WState.eq <;> try rfl
    funext r; revert r; apply fin40_cases; intro j hj
    interval_cases j <;> simp [σ4, σ3, σ2, σ1, hX, hY, hBB, hI]
  · have h6 : z / 2 ^ i / 2 ≤ z := le_trans (Nat.div_le_self _ _) hzi
    omega

/-! ## The fields of a plain node -/

/-- The translated fields from the word fields `(t, f1, f2)` at seed `z` (base `bz`, block size `k`). -/
def outFields (t f1 f2 z bz k : ℕ) : Fin 3 → ℕ :=
  if t = 0 then ![0, f1, 0]
  else if t = 1 then ![0, (z.testBit f1).toNat, 0]
  else if t = 2 then ![2, bz + f1 * k + k - 1, 0]
  else ![t, bz + f1 * k + k - 1, bz + f2 * k + k - 1]

/-- The cost bound of `plainFields`. -/
def fieldsCost (f1 f2 k bz z : ℕ) : ℕ :=
  imgCost f1 k bz + imgCost f2 k bz + imgCost f1 1 0 + f1 * (13 * z + 40) + 40 * z + 18 * (bz + f1 * k + k) + 1000

theorem readCost_le (x k bz : ℕ) :
    (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ imgCost x k bz := by
  unfold imgCost; omega

theorem nbl_zero : natBitLength 0 = 1 := rfl

theorem readCost_zero : (natBitLength 0 + 2) * (40 * 2 ^ natBitLength 0 + 40) = 360 := rfl

theorem pow_nbl_zero : 2 ^ (natBitLength 0 + 1) = 4 := rfl

/-- The tag-0 branch: `IMG2 := f1`, skip `f2 = 0`. -/
def low0 (ε : Bool) : WMX 3 40 :=
  .seq (.wm (readNatM ε sCW rRF rRC rIMG2 rRP rRT)) (.wm (readNatM ε sCW rRF rRC rRV rRP rRT))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem low0_exec (ε : Bool) (cap : ℕ) (σ : WState 3 40) (f1 : ℕ) (pre rest : List Bool)
    (hst : σ.st sCW = pre ++ enc ε (natWord f1) ++ (enc ε (natWord 0) ++ rest)) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG2 : σ.val rIMG2 = 0) (hcap : 2 ^ (natBitLength f1 + 1) + 4 ≤ cap) :
    WXExec cap (low0 ε) σ
      ((σ.seth sCW (pre.length + stp ε * (natWord f1).length + stp ε * (natWord 0).length)).setv rIMG2 f1)
      (imgCost f1 1 0 + 400) := by
  have hp1 : 2 ^ (natBitLength f1 + 1) = 2 * 2 ^ natBitLength f1 := by rw [pow_succ]; ring
  have hx1 : f1 < 2 ^ (natBitLength f1) := Nat.lt_pow_succ_log_self (by norm_num) f1
  have r1 := WXExec.wm (readNatM_spec (cap := cap) ε sCW rRF rRC rIMG2 rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) f1 pre _ σ hst hsh hRF hRC hRP
    hRT (by rw [hIMG2]; omega))
  set σ3 := (σ.seth sCW (pre.length + stp ε * (natWord f1).length)).setv rIMG2 (σ.val rIMG2 + f1) with hσ3
  have hpl : (pre ++ enc ε (natWord f1)).length = pre.length + stp ε * (natWord f1).length := by simp [enc_length]
  have r2 := WXExec.wm (readNatM_spec (cap := cap) ε sCW rRF rRC rRV rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (pre ++ enc ε (natWord f1))
    rest σ3 (by simp [σ3, hst]) (by simp [σ3, hpl]) (by simp [σ3, hRF]) (by simp [σ3, hRC]) (by simp [σ3, hRP])
    (by simp [σ3, hRT]) (by simp only [σ3, WState.setv_val, WState.seth_val, Function.update_apply]; simp [hRV, pow_nbl_zero]; omega))
  refine WXExec.mono (WXExec.cast cap (WXExec.seq r1 r2) ?_ le_rfl) ?_
  · rw [hpl]
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ3]
    · funext i; fin_cases i <;> simp [σ3]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ3, hIMG2]
    · rfl
  · have := readCost_le f1 1 0
    rw [readCost_zero]
    omega

/-- The tag-1 branch: `IMG2 := z_{f1}`, skip `f2 = 0`, `TAG := 0`. -/
def low1 (ε : Bool) : WMX 3 40 :=
  .seq (.wm (readNatM ε sCW rRF rRC rRV rRP rRT)) <| .seq bitStep <|
  .seq (.wm (readNatM ε sCW rRF rRC rRV rRP rRT)) (WMX.dec rTAG)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem low1_exec (ε : Bool) (cap : ℕ) (σ : WState 3 40) (f1 z : ℕ) (pre rest : List Bool)
    (hst : σ.st sCW = pre ++ enc ε (natWord f1) ++ (enc ε (natWord 0) ++ rest)) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG2 : σ.val rIMG2 = 0) (hZ : σ.val rZ = z) (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0)
    (hT2 : σ.val rT2 = 0) (hTAG : σ.val rTAG = 1)
    (hcap : 2 ^ (natBitLength f1 + 1) + 2 * z + f1 + 4 ≤ cap) :
    WXExec cap (low1 ε) σ
      (((σ.seth sCW (pre.length + stp ε * (natWord f1).length + stp ε * (natWord 0).length)).setv rIMG2
        (z.testBit f1).toNat).setv rTAG 0)
      (imgCost f1 1 0 + f1 * (13 * z + 40) + 40 * z + 600) := by
  have hp1 : 2 ^ (natBitLength f1 + 1) = 2 * 2 ^ natBitLength f1 := by rw [pow_succ]; ring
  have hx1 : f1 < 2 ^ (natBitLength f1) := Nat.lt_pow_succ_log_self (by norm_num) f1
  have r1 := WXExec.wm (readNatM_spec (cap := cap) ε sCW rRF rRC rRV rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) f1 pre _ σ hst hsh hRF hRC hRP
    hRT (by rw [hRV]; omega))
  set σ3 := (σ.seth sCW (pre.length + stp ε * (natWord f1).length)).setv rRV (σ.val rRV + f1) with hσ3
  have r2 := bitStep_exec cap σ3 z f1 (by simp [σ3, hRV]) (by simp [σ3, hZ]) (by simp [σ3, hX]) (by simp [σ3, hY])
    (by simp [σ3, hBB]) (by simp [σ3, hT2]) (by simp [σ3, hIMG2]) (by omega)
  set σ4 := (σ3.setv rRV 0).setv rIMG2 (z.testBit f1).toNat with hσ4
  have hpl : (pre ++ enc ε (natWord f1)).length = pre.length + stp ε * (natWord f1).length := by simp [enc_length]
  have r3 := WXExec.wm (readNatM_spec (cap := cap) ε sCW rRF rRC rRV rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (pre ++ enc ε (natWord f1))
    rest σ4 (by simp [σ4, σ3, hst]) (by simp [σ4, σ3, hpl]) (by simp [σ4, σ3, hRF]) (by simp [σ4, σ3, hRC])
    (by simp [σ4, σ3, hRP]) (by simp [σ4, σ3, hRT]) (by simp [σ4, pow_nbl_zero]; omega))
  set σ5 := (σ4.seth sCW ((pre ++ enc ε (natWord f1)).length + stp ε * (natWord 0).length)).setv rRV
    (σ4.val rRV + 0) with hσ5
  have r4 := WXExec.dec cap rTAG σ5 (by simp [σ5, σ4, σ3, hTAG]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq r1 (WXExec.seq r2 (WXExec.seq r3 r4))) ?_ le_rfl) ?_
  · apply WState.eq
    · funext i; fin_cases i <;> simp [σ5, σ4, σ3, hpl]
    · funext i; fin_cases i <;> simp [σ5, σ4, σ3]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ5, σ4, σ3, hRV, hIMG2, hTAG]
    · rfl
  · have := readCost_le f1 1 0
    rw [readCost_zero]
    unfold imgCost at *
    omega

/-- The high branch (tags `2, 3, 4`; `TMP = tag − 1` on entry): `IMG2 := img f1`, then `IMG := img f2` unless
`tag = 2` (then `f2 = 0` is skipped); `TMP` ends at `tag − 2`. -/
def high (ε : Bool) : WMX 3 40 :=
  .seq (imgStep ε) <| .seq (.wm (WM.move rIMG rIMG2)) <| .seq (WMX.dec rTMP) <|
  .ifr rTMP (imgStep ε) (.wm (readNatM ε sCW rRF rRC rRV rRP rRT))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem high_exec (ε : Bool) (cap : ℕ) (σ : WState 3 40) (t f1 f2 k bz : ℕ) (pre rest : List Bool)
    (ht2 : 2 ≤ t) (hf2 : t = 2 → f2 = 0)
    (hst : σ.st sCW = pre ++ enc ε (natWord f1) ++ (enc ε (natWord f2) ++ rest)) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG : σ.val rIMG = 0) (hIMG2 : σ.val rIMG2 = 0) (hT : σ.val rTN = 0) (hBZ : σ.val rBZ = bz)
    (hK : σ.val rKK = k) (hk : 1 ≤ k) (hTMP : σ.val rTMP = t - 1)
    (hcap : 2 ^ (natBitLength f1 + 1) + 2 ^ (natBitLength f2 + 1) + bz + f1 * k + f2 * k + k + t + 20 ≤ cap) :
    WXExec cap (high ε) σ
      (((σ.seth sCW (pre.length + stp ε * (natWord f1).length + stp ε * (natWord f2).length)).setv rIMG2
        (bz + f1 * k + k - 1)).setv rIMG (if t = 2 then 0 else bz + f2 * k + k - 1) |>.setv rTMP (t - 2))
      (imgCost f1 k bz + imgCost f2 k bz + 18 * (bz + f1 * k + k) + 50) := by
  have hrc2 := readCost_le f2 k bz
  have hp1 : 2 ^ (natBitLength f1 + 1) = 2 * 2 ^ natBitLength f1 := by rw [pow_succ]; ring
  have hx1 : f1 < 2 ^ (natBitLength f1) := Nat.lt_pow_succ_log_self (by norm_num) f1
  have hp2 : 2 ^ (natBitLength f2 + 1) = 2 * 2 ^ natBitLength f2 := by rw [pow_succ]; ring
  have hx2 : f2 < 2 ^ (natBitLength f2) := Nat.lt_pow_succ_log_self (by norm_num) f2
  have r1 := imgStep_exec ε cap σ f1 k bz pre _ hst hsh hRF hRC hRV hRP hRT hIMG hT hBZ hK hk (by omega)
  set σ3 := (σ.seth sCW (pre.length + stp ε * (natWord f1).length)).setv rIMG (bz + f1 * k + k - 1) with hσ3
  have r2 := WXExec.wm (wmove_spec (cap := cap) rIMG rIMG2 (by decide) (bz + f1 * k + k - 1) σ3 (by simp [σ3])
    (by simp [σ3]; omega) (by simp [σ3, hIMG2]; omega))
  set σ4 := (σ3.setv rIMG 0).setv rIMG2 (σ3.val rIMG2 + σ3.val rIMG) with hσ4
  have r3 := WXExec.dec cap rTMP σ4 (by simp [σ4, σ3, hTMP]; omega)
  set σ5 := σ4.setv rTMP (σ4.val rTMP - 1) with hσ5
  have hσ5TMP : σ5.val rTMP = t - 2 := by simp [σ5, σ4, σ3, hTMP]; omega
  have hpl : (pre ++ enc ε (natWord f1)).length = pre.length + stp ε * (natWord f1).length := by simp [enc_length]
  have hst5 : σ5.st sCW = (pre ++ enc ε (natWord f1)) ++ enc ε (natWord f2) ++ rest := by
    simp [σ5, σ4, σ3, hst]
  have hsh5 : σ5.sh sCW = (pre ++ enc ε (natWord f1)).length := by simp [σ5, σ4, σ3, hpl]
  by_cases h2t : t = 2
  · have hz2 : f2 = 0 := hf2 h2t
    subst hz2
    have r4 := WXExec.wm (readNatM_spec (cap := cap) ε sCW rRF rRC rRV rRP rRT (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 _ rest σ5 hst5 hsh5
      (by simp [σ5, σ4, σ3, hRF]) (by simp [σ5, σ4, σ3, hRC]) (by simp [σ5, σ4, σ3, hRP]) (by simp [σ5, σ4, σ3, hRT])
      (by simp [σ5, σ4, σ3, hRV, pow_nbl_zero]; omega))
    refine WXExec.mono (WXExec.cast cap (WXExec.seq r1 (WXExec.seq r2 (WXExec.seq r3
      (WXExec.ifrF (P := imgStep ε) (by rw [hσ5TMP, h2t]) r4)))) ?_ le_rfl) ?_
    · rw [hpl, if_pos h2t]
      apply WState.eq
      · funext i; fin_cases i <;> simp [σ5, σ4, σ3]
      · funext i; fin_cases i <;> simp [σ5, σ4, σ3]
      · funext i; revert i; apply fin40_cases; intro i hi
        interval_cases i <;> simp [σ5, σ4, σ3, hIMG2, hIMG, hTMP] <;> omega
      · rfl
    · simp only [readCost_zero] at hrc2 ⊢
      omega
  · have r4 := imgStep_exec ε cap σ5 f2 k bz _ rest hst5 hsh5 (by simp [σ5, σ4, σ3, hRF]) (by simp [σ5, σ4, σ3, hRC])
      (by simp [σ5, σ4, σ3, hRV]) (by simp [σ5, σ4, σ3, hRP]) (by simp [σ5, σ4, σ3, hRT]) (by simp [σ5, σ4])
      (by simp [σ5, σ4, σ3, hT]) (by simp [σ5, σ4, σ3, hBZ]) (by simp [σ5, σ4, σ3, hK]) hk (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.seq r1 (WXExec.seq r2 (WXExec.seq r3
      (WXExec.ifrT (Q := .wm (readNatM ε sCW rRF rRC rRV rRP rRT)) (by rw [hσ5TMP]; omega) r4)))) ?_ le_rfl) ?_
    · rw [hpl, if_neg h2t]
      apply WState.eq
      · funext i; fin_cases i <;> simp [σ5, σ4, σ3]
      · funext i; fin_cases i <;> simp [σ5, σ4, σ3]
      · funext i; revert i; apply fin40_cases; intro i hi
        interval_cases i <;> simp [σ5, σ4, σ3, hIMG2, hIMG, hTMP] <;> omega
      · rfl
    · omega

/-- Read the two number fields of a plain node (tag `TAG` already read) and compute the translated node's fields
`TAG`, `IMG2`, `IMG` (paper §11.6 stage 2: gates keep their kind, children map to their images, an input `i` becomes
the constant `z_i`). -/
def plainFields (ε : Bool) : WMX 3 40 :=
  .seq (copyReg rTAG rTMP rT2) <| .seq (WMX.dec rTMP) <|
  .seq (.ifr rTMP (high ε) (.ifr rTAG (low1 ε) (low0 ε))) (clearReg rTMP)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem plainFields_exec (ε : Bool) (cap : ℕ) (σ : WState 3 40) (t f1 f2 z bz k : ℕ) (pre rest : List Bool)
    (ht : t ≤ 4) (hf2 : t ≤ 2 → f2 = 0)
    (hst : σ.st sCW = pre ++ enc ε (natWord f1 ++ natWord f2) ++ rest) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG : σ.val rIMG = 0) (hIMG2 : σ.val rIMG2 = 0) (hT : σ.val rTN = 0) (hBZ : σ.val rBZ = bz)
    (hK : σ.val rKK = k) (hk : 1 ≤ k) (hZ : σ.val rZ = z) (hTAG : σ.val rTAG = t) (hTMP : σ.val rTMP = 0)
    (hT2 : σ.val rT2 = 0) (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0)
    (hcap : 2 ^ (natBitLength f1 + 1) + 2 ^ (natBitLength f2 + 1) + bz + f1 * k + f2 * k + k + 2 * z + f1 + 24 ≤
      cap) :
    WXExec cap (plainFields ε) σ
      ((((σ.seth sCW (pre.length + stp ε * (natWord f1 ++ natWord f2).length)).setv rTAG
        (outFields t f1 f2 z bz k 0)).setv rIMG2 (outFields t f1 f2 z bz k 1)).setv rIMG (outFields t f1 f2 z bz k 2))
      (fieldsCost f1 f2 k bz z) := by
  have hcw : σ.st sCW = pre ++ enc ε (natWord f1) ++ (enc ε (natWord f2) ++ rest) := by
    rw [hst, enc_append]; simp only [List.append_assoc]
  have hlen : pre.length + stp ε * (natWord f1 ++ natWord f2).length =
      pre.length + stp ε * (natWord f1).length + stp ε * (natWord f2).length := by
    rw [List.length_append, Nat.mul_add, Nat.add_assoc]
  rw [hlen]
  have hrc1 := readCost_le f1 k bz
  have hrc1' := readCost_le f1 1 0
  have hp1 : 2 ^ (natBitLength f1 + 1) = 2 * 2 ^ natBitLength f1 := by rw [pow_succ]; ring
  have hx1 : f1 < 2 ^ (natBitLength f1) := Nat.lt_pow_succ_log_self (by norm_num) f1
  have hp2 : 2 ^ (natBitLength f2 + 1) = 2 * 2 ^ natBitLength f2 := by rw [pow_succ]; ring
  have hx2 : f2 < 2 ^ (natBitLength f2) := Nat.lt_pow_succ_log_self (by norm_num) f2
  -- 1, 2. TMP := t − 1
  have h1 := copyReg_exec (cap := cap) rTAG rTMP rT2 (by decide) (by decide) (by decide) t σ hTAG hT2
    (by rw [hTMP]; omega) (by omega)
  have h2 := WXExec.dec cap (rTMP) (σ.setv rTMP (σ.val rTMP + t)) (by simp [hTMP]; omega)
  set σ2 := (σ.setv rTMP (σ.val rTMP + t)).setv rTMP ((σ.setv rTMP (σ.val rTMP + t)).val rTMP - 1) with hσ2
  have e2 : σ2 = σ.setv rTMP (t - 1) := by simp [σ2, hTMP, wsetv_setv]
  rw [e2] at h2
  by_cases h01 : t ≤ 1
  · have hz2 : f2 = 0 := hf2 (by omega)
    subst hz2
    by_cases h0 : t = 0
    · subst h0
      have hb := low0_exec ε cap (σ.setv rTMP (0 - 1)) f1 pre rest (by simpa using hcw) (by simpa using hsh)
        (by simp [hRF]) (by simp [hRC]) (by simp [hRV]) (by simp [hRP]) (by simp [hRT]) (by simp [hIMG2])
        (by omega)
      have hb' := WXExec.ifrF (r := rTMP) (P := high ε) (by simp)
        (WXExec.ifrF (r := rTAG) (P := low1 ε) (by simp [hTAG]) hb)
      have h4 := clearReg_exec (cap := cap) rTMP 0 ((((σ.setv rTMP (0 - 1)).seth sCW
        (pre.length + stp ε * (natWord f1).length + stp ε * (natWord 0).length)).setv rIMG2 f1)) (by simp) (by omega)
      refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq hb' h4))) ?_ le_rfl) ?_
      · apply WState.eq
        · funext i; fin_cases i <;> simp
        · funext i; fin_cases i <;> simp
        · funext i; revert i; apply fin40_cases; intro i hi
          interval_cases i <;> simp [outFields, hTMP, hTAG, hIMG, hIMG2]
        · rfl
      · unfold fieldsCost imgCost at *; omega
    · have h1' : t = 1 := by omega
      subst h1'
      have hb := low1_exec ε cap (σ.setv rTMP (1 - 1)) f1 z pre rest (by simpa using hcw) (by simpa using hsh)
        (by simp [hRF]) (by simp [hRC]) (by simp [hRV]) (by simp [hRP]) (by simp [hRT]) (by simp [hIMG2])
        (by simp [hZ]) (by simp [hX]) (by simp [hY]) (by simp [hBB]) (by simp [hT2]) (by simp [hTAG]) (by omega)
      have hb' := WXExec.ifrF (r := rTMP) (P := high ε) (by simp)
        (WXExec.ifrT (r := rTAG) (Q := low0 ε) (by simp [hTAG]) hb)
      have h4 := clearReg_exec (cap := cap) rTMP 0 (((((σ.setv rTMP (1 - 1)).seth sCW
        (pre.length + stp ε * (natWord f1).length + stp ε * (natWord 0).length)).setv rIMG2
        (z.testBit f1).toNat).setv rTAG 0)) (by simp) (by omega)
      refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq hb' h4))) ?_ le_rfl) ?_
      · apply WState.eq
        · funext i; fin_cases i <;> simp
        · funext i; fin_cases i <;> simp
        · funext i; revert i; apply fin40_cases; intro i hi
          interval_cases i <;> simp [outFields, hTMP, hTAG, hIMG, hIMG2]
        · rfl
      · unfold fieldsCost imgCost at *; omega
  · have hb := high_exec ε cap (σ.setv rTMP (t - 1)) t f1 f2 k bz pre rest (by omega) (fun h => hf2 (by omega))
      (by simpa using hcw) (by simpa using hsh) (by simp [hRF]) (by simp [hRC]) (by simp [hRV]) (by simp [hRP])
      (by simp [hRT]) (by simp [hIMG]) (by simp [hIMG2]) (by simp [hT]) (by simp [hBZ]) (by simp [hK]) hk
      (by simp) (by omega)
    have hb' := WXExec.ifrT (r := rTMP) (Q := .ifr rTAG (low1 ε) (low0 ε)) (by simp; omega) hb
    have h4 := clearReg_exec (cap := cap) rTMP (t - 2) ((((σ.setv rTMP (t - 1)).seth sCW
      (pre.length + stp ε * (natWord f1).length + stp ε * (natWord f2).length)).setv rIMG2
      (bz + f1 * k + k - 1)).setv rIMG (if t = 2 then 0 else bz + f2 * k + k - 1) |>.setv rTMP (t - 2)) (by simp)
      (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq hb' h4))) ?_ le_rfl) ?_
    · have h0 : ¬ t = 0 := by omega
      have h1' : ¬ t = 1 := by omega
      apply WState.eq
      · funext i; fin_cases i <;> simp
      · funext i; fin_cases i <;> simp
      · funext i; revert i; apply fin40_cases; intro i hi
        by_cases h2t : t = 2
        · subst h2t; interval_cases i <;> simp [outFields, hTMP, hTAG, hIMG, hIMG2]
        · interval_cases i <;> simp [outFields, hTMP, hTAG, hIMG, hIMG2, h0, h1', h2t]
      · rfl
    · unfold fieldsCost; omega

end NearCubicGates.Close.ENP.TEmit
