import Proof.Gates.ENP.TablePair

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
local notation "rL" => (9 : Fin 40)
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
local notation "rLC1" => (33 : Fin 40)
local notation "rT2" => (38 : Fin 40)
local notation "rTMP" => (39 : Fin 40)

/-! ## The argument stream -/

/-- The argument images in unary, each followed by a `false`. -/
def argsStream (ws : List ℕ) : List Bool := ws.flatMap (fun w => List.replicate w true ++ [false])

/-- The head position before argument `k`. -/
def argPos (ws : List ℕ) (k : ℕ) : ℕ := ((ws.take k).map (· + 1)).sum

theorem argsStream_split (ws : List ℕ) (k : ℕ) :
    argsStream ws = argsStream (ws.take k) ++ argsStream (ws.drop k) := by
  unfold argsStream
  conv_lhs => rw [← List.take_append_drop k ws]
  rw [List.flatMap_append]

theorem argsStream_length (ws : List ℕ) : (argsStream ws).length = (ws.map (· + 1)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [argsStream, List.flatMap_cons, List.length_append, List.length_replicate, List.length_singleton,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem argPos_succ (ws : List ℕ) (k : ℕ) (hk : k < ws.length) :
    argPos ws (k + 1) = argPos ws k + (ws[k] + 1) := by
  unfold argPos
  rw [List.take_add_one, List.map_append, List.sum_append]
  simp [List.getElem?_eq_getElem hk]

theorem argPos_mono (ws : List ℕ) (k : ℕ) : ∀ d, k + d ≤ ws.length → argPos ws k ≤ argPos ws (k + d) := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro h
    rw [← Nat.add_assoc, argPos_succ ws (k + d) (by omega)]
    have := ih (by omega)
    omega

theorem args_read (ws : List ℕ) (k : ℕ) (hk : k < ws.length) :
    (∀ i < ws[k], readTapeBit (argsStream ws) (argPos ws k + i) = true) ∧
      readTapeBit (argsStream ws) (argPos ws k + ws[k]) = false := by
  have hsplit := argsStream_split ws k
  have hlen : (argsStream (ws.take k)).length = argPos ws k := by rw [argsStream_length]; rfl
  have hdrop : ws.drop k = ws[k] :: ws.drop (k + 1) := List.drop_eq_getElem_cons hk
  have hrest : argsStream (ws.drop k) = List.replicate ws[k] true ++ [false] ++ argsStream (ws.drop (k + 1)) := by
    unfold argsStream
    rw [hdrop, List.flatMap_cons]
  rw [hsplit, hrest]
  constructor
  · intro i hi
    unfold readTapeBit
    rw [← hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hi, List.getElem?_append_left, List.getElem?_replicate]
  · unfold readTapeBit
    rw [← hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp

/-- Reading inside a prefix is unaffected by what follows. -/
theorem read_append_lt (p junk : List Bool) (i : ℕ) (h : i < p.length) :
    readTapeBit (p ++ junk) i = readTapeBit p i := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem argPos_lt (ws : List ℕ) (k : ℕ) (hk : k < ws.length) : argPos ws k + ws[k] < (argsStream ws).length := by
  have hsplit := argsStream_split ws (k + 1)
  have h1 : (argsStream (ws.take (k + 1))).length = argPos ws (k + 1) := by rw [argsStream_length]; rfl
  have := argPos_succ ws k hk
  rw [hsplit, List.length_append, h1]
  omega

/-! ## The pairs loop -/

/-- The bytes of the first `k` pairs of group `a` (start `gs`, argument images `ws`). -/
def pairsBytes {ℓ : ℕ} (a gs : ℕ) (ws : List ℕ) (k : ℕ) : List Bool :=
  (List.range k).flatMap (fun j =>
    PCPPRequestNodeSchema.native (TCirc.lit (ℓ := ℓ) (a.testBit j) (ws.getD j 0)) ++
    PCPPRequestNodeSchema.native (.and (if j = 0 then 1 + a else gs + 2 * j - 1) (gs + 2 * j) : BooleanNode (TCirc.T ℓ)))

/-- The state before pair `k`. -/
def pst {ℓ : ℕ} (σ : WState 3 40) (a gs : ℕ) (ws : List ℕ) (k : ℕ) : WState 3 40 :=
  appendO (((((σ.setv rX (a / 2 ^ k)).setv rNP (gs + 2 * k)).setv rJJ k).seth sARGS (argPos ws k)).setv
    rCA (argPos ws k)) sG rR7 (marks (pairsBytes (ℓ := ℓ) a gs ws k))

theorem nodeCost_mono {V V' : ℕ} (h : V ≤ V') : nodeCost V ≤ nodeCost V' := by
  unfold nodeCost
  have := fieldCost_mono (k := 3) (k' := 3) h le_rfl
  omega

theorem pairCost_mono {u w V u' w' V' : ℕ} (hu : u ≤ u') (hw : w ≤ w') (hV : V ≤ V') :
    pairCost u w V ≤ pairCost u' w' V' := by
  unfold pairCost
  have := nodeCost_mono hV
  omega

theorem pairsBytes_length_le {ℓ : ℕ} (a gs Vb : ℕ) (ws : List ℕ) (k : ℕ)
    (hV : ∀ j < k, ws.getD j 0 + 4 ≤ Vb ∧ gs + 2 * j ≤ Vb ∧ 1 + a ≤ Vb) :
    (pairsBytes (ℓ := ℓ) a gs ws k).length ≤ k * (12 * Vb + 18) := by
  induction k with
  | zero => simp [pairsBytes]
  | succ k ih =>
    have hpb : pairsBytes (ℓ := ℓ) a gs ws (k + 1) = pairsBytes (ℓ := ℓ) a gs ws k ++
        (PCPPRequestNodeSchema.native (TCirc.lit (ℓ := ℓ) (a.testBit k) (ws.getD k 0)) ++
          PCPPRequestNodeSchema.native (.and (if k = 0 then 1 + a else gs + 2 * k - 1) (gs + 2 * k) :
            BooleanNode (TCirc.T ℓ))) := by
      simp [pairsBytes, List.range_succ, List.flatMap_append]
    rw [hpb, List.length_append, List.length_append]
    have h1 := ih (fun j hj => hV j (by omega))
    obtain ⟨hw, hg, ha⟩ := hV k (by omega)
    have hw' : ws[k]?.getD 0 + 4 ≤ Vb := by simpa [List.getD_eq_getElem?_getD] using hw
    have h2 := native_len_le (TCirc.lit (ℓ := ℓ) (a.testBit k) (ws.getD k 0)) Vb (by
      intro i; unfold TCirc.lit; split <;> fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
    have h3 := native_len_le (.and (if k = 0 then 1 + a else gs + 2 * k - 1) (gs + 2 * k) :
      BooleanNode (TCirc.T ℓ)) Vb (by
      intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> (try split) <;> omega)
    have hm : (k + 1) * (12 * Vb + 18) = k * (12 * Vb + 18) + (12 * Vb + 18) := by ring
    rw [hm]
    omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The `ℓ` pairs of a group** (`sec:all-lengths` stage 2). -/
theorem pairsLoop_exec {ℓ : ℕ} (cap : ℕ) (σ : WState 3 40) (a gs Wm : ℕ) (ws : List ℕ) (hws : ws.length = ℓ)
    (hWm : ∀ w ∈ ws, w ≤ Wm) (hgs : 1 ≤ gs)
    (hY : σ.val rY = 0) (hBB : σ.val rBB = 0) (hW : σ.val rW = 0) (hF1 : σ.val rF1 = 0)
    (hF2 : σ.val rF2 = 0) (hA : σ.val rA = a) (hL : σ.val rL = ℓ) (hLC1 : σ.val rLC1 = 0)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hT : σ.val rTN = 0) (hG : σ.sh sG = (σ.st sG).length)
    (junk : List Bool) (hARGS : σ.st sARGS = argsStream ws ++ junk)
    (hcap : a + Wm + gs + 2 * ℓ + ℓ + argPos ws ℓ + σ.val rR7 + 14 * ℓ * (6 * (gs + 2 * ℓ + Wm + a + 4) + 9) +
      300 * (gs + 2 * ℓ + Wm + a + 10) ≤ cap) :
    WXExec cap (repK rL rLC1 pairBody) (pst (ℓ := ℓ) σ a gs ws 0) (pst (ℓ := ℓ) σ a gs ws ℓ)
      (ℓ * (pairCost a Wm (gs + 2 * ℓ + Wm + a + 4) + 8) + 7 * ℓ + 3) := by
  have hpb : ∀ k, pairsBytes (ℓ := ℓ) a gs ws (k + 1) = pairsBytes (ℓ := ℓ) a gs ws k ++
      (PCPPRequestNodeSchema.native (TCirc.lit (ℓ := ℓ) (a.testBit k) (ws.getD k 0)) ++
        PCPPRequestNodeSchema.native (.and (if k = 0 then 1 + a else gs + 2 * k - 1) (gs + 2 * k) :
          BooleanNode (TCirc.T ℓ))) := by
    intro k; simp [pairsBytes, List.range_succ, List.flatMap_append]
  refine Runs.repE (cap := cap) (by decide) _ ℓ (pst (ℓ := ℓ) σ a gs ws) (by omega)
    (by intro k; simp [pst]) (by intro k; simp [pst]) ?_ (by simp [pst, hL]) (by simp [pst, hLC1])
  intro k hk v1 v2
  have hkl : k < ws.length := by omega
  obtain ⟨hones0, hend0⟩ := args_read ws k hkl
  have hlt := argPos_lt ws k hkl
  have hones : ∀ i < ws[k], readTapeBit (argsStream ws ++ junk) (argPos ws k + i) = true := fun i hi => by
    rw [read_append_lt _ _ _ (by omega)]; exact hones0 i hi
  have hend : readTapeBit (argsStream ws ++ junk) (argPos ws k + ws[k]) = false := by
    rw [read_append_lt _ _ _ hlt]; exact hend0
  have hwk : ws[k] ≤ Wm := hWm _ (List.getElem_mem hkl)
  have hposk : argPos ws k ≤ argPos ws ℓ := by
    have := argPos_mono ws k (ℓ - k) (by omega); rwa [show k + (ℓ - k) = ℓ by omega] at this
  have hposk1 : argPos ws (k + 1) ≤ argPos ws ℓ := by
    have := argPos_mono ws (k + 1) (ℓ - (k + 1)) (by omega); rwa [show k + 1 + (ℓ - (k + 1)) = ℓ by omega] at this
  have hpe := pairBody_exec (ℓ := ℓ) cap (((pst (ℓ := ℓ) σ a gs ws k).setv rL v1).setv rLC1 v2) (a / 2 ^ k) ws[k] k
    (gs + 2 * k) a (by simp [pst]) (by simp [pst, hY]) (by simp [pst, hBB]) (by simp [pst, hW])
    (by simp [pst, hF1]) (by simp [pst, hF2]) (by simp [pst]) (by simp [pst]) (by simp [pst, hA])
    (fun _ => by omega)
    (fun r hr => by
      have := hwr r hr
      have hr7 : r ≠ rR7 := by intro h; subst h; simp at hr
      simp only [pst, WState.setv_val, WState.seth_val, appendO_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all)
    (by simp [pst, hT]) (by simp [pst, hG])
    (by simpa [pst, hARGS] using hones) (by simpa [pst, hARGS] using hend)
    (by
      have hR7 : (((pst (ℓ := ℓ) σ a gs ws k).setv rL v1).setv rLC1 v2).val rR7 =
          σ.val rR7 + (marks (pairsBytes (ℓ := ℓ) a gs ws k)).length := by simp [pst]
      have hbl := pairsBytes_length_le (ℓ := ℓ) a gs (gs + 2 * ℓ + Wm + a + 4) ws k (fun j hj => by
        have : ws.getD j 0 ≤ Wm := by
          rw [List.getD_eq_getElem?_getD]
          by_cases hjl : j < ws.length
          · rw [List.getElem?_eq_getElem hjl]; exact hWm _ (List.getElem_mem hjl)
          · rw [List.getElem?_eq_none (by omega)]; simp
        omega)
      have hkm : k * (12 * (gs + 2 * ℓ + Wm + a + 4) + 18) ≤ ℓ * (12 * (gs + 2 * ℓ + Wm + a + 4) + 18) :=
        Nat.mul_le_mul_right _ hk.le
      have hbytes : 2 * (pairsBytes (ℓ := ℓ) a gs ws k).length ≤ 14 * ℓ * (6 * (gs + 2 * ℓ + Wm + a + 4) + 9) := by
        have : 14 * ℓ * (6 * (gs + 2 * ℓ + Wm + a + 4) + 9) = 7 * (ℓ * (12 * (gs + 2 * ℓ + Wm + a + 4) + 18)) := by
          ring
        omega
      have hd : a / 2 ^ k ≤ a := Nat.div_le_self _ _
      simp only [pst, WState.setv_val, appendO_val, Function.update_apply] at hR7 ⊢
      simp at hR7 ⊢
      omega)
  have htb : decide (a / 2 ^ k % 2 = 1) = a.testBit k := Nat.testBit_eq_decide_div_mod_eq.symm
  rw [htb] at hpe
  refine WXExec.mono (WXExec.cast cap hpe ?_ le_rfl) ?_
  · have hdiv : a / 2 ^ k / 2 = a / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    have hgd : ws.getD k 0 = ws[k] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl]
    have hps := argPos_succ ws k hkl
    have hpbk := hpb k
    rw [hgd] at hpbk
    have hlen : (pairsBytes (ℓ := ℓ) a gs ws (k + 1)).length = (pairsBytes (ℓ := ℓ) a gs ws k).length +
        ((PCPPRequestNodeSchema.native (TCirc.lit (ℓ := ℓ) (a.testBit k) ws[k])).length +
          (PCPPRequestNodeSchema.native (.and (if k = 0 then 1 + a else gs + 2 * k - 1) (gs + 2 * k) :
            BooleanNode (TCirc.T ℓ))).length) := by
      rw [hpbk, List.length_append, List.length_append]
    apply WState.eq
    · funext i; fin_cases i <;> simp [pst, hps, hlen] <;> omega
    · funext i; fin_cases i <;> simp [pst, hpbk, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [pst, hdiv, hps, hlen] <;> omega
    · rfl
  · exact pairCost_mono (Nat.div_le_self _ _) hwk (by omega)

/-! ## The group -/

def sub2L : WMX 3 40 :=
  .seq (copyReg rL rTMP rT2) (.seq (.whr rTMP (.seq (WMX.dec rTMP) (.seq (WMX.dec rF1) (WMX.dec rF1))))
    (WMX.dec rF1))

theorem sub2Loop_exec (cap : ℕ) : ∀ (n : ℕ) (σ : WState 3 40) (f : ℕ), σ.val rTMP = n → σ.val rF1 = f →
    2 * n ≤ f → f ≤ cap → n ≤ cap →
    WXExec cap (.whr rTMP (.seq (WMX.dec rTMP) (.seq (WMX.dec rF1) (WMX.dec rF1)))) σ
      ((σ.setv rTMP 0).setv rF1 (f - 2 * n)) (7 * n + 1)
  | 0, σ, f, hn, hf, _, _, _ => by
    have e : (σ.setv rTMP 0).setv rF1 (f - 2 * 0) = σ := by
      rw [Nat.mul_zero, Nat.sub_zero, ← hf, ← hn, wsetv_same, wsetv_same]
    rw [e]
    exact WXExec.mono (WXExec.whrF hn) (by omega)
  | n + 1, σ, f, hn, hf, h2, hc, hnc => by
    have h1 := WXExec.dec cap rTMP σ (by omega)
    have h2' := WXExec.dec cap rF1 (σ.setv rTMP (σ.val rTMP - 1)) (by simp [hf]; omega)
    have h3 := WXExec.dec cap rF1 ((σ.setv rTMP (σ.val rTMP - 1)).setv rF1
      ((σ.setv rTMP (σ.val rTMP - 1)).val rF1 - 1)) (by simp [hf]; omega)
    have ih := sub2Loop_exec cap n (((σ.setv rTMP (σ.val rTMP - 1)).setv rF1
      ((σ.setv rTMP (σ.val rTMP - 1)).val rF1 - 1)).setv rF1 ((((σ.setv rTMP (σ.val rTMP - 1)).setv rF1
      ((σ.setv rTMP (σ.val rTMP - 1)).val rF1 - 1))).val rF1 - 1)) (f - 2) (by simp [hn]) (by simp [hf]; omega)
      (by omega) (by omega) (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 (WXExec.seq h2' h3)) ih) ?_ le_rfl)
      (by omega)
    apply WState.eq <;> try rfl
    funext r
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all <;> omega

def tOr : NodeT 40 := ![([], 4), ([rF1], 0), ([rF2], 0)]

/-- **Group `a` of a multiplexer** (`sec:all-lengths` stage 2). -/
def groupBody : WMX 3 40 :=
  .seq (copyReg rA rX rTMP) <|
  .seq (repK rL rLC1 pairBody) <|
  .seq (.ifr rA (.seq (.wm (setR rF1 rTN [rNP] 0)) sub2L) WMX.skip) <|
  .seq (.ifr rL (.seq (.wm (setR rF2 rTN [rNP] 0)) (WMX.dec rF2)) (.wm (setR rF2 rTN [rA] 1))) <|
  .seq (.wm (nodeW sG Rw rTN tOr)) <|
  .seq (WMX.inc rNP) <|
  .seq (clearReg rF1) <| .seq (clearReg rF2) <| .seq (clearReg rX) <| .seq (clearReg rJJ) <|
  .seq (.wm (WM.rewind sARGS rCA)) (WMX.inc rA)

/-- The bytes of group `a` (start `gs`, argument images `ws`). -/
def groupBytes {ℓ : ℕ} (a gs : ℕ) (ws : List ℕ) : List Bool :=
  pairsBytes (ℓ := ℓ) a gs ws ℓ ++ PCPPRequestNodeSchema.native
    (.or (if a = 0 then 0 else gs - 1) (if ℓ = 0 then 1 + a else gs + 2 * ℓ - 1) : BooleanNode (TCirc.T ℓ))

/-- The cost bound of one group. -/
def groupCost (ℓ a gs Wm P : ℕ) : ℕ :=
  ℓ * (pairCost a Wm (gs + 2 * ℓ + Wm + a + 4) + 8) + 7 * ℓ + 3 + nodeCost (gs + 2 * ℓ + Wm + a + 4) +
    200 * (gs + 2 * ℓ + Wm + a + 14) + 5 * P

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **One multiplexer group** (`sec:all-lengths` stage 2): writes `TCirc.group`'s nodes for group `a`. -/
theorem groupBody_exec {ℓ : ℕ} (cap : ℕ) (σ : WState 3 40) (a gs Wm : ℕ) (ws : List ℕ) (hws : ws.length = ℓ)
    (hWm : ∀ w ∈ ws, w ≤ Wm) (hgs : 1 ≤ gs)
    (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0) (hW : σ.val rW = 0) (hF1 : σ.val rF1 = 0)
    (hF2 : σ.val rF2 = 0) (hJ : σ.val rJJ = 0) (hNP : σ.val rNP = gs) (hA : σ.val rA = a) (hL : σ.val rL = ℓ)
    (hLC1 : σ.val rLC1 = 0) (hTMP : σ.val rTMP = 0) (hT2 : σ.val rT2 = 0)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hT : σ.val rTN = 0) (hG : σ.sh sG = (σ.st sG).length)
    (junk : List Bool) (hARGS : σ.st sARGS = argsStream ws ++ junk) (hAh : σ.sh sARGS = 0) (hCA : σ.val rCA = 0)
    (hcap : a + Wm + gs + 2 * ℓ + ℓ + argPos ws ℓ + σ.val rR7 + 14 * ℓ * (6 * (gs + 2 * ℓ + Wm + a + 4) + 9) +
      300 * (gs + 2 * ℓ + Wm + a + 10) ≤ cap) :
    WXExec cap groupBody σ (appendO ((σ.setv rA (a + 1)).setv rNP (gs + 2 * ℓ + 1)) sG rR7
      (marks (groupBytes (ℓ := ℓ) a gs ws))) (groupCost ℓ a gs Wm (argPos ws ℓ)) := by
  set V := gs + 2 * ℓ + Wm + a + 4 with hV
  -- 1. X := a
  have h1 := copyReg_exec (cap := cap) rA rX rTMP (by decide) (by decide) (by decide) a σ hA hTMP
    (by rw [hX]; omega) (by omega)
  rw [hX, Nat.zero_add] at h1
  have hst0 : pst (ℓ := ℓ) σ a gs ws 0 = σ.setv rX a := by
    have hp0 : argPos ws 0 = 0 := rfl
    have hb0 : pairsBytes (ℓ := ℓ) a gs ws 0 = [] := rfl
    apply WState.eq
    · funext i; fin_cases i <;> simp [pst, hp0, hb0, hAh]
    · funext i; fin_cases i <;> simp [pst, hp0, hb0, marks]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [pst, hp0, hb0, hNP, hJ, hCA]
    · rfl
  rw [← hst0] at h1
  -- 2. the pairs
  have h2 := pairsLoop_exec (ℓ := ℓ) cap σ a gs Wm ws hws hWm hgs hY hBB hW hF1 hF2 hA hL hLC1 hwr hT hG junk hARGS
    hcap
  set τ := pst (ℓ := ℓ) σ a gs ws ℓ with hτ
  have hτNP : τ.val rNP = gs + 2 * ℓ := by simp [τ, pst]
  have hτA : τ.val rA = a := by simp [τ, pst, hA]
  have hτL : τ.val rL = ℓ := by simp [τ, pst, hL]
  have hτTN : τ.val rTN = 0 := by simp [τ, pst, hT]
  have hτF1 : τ.val rF1 = 0 := by simp [τ, pst, hF1]
  have hτF2 : τ.val rF2 = 0 := by simp [τ, pst, hF2]
  have hτTMP : τ.val rTMP = 0 := by simp [τ, pst, hTMP]
  have hτT2 : τ.val rT2 = 0 := by simp [τ, pst, hT2]

  set op := (if a = 0 then 0 else gs - 1) with hop
  have h3 : WXExec cap (.ifr rA (.seq (.wm (setR rF1 rTN [rNP] 0)) sub2L) WMX.skip) τ (τ.setv rF1 op)
      (40 * (gs + 2 * ℓ + 10) + 18 * ℓ) := by
    by_cases ha0 : a = 0
    · have := WXExec.ifrF (P := .seq (.wm (setR rF1 rTN [rNP] 0)) sub2L) (by rw [hτA, ha0]) (WXExec.skip cap τ)
      refine WXExec.mono (WXExec.cast cap this ?_ le_rfl) (by omega)
      rw [hop, if_pos ha0, ← hτF1, wsetv_same]
    · have hs := WXExec.wm (setR_spec cap (D := rF1) (T := rTN) (by decide) [rNP] 0 τ (by simp) hτTN
        (by rw [hτF1]; omega) (by simp [regSum, hτNP]; omega))
      set τ1 := τ.setv rF1 (regSum τ [rNP] + 0) with hτ1
      have hc := copyReg_exec (cap := cap) rL rTMP rT2 (by decide) (by decide) (by decide) ℓ τ1
        (by simp [τ1, hτL]) (by simp [τ1, hτT2]) (by simp [τ1, hτTMP]; omega) (by omega)
      set τ2 := τ1.setv rTMP (τ1.val rTMP + ℓ) with hτ2
      have hl := sub2Loop_exec cap ℓ τ2 (gs + 2 * ℓ) (by simp [τ2, τ1, hτTMP]) (by simp [τ2, τ1, regSum, hτNP])
        (by omega) (by omega) (by omega)
      have hd := WXExec.dec cap rF1 ((τ2.setv rTMP 0).setv rF1 (gs + 2 * ℓ - 2 * ℓ)) (by simp; omega)
      refine WXExec.mono (WXExec.ifrT (by rw [hτA]; exact ha0) (WXExec.cast cap (WXExec.seq hs (WXExec.seq hc
        (WXExec.seq hl hd))) ?_ le_rfl)) ?_
      · apply WState.eq <;> try rfl
        funext r
        simp only [τ2, τ1, WState.setv_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [hop] <;> omega
      · simp [regSum, hτNP, hτF1]
        omega
  set τ3 := τ.setv rF1 op with hτ3

  set gi := (if ℓ = 0 then 1 + a else gs + 2 * ℓ - 1) with hgi
  have hτ3F2 : τ3.val rF2 = 0 := by simp [τ3, hτF2]
  have hτ3TN : τ3.val rTN = 0 := by simp [τ3, hτTN]
  have h4 : WXExec cap (.ifr rL (.seq (.wm (setR rF2 rTN [rNP] 0)) (WMX.dec rF2)) (.wm (setR rF2 rTN [rA] 1))) τ3
      (τ3.setv rF2 gi) (30 * (gs + 2 * ℓ + a + 10)) := by
    by_cases hl0 : ℓ = 0
    · have hs := setR_spec cap (D := rF2) (T := rTN) (by decide) [rA] 1 τ3 (by simp) hτ3TN (by rw [hτ3F2]; omega)
        (by simp [regSum, τ3, hτA]; omega)
      refine WXExec.mono (WXExec.ifrF (by simp [τ3, hτL, hl0]) (WXExec.wm (WExec.cast cap hs ?_ le_rfl))) ?_
      · simp [regSum, τ3, hτA, hgi, hl0]; ring_nf
      · simp [regSum, τ3, hτA, hτ3F2]; omega
    · have hs := setR_spec cap (D := rF2) (T := rTN) (by decide) [rNP] 0 τ3 (by simp) hτ3TN (by rw [hτ3F2]; omega)
        (by simp [regSum, τ3, hτNP]; omega)
      have hd := WXExec.dec cap rF2 (τ3.setv rF2 (regSum τ3 [rNP] + 0)) (by simp [regSum, τ3, hτNP]; omega)
      refine WXExec.mono (WXExec.ifrT (by simp [τ3, hτL, hl0]) (WXExec.cast cap (WXExec.seq (WXExec.wm hs) hd) ?_
        le_rfl)) ?_
      · simp [regSum, τ3, hτNP, hgi, hl0, wsetv_setv]
      · simp [regSum, τ3, hτNP, hτ3F2]; omega
  set τ4 := τ3.setv rF2 gi with hτ4
  -- 5. the disjunction node
  have hopV : op ≤ V := by rw [hop]; split <;> omega
  have hgiV : gi ≤ V := by rw [hgi]; split <;> omega
  have hτ4cl : Clean Rw rTN τ4 := clean_of τ4 (fun r hr => by
    have := hwr r hr
    simp only [τ4, τ3, τ, pst, WState.setv_val, WState.seth_val, appendO_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all) (by simp [τ4, τ3, hτTN])
  have hτ4G : τ4.sh sG = (τ4.st sG).length := by simp [τ4, τ3, τ, pst, hG]
  have hpbl := pairsBytes_length_le (ℓ := ℓ) a gs V ws ℓ (fun j hj => by
    have : ws.getD j 0 ≤ Wm := by
      rw [List.getD_eq_getElem?_getD]
      by_cases hjl : j < ws.length
      · rw [List.getElem?_eq_getElem hjl]; exact hWm _ (List.getElem_mem hjl)
      · rw [List.getElem?_eq_none (by omega)]; simp
    omega)
  have hτR7 : τ4.val rR7 = σ.val rR7 + 2 * (pairsBytes (ℓ := ℓ) a gs ws ℓ).length := by
    simp [τ4, τ3, τ, pst]
  have hmul : 2 * (ℓ * (12 * V + 18)) = 14 * ℓ * (6 * V + 9) - 5 * (ℓ * (12 * V + 18)) := by
    have : 14 * ℓ * (6 * V + 9) = 7 * (ℓ * (12 * V + 18)) := by ring
    omega
  have hn5 := nodeW_spec cap sG Rw rTN hTR tOr (by intro i; fin_cases i <;> simp [tOr, FieldOK] <;> decide)
    (.or op gi : BooleanNode (TCirc.T ℓ)) τ4
    (by intro i; fin_cases i <;> simp [fieldVal, regSum, tOr, PCPPRequestNodeSchema.fields, τ4, τ3])
    (by intro i; fin_cases i <;> simp [tOr]) V
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega) hτ4cl hτ4G
    (by
      have := native_len_le (.or op gi : BooleanNode (TCirc.T ℓ)) V
        (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
      rw [Rw7, hτR7]
      have : 14 * ℓ * (6 * V + 9) = 7 * (ℓ * (12 * V + 18)) := by ring
      omega)
  rw [Rw7] at hn5
  have h5 := WXExec.wm hn5
  set Ob := marks (PCPPRequestNodeSchema.native (.or op gi : BooleanNode (TCirc.T ℓ))) with hOb
  set τ5 := appendO τ4 sG rR7 Ob with hτ5
  -- 6. NP += 1
  have h6 := WXExec.inc cap rNP τ5 (by simp [τ5, τ4, τ3, hτNP]; omega)
  set τ6 := τ5.setv rNP (τ5.val rNP + 1) with hτ6

  have h7 := clearReg_exec (cap := cap) rF1 op τ6 (by simp [τ6, τ5, τ4, τ3]) (by omega)
  set τ7 := τ6.setv rF1 0 with hτ7
  have h8 := clearReg_exec (cap := cap) rF2 gi τ7 (by simp [τ7, τ6, τ5, τ4]) (by omega)
  set τ8 := τ7.setv rF2 0 with hτ8
  have hd : a / 2 ^ ℓ ≤ a := Nat.div_le_self _ _
  have h9 := clearReg_exec (cap := cap) rX (a / 2 ^ ℓ) τ8 (by simp [τ8, τ7, τ6, τ5, τ4, τ3, τ, pst]) (by omega)
  set τ9 := τ8.setv rX 0 with hτ9
  have h10 := clearReg_exec (cap := cap) rJJ ℓ τ9 (by simp [τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ, pst]) (by omega)
  set τ10 := τ9.setv rJJ 0 with hτ10
  -- 11. rewind ARGS
  have h11 := WXExec.wm (wrewind_spec (cap := cap) sARGS rCA (argPos ws ℓ) τ10
    (by simp [τ10, τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ, pst]) (by simp [τ10, τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ, pst]; omega))
  set τ11 := (τ10.setv rCA 0).seth sARGS (τ10.sh sARGS - argPos ws ℓ) with hτ11
  -- 12. A += 1
  have h12 := WXExec.inc cap rA τ11 (by simp [τ11, τ10, τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ, pst, hA]; omega)
  have hfin : τ11.setv rA (τ11.val rA + 1) =
      appendO ((σ.setv rA (a + 1)).setv rNP (gs + 2 * ℓ + 1)) sG rR7 (marks (groupBytes (ℓ := ℓ) a gs ws)) := by
    have hgb : marks (groupBytes (ℓ := ℓ) a gs ws) = marks (pairsBytes (ℓ := ℓ) a gs ws ℓ) ++ Ob := by
      rw [hOb, groupBytes, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
    rw [hgb]
    apply WState.eq
    · funext i; fin_cases i <;> simp [τ11, τ10, τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ, pst, hAh] <;> omega
    · funext i; fin_cases i <;> simp [τ11, τ10, τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ, pst, hARGS]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [τ11, τ10, τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ, pst, hX, hF1, hF2, hJ, hCA, hNP, hA] <;> omega
    · rfl
  rw [hfin] at h12
  refine WXExec.mono (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5 (WXExec.seq h6
    (WXExec.seq h7 (WXExec.seq h8 (WXExec.seq h9 (WXExec.seq h10 (WXExec.seq h11 h12))))))))))) ?_
  unfold groupCost
  have hnc : nodeCost V = nodeCost (gs + 2 * ℓ + Wm + a + 4) := rfl
  omega

/-- `groupBytes` are the native bytes of `TCirc.group` when `ws` lists the argument images. -/
theorem group_bytes {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ) (z c : ℕ) (args : Fin ℓ → ℕ)
    (a : ℕ) (ws : List ℕ) (hws : ∀ j (hj : j < ℓ), ws.getD j 0 = TCirc.img C z (args ⟨j, hj⟩)) :
    (TCirc.group C z c args a).flatMap PCPPRequestNodeSchema.native = groupBytes (ℓ := ℓ) a (TCirc.gs C z c a) ws := by
  unfold TCirc.group groupBytes pairsBytes
  rw [List.flatMap_append, List.flatMap_assoc]
  congr 1
  · apply List.flatMap_congr
    intro j hj
    have hjl : j < ℓ := List.mem_range.mp hj
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, dif_pos hjl, hws j hjl, TCirc.gIdx]
  · simp [TCirc.oPrev, TCirc.gIdx]

end NearCubicGates.Close.ENP.TEmit
