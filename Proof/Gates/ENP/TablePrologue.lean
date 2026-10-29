import Proof.Gates.ENP.TableSeedsRuns

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
open NearCubicWires.Bindings.MW20

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

/-! ## `T = 2^ℓ` and `K = T(2ℓ+1)` -/

def dbl : WMX 3 40 := .seq (copyReg rTT rX rT2) (.wm (WM.move rX rTT))

set_option maxHeartbeats 4000000 in
theorem dbl_exec (cap : ℕ) (σ : WState 3 40) (t : ℕ) (hTT : σ.val rTT = t) (hX : σ.val rX = 0) (hT2 : σ.val rT2 = 0)
    (hcap : 2 * t ≤ cap) :
    WXExec cap dbl σ (σ.setv rTT (2 * t)) (25 * t + 5) := by
  have h1 := copyReg_exec (cap := cap) rTT rX rT2 (by decide) (by decide) (by decide) t σ hTT hT2 (by rw [hX]; omega)
    (by omega)
  have h2 := WXExec.wm (wmove_spec (cap := cap) rX rTT (by decide) t (σ.setv rX (σ.val rX + t)) (by simp [hX])
    (by simp [hX]; omega) (by simp [hTT, hX]; omega))
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 h2) ?_ le_rfl) (by omega)
  apply WState.eq <;> try rfl
  funext r; revert r; apply fin40_cases; intro i hi
  interval_cases i <;> simp [hX, hTT] <;> omega

/-- `KK += 2·TT` (`TN` scratch). -/
def add2 : WMX 3 40 := .seq (.wm (addW rTT rKK rTN)) (.wm (addW rTT rKK rTN))

theorem add2_exec (cap : ℕ) (σ : WState 3 40) (t v : ℕ) (hTT : σ.val rTT = t) (hKK : σ.val rKK = v)
    (hT : σ.val rTN = 0) (hcap : v + 2 * t ≤ cap) :
    WXExec cap add2 σ (σ.setv rKK (v + 2 * t)) (36 * t + 7) := by
  have h1 := addW_spec (cap := cap) (A := rTT) (W := rKK) (T := rTN) (by decide) (by decide) (by decide) σ hT
    (by rw [hTT, hKK]; omega)
  have h2 := addW_spec (cap := cap) (A := rTT) (W := rKK) (T := rTN) (by decide) (by decide) (by decide)
    (σ.setv rKK (σ.val rKK + σ.val rTT)) (by simp [hT]) (by simp [hTT, hKK]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq (WXExec.wm h1) (WXExec.wm h2)) ?_ le_rfl) (by simp [hTT]; omega)
  rw [wsetv_setv]; simp [hTT, hKK]; ring_nf

set_option maxHeartbeats 4000000 in
/-- **`TT := 2^ℓ`** by `ℓ` doublings (`TT = 1` on entry). -/
theorem pow_exec (cap : ℕ) (σ : WState 3 40) (ℓ : ℕ) (hL : σ.val rL = ℓ) (hLC1 : σ.val rLC1 = 0)
    (hTT : σ.val rTT = 1) (hX : σ.val rX = 0) (hT2 : σ.val rT2 = 0) (hcap : 2 * 2 ^ ℓ + 2 * ℓ ≤ cap) :
    WXExec cap (repK rL rLC1 dbl) σ (σ.setv rTT (2 ^ ℓ)) (ℓ * (25 * 2 ^ ℓ + 13) + 7 * ℓ + 3) := by
  have hst := Runs.repE (cap := cap) (K := rL) (K2 := rLC1) (body := dbl) (by decide) (25 * 2 ^ ℓ + 5) ℓ
    (fun k => σ.setv rTT (2 ^ k)) (by omega) (by intro k; simp) (by intro k; simp)
    (by
      intro k hk v1 v2
      have hpk : 2 ^ k ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hk.le
      have hpk1 : 2 ^ (k + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hk
      have h := dbl_exec cap (((σ.setv rTT (2 ^ k)).setv rL v1).setv rLC1 v2) (2 ^ k) (by simp) (by simp [hX])
        (by simp [hT2]) (by rw [pow_succ] at hpk1; omega)
      refine WXExec.mono (WXExec.cast cap h ?_ le_rfl) (by omega)
      apply WState.eq <;> try rfl
      funext r; revert r; apply fin40_cases; intro i hi
      interval_cases i <;> simp [pow_succ] <;> ring)
    (by simp [hL]) (by simp [hLC1])
  have e0 : σ.setv rTT (2 ^ 0) = σ := by rw [pow_zero, ← hTT, wsetv_same]
  rw [e0] at hst
  exact WXExec.mono hst (by ring_nf; omega)

set_option maxHeartbeats 4000000 in
/-- **`KK := T(2ℓ+1)`** (`KK = T` on entry) by `ℓ` additions of `2T`. -/
theorem kk_exec (cap : ℕ) (σ : WState 3 40) (ℓ t : ℕ) (hL : σ.val rL = ℓ) (hLC1 : σ.val rLC1 = 0)
    (hTT : σ.val rTT = t) (hKK : σ.val rKK = t) (hT : σ.val rTN = 0) (hcap : t * (2 * ℓ + 1) + 2 * ℓ ≤ cap) :
    WXExec cap (repK rL rLC1 add2) σ (σ.setv rKK (t * (2 * ℓ + 1))) (ℓ * (36 * t + 15) + 7 * ℓ + 3) := by
  have hst := Runs.repE (cap := cap) (K := rL) (K2 := rLC1) (body := add2) (by decide) (36 * t + 7) ℓ
    (fun k => σ.setv rKK (t + 2 * k * t)) (by omega) (by intro k; simp) (by intro k; simp)
    (by
      intro k hk v1 v2
      have hkt : 2 * (k + 1) * t ≤ 2 * ℓ * t := Nat.mul_le_mul_right _ (by omega)
      have h := add2_exec cap (((σ.setv rKK (t + 2 * k * t)).setv rL v1).setv rLC1 v2) t (t + 2 * k * t)
        (by simp [hTT]) (by simp) (by simp [hT]) (by
          have : t * (2 * ℓ + 1) = 2 * ℓ * t + t := by ring
          have : 2 * (k + 1) * t = 2 * k * t + 2 * t := by ring
          omega)
      refine WXExec.cast cap h ?_ le_rfl
      apply WState.eq <;> try rfl
      funext r; revert r; apply fin40_cases; intro i hi
      interval_cases i <;> simp <;> ring)
    (by simp [hL]) (by simp [hLC1])
  have e0 : σ.setv rKK (t + 2 * 0 * t) = σ := by rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, ← hKK, wsetv_same]
  rw [e0] at hst
  have e1 : t + 2 * ℓ * t = t * (2 * ℓ + 1) := by ring
  rw [e1] at hst
  exact WXExec.mono hst (by ring_nf; omega)

/-! ## The start region -/

/-- The template of input node `A`: `(1, A, 0)`. -/
def tIn : NodeT 40 := ![([], 1), ([rA], 0), ([], 0)]
/-- The template of the constant `true`: `(0, 1, 0)`. -/
def tOne : NodeT 40 := ![([], 0), ([], 1), ([], 0)]

/-- The native bytes of input node `a`. -/
def inW (a : ℕ) : List Bool := natWord 1 ++ natWord a ++ natWord 0

/-- The bytes of the input nodes `0..k−1`. -/
def inB (k : ℕ) : List Bool := (List.range k).flatMap inW

/-- The native bytes of the constant `true`. -/
def ob : List Bool := PCPPRequestNodeSchema.native (BooleanNode.const true : BooleanNode 0)

theorem startBytes_eq (ℓ : ℕ) : startBytes ℓ = zb ++ inB (TCirc.T ℓ) ++ ob := by
  unfold startBytes TCirc.start
  rw [TCirc.ofFn_inputs]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have : (TCirc.inputs (ℓ := ℓ) (TCirc.T ℓ)).flatMap PCPPRequestNodeSchema.native = inB (TCirc.T ℓ) := by
    unfold TCirc.inputs inB
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro a ha
    have ha' : a < TCirc.T ℓ := List.mem_range.mp ha
    simp [ha', inW, PCPPRequestNodeSchema.native, PCPPRequestNodeSchema.fields]
  rw [this]; rfl

/-- One input node: emit `(1, A, 0)`, `A += 1`. -/
def inBody : WMX 3 40 := .seq (.wm (nodeW sG Rw rTN tIn)) (WMX.inc rA)

/-- The state after `k` input nodes. -/
def inSt (σ : WState 3 40) (k : ℕ) : WState 3 40 := appendO (σ.setv rA k) sG rR7 (marks (inB k))

theorem inW_length_le (a V : ℕ) (h : a + 1 ≤ V) : (inW a).length ≤ 6 * V + 9 := by
  have := native_len_le (.input ⟨a, Nat.lt_succ_self a⟩ : BooleanNode (a + 1)) V
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
  simpa [inW, PCPPRequestNodeSchema.native, PCPPRequestNodeSchema.fields] using this

theorem inB_length_le (k V : ℕ) (h : k ≤ V) : (inB k).length ≤ k * (6 * V + 9) := by
  induction k with
  | zero => simp [inB]
  | succ k ih =>
    have e : inB (k + 1) = inB k ++ inW k := by simp [inB, List.range_succ, List.flatMap_append]
    rw [e, List.length_append, Nat.add_mul, Nat.one_mul]
    have := inW_length_le k V (by omega)
    have := ih (by omega)
    omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The `T` input nodes** (`sec:all-lengths` stage 2: one variable per oracle address). -/
theorem inputs_exec (cap : ℕ) (σ : WState 3 40) (t : ℕ) (hTT : σ.val rTT = t) (hA : σ.val rA = 0)
    (hLC3 : σ.val rLC3 = 0) (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hT : σ.val rTN = 0)
    (hG : σ.sh sG = (σ.st sG).length)
    (hcap : σ.val rR7 + 2 * (t * (6 * (t + 1) + 9)) + 40 * (t + 1) + 2 * t + 60 ≤ cap) :
    WXExec cap (repK rTT rLC3 inBody) σ (inSt σ t) (t * (nodeCost (t + 1) + 12) + 7 * t + 3) := by
  have hst := Runs.repE (cap := cap) (K := rTT) (K2 := rLC3) (body := inBody) (by decide) (nodeCost (t + 1) + 4) t
    (inSt σ) (by omega) (by intro k; simp [inSt]) (by intro k; simp [inSt]) ?_ (by simp [inSt, hTT])
    (by simp [inSt, hLC3])
  · have e0 : inSt σ 0 = σ := by
      apply WState.eq
      · funext i; fin_cases i <;> simp [inSt, inB, marks]
      · funext i; fin_cases i <;> simp [inSt, inB, marks]
      · funext i; revert i; apply fin40_cases; intro i hi
        interval_cases i <;> simp [inSt, inB, marks, hA]
      · rfl
    rw [e0] at hst
    exact WXExec.mono hst (by ring_nf; omega)
  intro k hk v1 v2
  set τ := ((inSt σ k).setv rTT v1).setv rLC3 v2 with hτ
  have hcl : Clean Rw rTN τ := clean_of τ (fun r hr => by
    have := hwr r hr
    have h1 : r ≠ rR7 := by intro h; subst h; simp at hr
    have h2 : r ≠ rA := by intro h; subst h; simp at hr
    have h3 : r ≠ rTT := by intro h; subst h; simp at hr
    have h4 : r ≠ rLC3 := by intro h; subst h; simp at hr
    simp [τ, inSt, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, this]) (by simp [τ, inSt, hT])
  have hbl := inB_length_le k (t + 1) (by omega)
  have hkm : k * (6 * (t + 1) + 9) ≤ t * (6 * (t + 1) + 9) := Nat.mul_le_mul_right _ hk.le
  have hn := nodeW_spec cap sG Rw rTN hTR tIn (by intro i; fin_cases i <;> simp [tIn, FieldOK] <;> decide)
    (.input ⟨k, Nat.lt_succ_self k⟩ : BooleanNode (k + 1)) τ
    (by intro i; fin_cases i <;> simp [fieldVal, regSum, tIn, PCPPRequestNodeSchema.fields, τ, inSt])
    (by intro i; fin_cases i <;> simp [tIn]) (t + 1)
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega) hcl
    (by simp [τ, inSt, hG])
    (by
      have := native_len_le (.input ⟨k, Nat.lt_succ_self k⟩ : BooleanNode (k + 1)) (t + 1)
        (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
      rw [Rw7]; simp [τ, inSt, marks_len]; omega)
  rw [Rw7] at hn
  have hi := WXExec.inc cap rA (appendO τ sG rR7 (marks (PCPPRequestNodeSchema.native
    (.input ⟨k, Nat.lt_succ_self k⟩ : BooleanNode (k + 1))))) (by simp [τ, inSt]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq (WXExec.wm hn) hi) ?_ le_rfl) (by omega)
  have hb : inB (k + 1) = inB k ++ PCPPRequestNodeSchema.native (.input ⟨k, Nat.lt_succ_self k⟩ :
      BooleanNode (k + 1)) := by
    simp [inB, List.range_succ, List.flatMap_append, inW, PCPPRequestNodeSchema.native, PCPPRequestNodeSchema.fields]
  apply WState.eq
  · funext i; fin_cases i <;> simp [τ, inSt, hb, marks_len] <;> omega
  · funext i; fin_cases i <;> simp [τ, inSt, hb, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
  · funext i; revert i; apply fin40_cases; intro i hi
    interval_cases i <;> simp [τ, inSt, hb, marks_len] <;> omega
  · rfl

/-! ## The prologue -/

/-- **The prologue** (`sec:all-lengths` stage 2): header, `T`, `K`, the start region, `NP := T + 2`, `SC := T`. -/
def prologue : WMX 3 40 :=
  .seq (.wm (readNatM false sCW rRF rRC rL rRP rRT)) <|
  .seq (.wm (readNatM false sCW rRF rRC rM rRP rRT)) <|
  .seq (WMX.inc rTT) <| .seq (repK rL rLC1 dbl) <|
  .seq (copyReg rTT rKK rT2) <| .seq (repK rL rLC1 add2) <|
  .seq (.wm (nodeW sG Rw rTN tZero)) <| .seq (repK rTT rLC3 inBody) <| .seq (clearReg rA) <|
  .seq (.wm (nodeW sG Rw rTN tOne)) <|
  .seq (copyReg rTT rNP rT2) <| .seq (WMX.inc rNP) <| .seq (WMX.inc rNP) (copyReg rTT rSC rT2)

/-- The prologue's cost bound. -/
def prologueCost (ℓ m : ℕ) : ℕ :=
  (natBitLength ℓ + 2) * (40 * 2 ^ natBitLength ℓ + 40) + (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) +
    (ℓ * (25 * 2 ^ ℓ + 13) + 7 * ℓ + 3) + (ℓ * (36 * 2 ^ ℓ + 15) + 7 * ℓ + 3) +
    (2 ^ ℓ * (nodeCost (2 ^ ℓ + 1) + 12) + 7 * 2 ^ ℓ + 3) + 2 * nodeCost 1 + 100 * 2 ^ ℓ + 100

/-- The prologue's capacity. -/
def prologueCap (ℓ m : ℕ) : ℕ :=
  2 ^ (natBitLength ℓ + 1) + 2 ^ (natBitLength m + 1) + 2 * 2 ^ ℓ + 2 * ℓ + 2 ^ ℓ * (2 * ℓ + 1) +
    2 * (2 ^ ℓ * (6 * (2 ^ ℓ + 1) + 9)) + 40 * (2 ^ ℓ + 1) + 2 * 2 ^ ℓ + 200

theorem zb_len : (marks zb).length = 18 := by rw [marks_len, zb_length]
theorem ob_len : ob.length = 9 := by decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **The prologue runs** from the start state to `preSeeds`. -/
theorem prologue_exec {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) (cap : ℕ)
    (hcap : prologueCap ℓ C.nodes.length ≤ cap) :
    WXExec cap prologue (tStart ((OracleOutput.word ⟨ℓ, C⟩) ++ post)) (preSeeds C post)
      (prologueCost ℓ C.nodes.length) := by
  set W := (OracleOutput.word ⟨ℓ, C⟩) ++ post with hW
  have q1 : 0 < 2 ^ natBitLength ℓ := Nat.two_pow_pos _
  have q2 : 0 < 2 ^ natBitLength C.nodes.length := Nat.two_pow_pos _
  have hl1 : ℓ < 2 ^ natBitLength ℓ := Nat.lt_pow_succ_log_self (by norm_num) ℓ
  have hm1 : C.nodes.length < 2 ^ natBitLength C.nodes.length := Nat.lt_pow_succ_log_self (by norm_num) C.nodes.length
  have hp1 : 2 ^ (natBitLength ℓ + 1) = 2 * 2 ^ natBitLength ℓ := by rw [pow_succ]; ring
  have hp2 : 2 ^ (natBitLength C.nodes.length + 1) = 2 * 2 ^ natBitLength C.nodes.length := by rw [pow_succ]; ring
  have hT : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hc := hcap
  unfold prologueCap at hc
  set σ0 := tStart W with hσ0
  -- 1, 2. L := ℓ, M := C.nodes.length
  have hw0 : σ0.st sCW = [] ++ enc false (natWord ℓ) ++ (natWord C.nodes.length ++ (C.nodes.flatMap oracleNodeWord ++
      natWord C.output.val ++ post)) := by
    simp [σ0, tStart, W, word_eq, WireExponent3_5.PrimAsm.ParseNat.enc]
  have h1 := WXExec.wm (readNatM_spec (cap := cap) false sCW rRF rRC rL rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ℓ [] _ σ0 hw0
    (by simp [σ0, tStart]) (by simp [σ0, tStart]) (by simp [σ0, tStart]) (by simp [σ0, tStart]) (by simp [σ0, tStart])
    (by simp [σ0, tStart]; omega))
  set σ1 := (σ0.seth sCW ([].length + stp false * (natWord ℓ).length)).setv rL (σ0.val rL + ℓ) with hσ1
  have hw1 : σ1.st sCW = enc false (natWord ℓ) ++ enc false (natWord C.nodes.length) ++ (C.nodes.flatMap oracleNodeWord ++
      natWord C.output.val ++ post) := by
    simp [σ1, σ0, tStart, W, word_eq, WireExponent3_5.PrimAsm.ParseNat.enc]
  have h2 := WXExec.wm (readNatM_spec (cap := cap) false sCW rRF rRC rM rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C.nodes.length (enc false (natWord ℓ)) _ σ1
    hw1 (by simp [σ1, σ0, tStart, WireExponent3_5.PrimAsm.ParseNat.enc, stp]) (by simp [σ1, σ0, tStart])
    (by simp [σ1, σ0, tStart]) (by simp [σ1, σ0, tStart]) (by simp [σ1, σ0, tStart]) (by simp [σ1, σ0, tStart]; omega))
  set σ2 := (σ1.seth sCW ((enc false (natWord ℓ)).length + stp false * (natWord C.nodes.length).length)).setv rM
    (σ1.val rM + C.nodes.length) with hσ2
  -- 3, 4. TT := 2^ℓ
  have h3 := WXExec.inc cap rTT σ2 (by simp [σ2, σ1, σ0, tStart]; omega)
  set σ3 := σ2.setv rTT (σ2.val rTT + 1) with hσ3
  have h4 := pow_exec cap σ3 ℓ (by simp [σ3, σ2, σ1, σ0, tStart]) (by simp [σ3, σ2, σ1, σ0, tStart])
    (by simp [σ3, σ2, σ1, σ0, tStart]) (by simp [σ3, σ2, σ1, σ0, tStart]) (by simp [σ3, σ2, σ1, σ0, tStart]) (by omega)
  set σ4 := σ3.setv rTT (2 ^ ℓ) with hσ4
  -- 5, 6. KK := T(2ℓ+1)
  have h5 := copyReg_exec (cap := cap) rTT rKK rT2 (by decide) (by decide) (by decide) (2 ^ ℓ) σ4 (by simp [σ4])
    (by simp [σ4, σ3, σ2, σ1, σ0, tStart]) (by simp [σ4, σ3, σ2, σ1, σ0, tStart]; omega) (by omega)
  set σ5 := σ4.setv rKK (σ4.val rKK + 2 ^ ℓ) with hσ5
  have h6 := kk_exec cap σ5 ℓ (2 ^ ℓ) (by simp [σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by simp [σ5, σ4, σ3, σ2, σ1, σ0, tStart]) (by simp [σ5, σ4]) (by simp [σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by simp [σ5, σ4, σ3, σ2, σ1, σ0, tStart]) (by omega)
  set σ6 := σ5.setv rKK (2 ^ ℓ * (2 * ℓ + 1)) with hσ6
  -- 7. const false
  have hcl6 : Clean Rw rTN σ6 := clean_of σ6 (fun r hr => by
    revert hr; fin_cases r <;> simp [σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
  have h7 := nodeW_spec cap sG Rw rTN hTR tZero (by intro i; fin_cases i <;> simp [tZero, FieldOK])
    (BooleanNode.const false : BooleanNode 0) σ6
    (by intro i; fin_cases i <;> simp [fieldVal, regSum, tZero, PCPPRequestNodeSchema.fields])
    (by intro i; fin_cases i <;> simp [tZero]) 0
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields]) hcl6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by rw [Rw7]; simp [σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart]; rw [show PCPPRequestNodeSchema.native
      (BooleanNode.const false : BooleanNode 0) = zb from rfl, zb_length]; omega)
  rw [Rw7, show PCPPRequestNodeSchema.native (BooleanNode.const false : BooleanNode 0) = zb from rfl] at h7
  set σ7 := appendO σ6 sG rR7 (marks zb) with hσ7
  -- 8. the inputs
  have h8 := inputs_exec cap σ7 (2 ^ ℓ) (by simp [σ7, σ6, σ5, σ4]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (fun r hr => by revert hr; fin_cases r <;> simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart, zb_len, zb_length]; omega)
  set σ8 := inSt σ7 (2 ^ ℓ) with hσ8
  -- 9. clear A
  have h9 := clearReg_exec (cap := cap) rA (2 ^ ℓ) σ8 (by simp [σ8, inSt]) (by omega)
  set σ9 := σ8.setv rA 0 with hσ9
  -- 10. const true
  have hcl9 : Clean Rw rTN σ9 := clean_of σ9 (fun r hr => by
    revert hr; fin_cases r <;> simp [σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by simp [σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
  have hib := inB_length_le (2 ^ ℓ) (2 ^ ℓ + 1) (by omega)
  have h10 := nodeW_spec cap sG Rw rTN hTR tOne (by intro i; fin_cases i <;> simp [tOne, FieldOK])
    (BooleanNode.const true : BooleanNode 0) σ9
    (by intro i; fin_cases i <;> simp [fieldVal, regSum, tOne, PCPPRequestNodeSchema.fields])
    (by intro i; fin_cases i <;> simp [tOne]) 1
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields]) hcl9
    (by simp [σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by
      rw [Rw7]; simp [σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart, marks_len, zb_length]
      rw [show PCPPRequestNodeSchema.native (BooleanNode.const true : BooleanNode 0) = ob from rfl, ob_len]; omega)
  rw [Rw7, show PCPPRequestNodeSchema.native (BooleanNode.const true : BooleanNode 0) = ob from rfl] at h10
  set σ10 := appendO σ9 sG rR7 (marks ob) with hσ10
  -- 11–14. NP := T + 2, SC := T
  have h11 := copyReg_exec (cap := cap) rTT rNP rT2 (by decide) (by decide) (by decide) (2 ^ ℓ) σ10
    (by simp [σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4]) (by simp [σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by simp [σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart]; omega) (by omega)
  set σ11 := σ10.setv rNP (σ10.val rNP + 2 ^ ℓ) with hσ11
  have h12 := WXExec.inc cap rNP σ11 (by simp [σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart]; omega)
  set σ12 := σ11.setv rNP (σ11.val rNP + 1) with hσ12
  have h13 := WXExec.inc cap rNP σ12
    (by simp [σ12, σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart] <;> omega)
  set σ13 := σ12.setv rNP (σ12.val rNP + 1) with hσ13
  have h14 := copyReg_exec (cap := cap) rTT rSC rT2 (by decide) (by decide) (by decide) (2 ^ ℓ) σ13
    (by simp [σ13, σ12, σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4])
    (by simp [σ13, σ12, σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart])
    (by simp [σ13, σ12, σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart]; omega) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5
    (WXExec.seq h6 (WXExec.seq (WXExec.wm h7) (WXExec.seq h8 (WXExec.seq h9 (WXExec.seq (WXExec.wm h10)
    (WXExec.seq h11 (WXExec.seq h12 (WXExec.seq h13 h14))))))))))))) ?_ le_rfl) ?_
  · have hsb := startBytes_eq ℓ
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ13, σ12, σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart,
        preSeeds, hdr, hsb, marks_len, WireExponent3_5.PrimAsm.ParseNat.enc, stp] <;> ring
    · funext i; fin_cases i <;> simp [σ13, σ12, σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart,
        preSeeds, hsb, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append, W]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ13, σ12, σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart,
        preSeeds, preVal, hsb, marks_len, TCirc.S] <;> ring
    · rfl
  · unfold prologueCost
    simp [σ13, σ12, σ11, σ10, σ9, σ8, inSt, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, tStart]
    have : nodeCost 0 ≤ nodeCost 1 := nodeCost_mono (by omega)
    omega

/-! ## The epilogue -/

local notation "s3" => (3 : Fin 4)

/-- Write `r` ones (consuming `r`) to stream 3 (counter `CA`). -/
def onesTo (r : Fin 40) : WMX 3 40 := .whr r (.seq (WMX.dec r) (emitO s3 rCA true))

theorem onesTo_exec (cap : ℕ) (r : Fin 40) (hr : r ≠ rCA) : ∀ (n : ℕ) (σ : WState 3 40) (out L0 : List Bool),
    σ.val r = n → OutOn σ s3 rCA out L0 → out.length + n < cap → n ≤ cap →
    WXExec cap (onesTo r) σ ((outSt σ s3 rCA (out ++ List.replicate n true) L0).setv r 0) (n * 12 + 1)
  | 0, σ, out, L0, hn, hO, _, _ => by
    have e : (outSt σ s3 rCA (out ++ List.replicate 0 true) L0).setv r 0 = σ := by
      simp only [List.replicate_zero, List.append_nil]
      rw [outSt_self σ hO, ← hn, wsetv_same]
    rw [e]
    exact WXExec.mono (WXExec.whrF hn) (by omega)
  | n + 1, σ, out, L0, hn, hO, hc, hnc => by
    have h1 := WXExec.dec cap r σ (by omega)
    have hO1 : OutOn (σ.setv r (σ.val r - 1)) s3 rCA out L0 := outOn_setv hO r hr _
    have h2 := emitO_spec cap (σ.setv r (σ.val r - 1)) out L0 true hO1 (by omega)
    have ih := onesTo_exec cap r hr n (outSt (σ.setv r (σ.val r - 1)) s3 rCA (out ++ [true]) L0)
      (out ++ [true]) L0 (by simp [outSt, hn, Function.update_of_ne hr]) (outOn_outSt _ _ _ _ _) (by simp; omega)
      (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 h2) ih) ?_ le_rfl) (by omega)
    rw [outSt_outSt]
    have hrep : out ++ [true] ++ List.replicate n true = out ++ List.replicate (n + 1) true := by
      rw [List.append_assoc, List.singleton_append, List.replicate_succ]
    rw [hrep]
    apply WState.eq
    · funext i; simp only [outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    · funext i; simp only [outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    · funext i; simp only [outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · rfl

/-- **The epilogue**: the info word on stream 3, every stream rewound, every register cleared. -/
def epilogue : WMX 3 40 :=
  .seq (copyReg rTT rX rT2) <| .seq (onesTo rX) <| .seq (emitO s3 rCA false) <|
  .seq (copyReg rNP rX rT2) <| .seq (WMX.dec rX) <| .seq (onesTo rX) <|
  .seq (.wm (WM.rewind s3 rCA)) <|
  .seq (copyReg rR7 rTMP rT2) <| .seq (.wm (WM.rewind sCW rTMP)) <| .seq (.wm (WM.rewind sG rR7)) <|
  .seq (clearReg rL) <| .seq (clearReg rM) <| .seq (clearReg rTT) <| .seq (clearReg rKK) <|
  .seq (clearReg rNP) (clearReg rZ)

/-- The epilogue's cost bound. -/
def epilogueCost {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ :=
  100 * (2 ^ ℓ + (TCirc.tCircuit C).nodes.length + r7M C + ℓ + C.nodes.length + TCirc.K ℓ) + 100

/-- The epilogue's capacity. -/
def epilogueCap {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ :=
  2 * (2 ^ ℓ + (TCirc.tCircuit C).nodes.length + r7M C + ℓ + C.nodes.length + TCirc.K ℓ) + 100

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **The epilogue runs** from `postSeeds` to the emitter's end state. -/
theorem epilogue_exec {ℓ : ℕ} (hB : TBytesSpec) (C : OracleCircuit ℓ ℓ) (post junk : List Bool) (cap : ℕ)
    (hcap : epilogueCap C ≤ cap) :
    WXExec cap epilogue (postSeeds C post junk)
      (tFinish ((OracleOutput.word ⟨ℓ, C⟩) ++ post) (marks (tGraph C)) junk
        (tInfo (2 ^ ℓ) (TCirc.tCircuit C).output.val)) (epilogueCost C) := by
  have hN1 : 1 ≤ (TCirc.tCircuit C).nodes.length := by
    show 1 ≤ (TCirc.nodes C).length
    rw [TCirc.nodes_length]; unfold TCirc.base TCirc.S; omega
  have hout : (TCirc.tCircuit C).output.val = (TCirc.tCircuit C).nodes.length - 1 := rfl
  have hT1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hc := hcap
  unfold epilogueCap at hc
  set σ0 := postSeeds C post junk with hσ0
  -- 1. T ones
  have e1 := copyReg_exec (cap := cap) rTT rX rT2 (by decide) (by decide) (by decide) (2 ^ ℓ) σ0
    (by simp [σ0, postSeeds, postVal]) (by simp [σ0, postSeeds, postVal]) (by simp [σ0, postSeeds, postVal]; omega)
    (by omega)
  set σ1 := σ0.setv rX (σ0.val rX + 2 ^ ℓ) with hσ1
  have hO1 : OutOn σ1 s3 rCA [] [] := ⟨by simp [σ1, σ0, postSeeds, StablePartition.Workspace.overlay],
    by simp [σ1, σ0, postSeeds], by simp [σ1, σ0, postSeeds, postVal]⟩
  have e2 := onesTo_exec cap rX (by decide) (2 ^ ℓ) σ1 [] [] (by simp [σ1, σ0, postSeeds, postVal]) hO1
    (by simp; omega) (by omega)
  simp only [List.nil_append] at e2
  set σ2 := (outSt σ1 s3 rCA (List.replicate (2 ^ ℓ) true) []).setv rX 0 with hσ2
  -- 2. the separator
  have hO2 : OutOn σ2 s3 rCA (List.replicate (2 ^ ℓ) true) [] :=
    outOn_setv (outOn_outSt σ1 s3 rCA (List.replicate (2 ^ ℓ) true) []) rX (by decide) 0
  have e3 := emitO_spec cap σ2 _ [] false hO2 (by simp; omega)
  set σ3 := outSt σ2 s3 rCA (List.replicate (2 ^ ℓ) true ++ [false]) [] with hσ3
  -- 3. (TCirc.tCircuit C).nodes.length − 1 ones
  have e4 := copyReg_exec (cap := cap) rNP rX rT2 (by decide) (by decide) (by decide) (TCirc.tCircuit C).nodes.length σ3
    (by simp [σ3, σ2, σ1, σ0, outSt, postSeeds, postVal]) (by simp [σ3, σ2, σ1, σ0, outSt, postSeeds, postVal])
    (by simp [σ3, σ2, σ1, σ0, outSt, postSeeds, postVal]; omega) (by omega)
  set σ4 := σ3.setv rX (σ3.val rX + (TCirc.tCircuit C).nodes.length) with hσ4
  have e5 := WXExec.dec cap rX σ4 (by simp [σ4, σ3, σ2, outSt]; omega)
  set σ5 := σ4.setv rX (σ4.val rX - 1) with hσ5
  have hO5 : OutOn σ5 s3 rCA (List.replicate (2 ^ ℓ) true ++ [false]) [] :=
    outOn_setv (outOn_setv (outOn_outSt _ _ _ _ _) rX (by decide) _) rX (by decide) _
  have e6 := onesTo_exec cap rX (by decide) ((TCirc.tCircuit C).nodes.length - 1) σ5 _ [] (by simp [σ5, σ4, σ3, σ2, outSt]) hO5
    (by simp; omega) (by omega)
  set σ6 := (outSt σ5 s3 rCA (List.replicate (2 ^ ℓ) true ++ [false] ++ List.replicate ((TCirc.tCircuit C).nodes.length - 1) true) []).setv rX 0
    with hσ6
  have hinfo : List.replicate (2 ^ ℓ) true ++ [false] ++ List.replicate ((TCirc.tCircuit C).nodes.length - 1) true = tInfo (2 ^ ℓ) ((TCirc.tCircuit C).nodes.length - 1) := by
    simp [tInfo]
  -- 4. rewind stream 3
  have hIL : (tInfo (2 ^ ℓ) ((TCirc.tCircuit C).nodes.length - 1)).length = 2 ^ ℓ + (TCirc.tCircuit C).nodes.length := by simp [tInfo]; omega
  have e7 := WXExec.wm (wrewind_spec (cap := cap) s3 rCA (2 ^ ℓ + (TCirc.tCircuit C).nodes.length) σ6
    (by simp [σ6, outSt, hinfo, hIL]) (by simp [σ6, outSt, hinfo, hIL]; omega))
  set σ7 := (σ6.setv rCA 0).seth s3 (σ6.sh s3 - (2 ^ ℓ + (TCirc.tCircuit C).nodes.length)) with hσ7
  -- 5. rewind the word and G
  have hR7 : σ7.val rR7 = r7M C := by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt, postSeeds, postVal, r7M]
  have hT7 : σ7.val rTMP = 0 := by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt, postSeeds, postVal]
  have e8 := copyReg_exec (cap := cap) rR7 rTMP rT2 (by decide) (by decide) (by decide) (r7M C) σ7 hR7
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt, postSeeds, postVal]) (by rw [hT7]; omega) (by omega)
  set σ8 := σ7.setv rTMP (σ7.val rTMP + r7M C) with hσ8
  have e9 := WXExec.wm (wrewind_spec (cap := cap) sCW rTMP (r7M C) σ8
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt, postSeeds, postVal]) (by simp [σ8]; omega))
  set σ9 := (σ8.setv rTMP 0).seth sCW (σ8.sh sCW - r7M C) with hσ9
  have e10 := WXExec.wm (wrewind_spec (cap := cap) sG rR7 (r7M C) σ9
    (by simp [σ9, σ8, hR7]) (by simp [σ9, σ8, hR7]; omega))
  set σ10 := (σ9.setv rR7 0).seth sG (σ9.sh sG - r7M C) with hσ10
  -- 6. clear
  have e11 := clearReg_exec (cap := cap) rL ℓ σ10 (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt,
    postSeeds, postVal]) (by omega)
  set σ11 := σ10.setv rL 0 with hσ11
  have e12 := clearReg_exec (cap := cap) rM C.nodes.length σ11 (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2,
    σ1, σ0, outSt, postSeeds, postVal]) (by omega)
  set σ12 := σ11.setv rM 0 with hσ12
  have e13 := clearReg_exec (cap := cap) rTT (2 ^ ℓ) σ12 (by simp [σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2,
    σ1, σ0, outSt, postSeeds, postVal]) (by omega)
  set σ13 := σ12.setv rTT 0 with hσ13
  have e14 := clearReg_exec (cap := cap) rKK (TCirc.K ℓ) σ13 (by simp [σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4,
    σ3, σ2, σ1, σ0, outSt, postSeeds, postVal]) (by omega)
  set σ14 := σ13.setv rKK 0 with hσ14
  have e15 := clearReg_exec (cap := cap) rNP (TCirc.tCircuit C).nodes.length σ14 (by simp [σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4,
    σ3, σ2, σ1, σ0, outSt, postSeeds, postVal]) (by omega)
  set σ15 := σ14.setv rNP 0 with hσ15
  have e16 := clearReg_exec (cap := cap) rZ (2 ^ ℓ) σ15 (by simp [σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5,
    σ4, σ3, σ2, σ1, σ0, outSt, postSeeds, postVal]) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5
    (WXExec.seq e6 (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 (WXExec.seq e10 (WXExec.seq e11 (WXExec.seq e12
    (WXExec.seq e13 (WXExec.seq e14 (WXExec.seq e15 e16))))))))))))))) ?_ le_rfl) ?_
  ·
    have hhdr : hdr C ≤ r7M C := by
      have hw := hB C
      have h1 : hdr C ≤ (OracleOutput.word ⟨ℓ, C⟩).length := by
        unfold hdr; rw [word_eq]; simp only [List.length_append]; omega
      have h2 := seedsB_le C 1 (TCirc.T ℓ) Nat.one_le_two_pow
      have h3 : seedsB C 1 = (TCirc.seed C 0).flatMap PCPPRequestNodeSchema.native := by simp [seedsB]
      rw [h3] at h2
      unfold r7M; simp only [marks_len]; rw [tGraph_eq, List.length_append]
      unfold startBytes at *
      omega
    have hhdr' : hdr C ≤ 2 * (tGraph C).length := by simpa [r7M, marks_len] using hhdr
    rw [hout, ← hinfo]
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt,
        postSeeds, postVal, tFinish, r7M, hIL, hinfo] <;> omega
    · funext i; fin_cases i <;> simp [σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt,
        postSeeds, tFinish, StablePartition.Workspace.overlay]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ15, σ14, σ13, σ12, σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt,
        postSeeds, postVal, tFinish]
    · rfl
  · unfold epilogueCost
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, outSt, postSeeds, postVal, hIL, hinfo]
    omega

end NearCubicGates.Close.ENP.TEmit
