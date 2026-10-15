import Proof.Gates.ENP.TableNode
import Proof.Gates.ENP.TableCost

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

/-! ## The word of a node and its block -/

/-- The three word fields of a node (`(5, 0, 0)` for an oracle gate). -/
def wf {ℓ : ℕ} : OracleNode ℓ ℓ → ℕ × ℕ × ℕ
  | .const b => (0, b.toNat, 0)
  | .input i => (1, i.val, 0)
  | .not c => (2, c, 0)
  | .and l r => (3, l, r)
  | .or l r => (4, l, r)
  | .oracle _ => (5, 0, 0)

/-- A node that is not an oracle gate. -/
def Plain {ℓ : ℕ} (nd : OracleNode ℓ ℓ) : Prop := ∀ args, nd ≠ .oracle args

theorem word_plain {ℓ : ℕ} (nd : OracleNode ℓ ℓ) (h : Plain nd) :
    oracleNodeWord nd = natWord (wf nd).1 ++ (natWord (wf nd).2.1 ++ natWord (wf nd).2.2) := by
  cases nd with
  | oracle args => exact absurd rfl (h args)
  | _ => simp [oracleNodeWord, wf]

theorem word_oracle {ℓ : ℕ} (args : Fin ℓ → ℕ) :
    oracleNodeWord (.oracle args : OracleNode ℓ ℓ) = natWord 5 ++ (List.ofFn args).flatMap natWord := by
  simp only [oracleNodeWord, args_word]

theorem wf_tag_le {ℓ : ℕ} (nd : OracleNode ℓ ℓ) (h : Plain nd) : (wf nd).1 ≤ 4 := by
  cases nd with
  | oracle args => exact absurd rfl (h args)
  | _ => simp [wf]

theorem wf_f2 {ℓ : ℕ} (nd : OracleNode ℓ ℓ) (h : (wf nd).1 ≤ 2) : (wf nd).2.2 = 0 := by
  cases nd <;> simp_all [wf]

theorem translate_fields {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z : ℕ) (nd : OracleNode ℓ ℓ) (h : Plain nd) (i : Fin 3) :
    PCPPRequestNodeSchema.fields (TCirc.translate C z nd) i =
      outFields (wf nd).1 (wf nd).2.1 (wf nd).2.2 z (TCirc.base C z) (TCirc.K ℓ) i := by
  have hK : 1 ≤ TCirc.K ℓ := Nat.mul_pos (Nat.two_pow_pos ℓ) (by omega)
  cases nd with
  | oracle args => exact absurd rfl (h args)
  | const b => fin_cases i <;> simp [TCirc.translate, PCPPRequestNodeSchema.fields, outFields, wf]
  | input j => fin_cases i <;> simp [TCirc.translate, PCPPRequestNodeSchema.fields, outFields, wf]
  | not c => fin_cases i <;> simp [TCirc.translate, PCPPRequestNodeSchema.fields, outFields, wf, TCirc.img] <;> omega
  | and l r => fin_cases i <;> simp [TCirc.translate, PCPPRequestNodeSchema.fields, outFields, wf, TCirc.img] <;> omega
  | or l r => fin_cases i <;> simp [TCirc.translate, PCPPRequestNodeSchema.fields, outFields, wf, TCirc.img] <;> omega

theorem block_plain {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z c : ℕ) (nd : OracleNode ℓ ℓ) (h : Plain nd) :
    (TCirc.block C z c nd).flatMap PCPPRequestNodeSchema.native =
      (List.replicate (TCirc.K ℓ - 1) zb).flatten ++ PCPPRequestNodeSchema.native (TCirc.translate C z nd) := by
  have e : ∀ n, (List.replicate n (BooleanNode.const false : BooleanNode (TCirc.T ℓ))).flatMap
      PCPPRequestNodeSchema.native = (List.replicate n zb).flatten := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.flatMap_cons, ih, List.replicate_succ, List.flatten_cons]; rfl
  cases nd with
  | oracle args => exact absurd rfl (h args)
  | _ => simp only [TCirc.block, List.flatMap_append, e, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-! ## Cost monotonicity of the plain pieces -/

theorem imgCost_mono {x x' k bz bz' : ℕ} (hx : x ≤ x') (hb : bz ≤ bz') : imgCost x k bz ≤ imgCost x' k bz' := by
  unfold imgCost
  have h1 := nbl_mono hx
  have h2 : 2 ^ natBitLength x ≤ 2 ^ natBitLength x' := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤
      (natBitLength x' + 2) * (40 * 2 ^ natBitLength x' + 40) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : x * (18 * k + 7) ≤ x' * (18 * k + 7) := Nat.mul_le_mul_right _ hx
  omega

theorem fieldsCost_mono {f1 f2 k bz z f1' f2' bz' z' : ℕ} (h1 : f1 ≤ f1') (h2 : f2 ≤ f2') (hb : bz ≤ bz')
    (hz : z ≤ z') : fieldsCost f1 f2 k bz z ≤ fieldsCost f1' f2' k bz' z' := by
  unfold fieldsCost
  have a1 := imgCost_mono (k := k) h1 hb
  have a2 := imgCost_mono (k := k) h2 hb
  have a3 : f1 * (13 * z + 40) ≤ f1' * (13 * z' + 40) := Nat.mul_le_mul h1 (by omega)
  have a4 : f1 * k ≤ f1' * k := Nat.mul_le_mul_right _ h1
  have a5 := imgCost_mono (k := 1) h1 (le_refl 0)
  omega

theorem plainCost_mono {k V V' : ℕ} (h : V ≤ V') : plainCost k V ≤ plainCost k V' := by
  unfold plainCost
  have := nodeCost_mono h
  omega

/-! ## The node program -/

/-- Read the tag; `TMP := tag − 4` (nonzero exactly for an oracle gate). -/
def nodeHead (ε : Bool) : WMX 3 40 :=
  .seq (.wm (readNatM ε sCW rRF rRC rTAG rRP rRT)) <| .seq (copyReg rTAG rTMP rT2) <|
  .seq (WMX.dec rTMP) <| .seq (WMX.dec rTMP) <| .seq (WMX.dec rTMP) (WMX.dec rTMP)

/-- **One node of `C` at the current seed** (paper §11.6 stage 2). -/
def nodeBody (ε : Bool) : WMX 3 40 :=
  .seq (nodeHead ε) <|
  .ifr rTMP (.seq (clearReg rTMP) (.seq (oracleBlock ε) (clearReg rTAG))) (.seq (plainFields ε) emitPlain)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem nodeHead_exec (ε : Bool) (cap : ℕ) (σ : WState 3 40) (t : ℕ) (pre rest : List Bool) (ht : t ≤ 5)
    (hst : σ.st sCW = pre ++ enc ε (natWord t) ++ rest) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hTAG : σ.val rTAG = 0) (hTMP : σ.val rTMP = 0) (hT2 : σ.val rT2 = 0) (hcap : 40 ≤ cap) :
    WXExec cap (nodeHead ε) σ (((σ.seth sCW (pre.length + stp ε * (natWord t).length)).setv rTAG t).setv rTMP (t - 4))
      2000 := by
  have hb : (natBitLength t + 2) * (40 * 2 ^ natBitLength t + 40) ≤ 1800 := by
    interval_cases t <;> norm_num [natBitLength]
  have h1 := WXExec.wm (readNatM_spec (cap := cap) ε sCW rRF rRC rTAG rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t pre rest σ hst hsh hRF hRC hRP
    hRT (by rw [hTAG]; interval_cases t <;> norm_num [natBitLength] <;> omega))
  set σ1 := (σ.seth sCW (pre.length + stp ε * (natWord t).length)).setv rTAG (σ.val rTAG + t) with hσ1
  have h2 := copyReg_exec (cap := cap) rTAG rTMP rT2 (by decide) (by decide) (by decide) t σ1 (by simp [σ1, hTAG])
    (by simp [σ1, hT2]) (by simp [σ1, hTMP]; omega) (by omega)
  set σ2 := σ1.setv rTMP (σ1.val rTMP + t) with hσ2
  have d1 := WXExec.dec cap rTMP σ2 (by simp [σ2, σ1, hTMP]; omega)
  have d2 := WXExec.dec cap rTMP (σ2.setv rTMP (σ2.val rTMP - 1)) (by simp [σ2, σ1, hTMP]; omega)
  have d3 := WXExec.dec cap rTMP ((σ2.setv rTMP (σ2.val rTMP - 1)).setv rTMP
    ((σ2.setv rTMP (σ2.val rTMP - 1)).val rTMP - 1)) (by simp [σ2, σ1, hTMP]; omega)
  have d4 := WXExec.dec cap rTMP (((σ2.setv rTMP (σ2.val rTMP - 1)).setv rTMP
    ((σ2.setv rTMP (σ2.val rTMP - 1)).val rTMP - 1)).setv rTMP (((σ2.setv rTMP (σ2.val rTMP - 1)).setv rTMP
    ((σ2.setv rTMP (σ2.val rTMP - 1)).val rTMP - 1)).val rTMP - 1)) (by simp [σ2, σ1, hTMP]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq d1 (WXExec.seq d2
    (WXExec.seq d3 d4))))) ?_ le_rfl) ?_
  · apply WState.eq <;> try rfl
    funext r; revert r; apply fin40_cases; intro i hi
    interval_cases i <;> simp [σ2, σ1, hTAG, hTMP] <;> omega
  · omega

def nst (σ : WState 3 40) (h np : ℕ) (L1 u : List Bool) : WState 3 40 :=
  appendO (((σ.seth sCW h).sets sARGS L1).setv rNP np) sG rR7 (marks u)

/-- The node cost bound (uniform over the nodes and seeds below the maxima). -/
def nodeCostB (ℓ Xm bzM npM zM : ℕ) : ℕ :=
  2100 + oracleCost ℓ (TCirc.T ℓ) npM Xm (TCirc.K ℓ) bzM + fieldsCost Xm Xm (TCirc.K ℓ) bzM zM +
    plainCost (TCirc.K ℓ) (bzM + Xm * TCirc.K ℓ + TCirc.K ℓ + 5) + 100

/-- The fields of a node of `C` are below `Xm`. -/
def FieldsLe {ℓ : ℕ} (Xm : ℕ) : OracleNode ℓ ℓ → Prop
  | .oracle args => ∀ j, args j ≤ Xm
  | nd => (wf nd).2.1 ≤ Xm ∧ (wf nd).2.2 ≤ Xm

/-- The block-capacity bound `Vb` of the oracle blocks. -/
def vbM (ℓ Xm bzM npM : ℕ) : ℕ := npM + TCirc.T ℓ * (2 * ℓ + 1) + TCirc.T ℓ + (bzM + Xm * TCirc.K ℓ + TCirc.K ℓ) + 4

/-- The capacity needed by a node (oracle blocks' two conditions, the plain fields, the plain emission, the head). -/
def NodeCap (ℓ Xm bzM npM zM R7M cap : ℕ) : Prop :=
  2 * ℓ + 2 ^ (natBitLength Xm + 1) + bzM + Xm * TCirc.K ℓ + TCirc.K ℓ +
      ℓ * (bzM + Xm * TCirc.K ℓ + TCirc.K ℓ) + 10 ≤ cap ∧
    2 * TCirc.T ℓ + vbM ℓ Xm bzM npM + 3 * ℓ + ℓ * (bzM + Xm * TCirc.K ℓ + TCirc.K ℓ) + R7M +
      2 * (TCirc.T ℓ * (ℓ * (12 * vbM ℓ Xm bzM npM + 18) + (6 * vbM ℓ Xm bzM npM + 9))) +
      14 * ℓ * (6 * vbM ℓ Xm bzM npM + 9) + 300 * (vbM ℓ Xm bzM npM + 10) ≤ cap ∧
    2 * 2 ^ (natBitLength Xm + 1) + bzM + 2 * (Xm * TCirc.K ℓ) + TCirc.K ℓ + 2 * zM + Xm + 24 ≤ cap ∧
    R7M + 18 * TCirc.K ℓ + 20 * (bzM + Xm * TCirc.K ℓ + TCirc.K ℓ + 5) + 60 + npM + TCirc.K ℓ ≤ cap ∧
    40 ≤ cap

theorem K_pos (ℓ : ℕ) : 1 ≤ TCirc.K ℓ := Nat.mul_pos (Nat.two_pow_pos ℓ) (by omega)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **An oracle gate** at seed `z`: the multiplexer block (paper §11.6 stage 2). -/
theorem nodeOracle_exec {ℓ : ℕ} (ε : Bool) (cap : ℕ) (C : OracleCircuit ℓ ℓ) (z c : ℕ) (args : Fin ℓ → ℕ)
    (σ : WState 3 40) (pre rest L0 : List Bool) (Xm bzM npM zM R7M : ℕ)
    (hst : σ.st sCW = pre ++ enc ε (oracleNodeWord (.oracle args : OracleNode ℓ ℓ)) ++ rest)
    (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hTAG : σ.val rTAG = 0) (hIMG : σ.val rIMG = 0) (hT : σ.val rTN = 0) (hTMP : σ.val rTMP = 0)
    (hT2 : σ.val rT2 = 0) (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0) (hW : σ.val rW = 0)
    (hF1 : σ.val rF1 = 0) (hF2 : σ.val rF2 = 0) (hJ : σ.val rJJ = 0) (hA : σ.val rA = 0) (hLC1 : σ.val rLC1 = 0)
    (hLC2 : σ.val rLC2 = 0) (hLC3 : σ.val rLC3 = 0)
    (hBZ : σ.val rBZ = TCirc.base C z) (hK : σ.val rKK = TCirc.K ℓ) (hTT : σ.val rTT = TCirc.T ℓ)
    (hL : σ.val rL = ℓ) (hNP : σ.val rNP = TCirc.bs C z c)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hG : σ.sh sG = (σ.st sG).length) (hO : OutOn σ sARGS rCA [] L0)
    (hXm : ∀ j, args j ≤ Xm) (hbz : TCirc.base C z ≤ bzM) (hnp : TCirc.bs C z c ≤ npM) (hR7 : σ.val rR7 ≤ R7M)
    (hcap : NodeCap ℓ Xm bzM npM zM R7M cap) :
    WXExec cap (nodeBody ε) σ
      (nst σ (pre.length + stp ε * (oracleNodeWord (.oracle args : OracleNode ℓ ℓ)).length)
        (TCirc.bs C z c + TCirc.K ℓ)
        (StablePartition.Workspace.overlay
          (argsStream ((List.ofFn args).map (fun x => TCirc.base C z + x * TCirc.K ℓ + TCirc.K ℓ - 1))) L0)
        ((TCirc.block C z c (.oracle args)).flatMap PCPPRequestNodeSchema.native))
      (nodeCostB ℓ Xm bzM npM zM) := by
  obtain ⟨hcA, hcB, -, -, hc40⟩ := hcap
  have hk := K_pos ℓ
  have hw := word_oracle args
  have hcw : σ.st sCW = pre ++ enc ε (natWord 5) ++ (enc ε ((List.ofFn args).flatMap natWord) ++ rest) := by
    rw [hst, hw, enc_append]; simp only [List.append_assoc]
  -- the head
  have hH := nodeHead_exec ε cap σ 5 pre _ (by norm_num) hcw hsh hRF hRC hRP hRT hTAG hTMP hT2 hc40
  set σH := ((σ.seth sCW (pre.length + stp ε * (natWord 5).length)).setv rTAG 5).setv rTMP (5 - 4) with hσH
  have c1 := clearReg_exec (cap := cap) rTMP 1 σH (by simp [σH]) (by omega)
  set σ1 := σH.setv rTMP 0 with hσ1
  have hP0 : (pre ++ enc ε (natWord 5)).length = pre.length + stp ε * (natWord 5).length := by simp [enc_length]
  have hxk : Xm * TCirc.K ℓ ≤ Xm * TCirc.K ℓ := le_rfl
  have hbm : ℓ * (TCirc.base C z + Xm * TCirc.K ℓ + TCirc.K ℓ) ≤ ℓ * (bzM + Xm * TCirc.K ℓ + TCirc.K ℓ) :=
    Nat.mul_le_mul_left _ (by omega)
  have hS : 1 ≤ TCirc.bs C z c := by simp [TCirc.bs, TCirc.base, TCirc.S]; omega
  have ob := oracleBlock_exec (ℓ := ℓ) ε cap σ1 (List.ofFn args) (by simp) (TCirc.T ℓ) (TCirc.K ℓ) (TCirc.base C z) Xm
    (TCirc.bs C z c) (vbM ℓ Xm bzM npM) (pre ++ enc ε (natWord 5)) rest L0
    (by simp only [σ1, σH, WState.setv_st, WState.seth_st]; rw [hcw]; simp only [List.append_assoc])
    (by simp [σ1, σH, hP0])
    (by simp [σ1, σH, hRF]) (by simp [σ1, σH, hRC]) (by simp [σ1, σH, hRV]) (by simp [σ1, σH, hRP])
    (by simp [σ1, σH, hRT]) (by simp [σ1, σH, hIMG]) (by simp [σ1, σH, hT]) (by simp [σ1, σH, hBZ])
    (by simp [σ1, σH, hK]) hk (by simp [σ1, σH, hL]) (by simp [σ1, σH, hLC2])
    ⟨by simp [σ1, σH, hO.1], by simp [σ1, σH, hO.2.1], by simp [σ1, σH, hO.2.2]⟩
    (by intro x hx; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx; exact hXm j)
    (by simp [σ1, σH, hX]) (by simp [σ1, σH, hY]) (by simp [σ1, σH, hBB]) (by simp [σ1, σH, hW])
    (by simp [σ1, σH, hF1]) (by simp [σ1, σH, hF2]) (by simp [σ1, σH, hJ]) (by simp [σ1, σH, hNP]) hS
    (by simp [σ1, σH, hA]) (by simp [σ1, σH, hLC1]) (by simp [σ1, σH]) (by simp [σ1, σH, hT2])
    (by simp [σ1, σH, hTT]) (by simp [σ1, σH, hLC3])
    (fun r hr => by
      have := hwr r hr
      have h1 : r ≠ rTAG := by intro h; subst h; simp at hr
      have h2 : r ≠ rTMP := by intro h; subst h; simp at hr
      simp [σ1, σH, Function.update_of_ne h1, Function.update_of_ne h2, this])
    (by simp [σ1, σH, hG]) (by unfold vbM; omega) (by omega)
    (by have : σ1.val rR7 = σ.val rR7 := by simp [σ1, σH]
        rw [this]; unfold vbM at hcB ⊢; omega)
  set σ2 := ost (ℓ := ℓ) ε σ1 (pre ++ enc ε (natWord 5)).length (List.ofFn args)
    ((List.ofFn args).map (fun x => TCirc.base C z + x * TCirc.K ℓ + TCirc.K ℓ - 1)) L0 (TCirc.bs C z c) (TCirc.T ℓ)
    with hσ2
  have c2 := clearReg_exec (cap := cap) rTAG 5 σ2 (by simp [σ2, ost, σ1, σH]) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq hH (WXExec.ifrT (Q := .seq (plainFields ε) emitPlain)
    (by simp [σH]) (WXExec.seq c1 (WXExec.seq ob c2)))) ?_ le_rfl) ?_
  · have hob := oracle_bytes C z c args
    have hlen : pre.length + stp ε * (oracleNodeWord (.oracle args : OracleNode ℓ ℓ)).length =
        (pre ++ enc ε (natWord 5)).length + stp ε * ((List.ofFn args).flatMap natWord).length := by
      rw [hw, hP0, List.length_append, Nat.mul_add, Nat.add_assoc]
    rw [hlen, hob]
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ2, ost, σ1, σH, nst, hO.2.1]
    · funext i; fin_cases i <;> simp [σ2, ost, σ1, σH, nst]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ2, ost, σ1, σH, nst, hTAG, hTMP]
    · rfl
  · unfold nodeCostB
    have := oracleCost_mono (ℓ := ℓ) (T := TCirc.T ℓ) (kk := TCirc.K ℓ) hnp (le_refl Xm) hbz
    omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **A plain node** at seed `z`: `K − 1` fillers and the translated gate (paper §11.6 stage 2). -/
theorem nodePlain_exec {ℓ : ℕ} (ε : Bool) (cap : ℕ) (C : OracleCircuit ℓ ℓ) (z c : ℕ) (nd : OracleNode ℓ ℓ)
    (hnd : Plain nd) (σ : WState 3 40) (pre rest : List Bool) (Xm bzM npM zM R7M np : ℕ)
    (hst : σ.st sCW = pre ++ enc ε (oracleNodeWord nd) ++ rest) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hTAG : σ.val rTAG = 0) (hIMG : σ.val rIMG = 0) (hIMG2 : σ.val rIMG2 = 0) (hT : σ.val rTN = 0)
    (hTMP : σ.val rTMP = 0) (hT2 : σ.val rT2 = 0) (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0)
    (hBZ : σ.val rBZ = TCirc.base C z) (hK : σ.val rKK = TCirc.K ℓ) (hZ : σ.val rZ = z) (hNP : σ.val rNP = np)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hG : σ.sh sG = (σ.st sG).length)
    (hf1 : (wf nd).2.1 ≤ Xm) (hf2 : (wf nd).2.2 ≤ Xm) (hbz : TCirc.base C z ≤ bzM) (hz : z ≤ zM) (hnp : np ≤ npM)
    (hR7 : σ.val rR7 ≤ R7M) (hcap : NodeCap ℓ Xm bzM npM zM R7M cap) :
    WXExec cap (nodeBody ε) σ
      (nst σ (pre.length + stp ε * (oracleNodeWord nd).length) (np + TCirc.K ℓ) (σ.st sARGS)
        ((TCirc.block C z c nd).flatMap PCPPRequestNodeSchema.native))
      (nodeCostB ℓ Xm bzM npM zM) := by
  obtain ⟨-, -, hcC, hcD, hc40⟩ := hcap
  have hk := K_pos ℓ
  have ht4 : (wf nd).1 ≤ 4 := wf_tag_le nd hnd
  have hw := word_plain nd hnd
  have hcw : σ.st sCW = pre ++ enc ε (natWord (wf nd).1) ++ (enc ε (natWord (wf nd).2.1 ++ natWord (wf nd).2.2) ++ rest) := by
    rw [hst, hw, enc_append]; simp only [List.append_assoc]
  -- the head
  have hH := nodeHead_exec ε cap σ (wf nd).1 pre _ (by omega) hcw hsh hRF hRC hRP hRT hTAG hTMP hT2 hc40
  set σH := ((σ.seth sCW (pre.length + stp ε * (natWord (wf nd).1).length)).setv rTAG (wf nd).1).setv rTMP ((wf nd).1 - 4) with hσH
  have hHT : σH.val rTMP = 0 := by simp [σH]; omega
  have hP0 : (pre ++ enc ε (natWord (wf nd).1)).length = pre.length + stp ε * (natWord (wf nd).1).length := by simp [enc_length]
  have hxk1 : (wf nd).2.1 * TCirc.K ℓ ≤ Xm * TCirc.K ℓ := Nat.mul_le_mul_right _ hf1
  have hxk2 : (wf nd).2.2 * TCirc.K ℓ ≤ Xm * TCirc.K ℓ := Nat.mul_le_mul_right _ hf2
  have hpw1 : 2 ^ (natBitLength (wf nd).2.1 + 1) ≤ 2 ^ (natBitLength Xm + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := nbl_mono hf1; omega)
  have hpw2 : 2 ^ (natBitLength (wf nd).2.2 + 1) ≤ 2 ^ (natBitLength Xm + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := nbl_mono hf2; omega)
  have pf := plainFields_exec ε cap σH (wf nd).1 (wf nd).2.1 (wf nd).2.2 z (TCirc.base C z) (TCirc.K ℓ) (pre ++ enc ε (natWord (wf nd).1)) rest ht4
    (fun h => wf_f2 nd h) (by simp [σH, hcw]) (by simp [σH, hP0])
    (by simp [σH, hRF]) (by simp [σH, hRC]) (by simp [σH, hRV]) (by simp [σH, hRP]) (by simp [σH, hRT])
    (by simp [σH, hIMG]) (by simp [σH, hIMG2]) (by simp [σH, hT]) (by simp [σH, hBZ]) (by simp [σH, hK]) hk
    (by simp [σH, hZ]) (by simp [σH]) hHT (by simp [σH, hT2]) (by simp [σH, hX]) (by simp [σH, hY])
    (by simp [σH, hBB]) (by omega)
  set σP := (((σH.seth sCW ((pre ++ enc ε (natWord (wf nd).1)).length + stp ε * (natWord (wf nd).2.1 ++ natWord (wf nd).2.2).length)).setv
    rTAG (outFields (wf nd).1 (wf nd).2.1 (wf nd).2.2 z (TCirc.base C z) (TCirc.K ℓ) 0)).setv rIMG2
    (outFields (wf nd).1 (wf nd).2.1 (wf nd).2.2 z (TCirc.base C z) (TCirc.K ℓ) 1)).setv rIMG
    (outFields (wf nd).1 (wf nd).2.1 (wf nd).2.2 z (TCirc.base C z) (TCirc.K ℓ) 2) with hσP
  have htf := translate_fields C z nd hnd
  have hV : ∀ i, PCPPRequestNodeSchema.fields (TCirc.translate C z nd) i ≤ bzM + Xm * TCirc.K ℓ + TCirc.K ℓ + 5 := by
    intro i; rw [htf]
    have hb : (z.testBit (wf nd).2.1).toNat ≤ 1 := by cases z.testBit (wf nd).2.1 <;> simp
    have hXK : Xm ≤ Xm * TCirc.K ℓ := Nat.le_mul_of_pos_right _ hk
    unfold outFields
    split_ifs <;> fin_cases i <;> simp <;> omega
  have ep := emitPlain_exec cap σP (TCirc.translate C z nd) (TCirc.K ℓ) np (bzM + Xm * TCirc.K ℓ + TCirc.K ℓ + 5)
    (by rw [htf]; simp [σP]) (by rw [htf]; simp [σP]) (by rw [htf]; simp [σP]) hV (by simp [σP, σH, hK]) hk
    (by simp [σP, σH, hNP]) (by simp [σP, σH]; omega) (by simp [σP, σH, hT2])
    (fun r hr => by
      have := hwr r hr
      have h1 : r ≠ rTAG := by intro h; subst h; simp at hr
      have h2 : r ≠ rTMP := by intro h; subst h; simp at hr
      have h3 : r ≠ rIMG := by intro h; subst h; simp at hr
      have h4 : r ≠ rIMG2 := by intro h; subst h; simp at hr
      simp [σP, σH, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
        Function.update_of_ne h4, this])
    (by simp [σP, σH, hT]) (by simp [σP, σH, hG]) (by simp [σP, σH]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq hH (WXExec.ifrF
    (P := .seq (clearReg rTMP) (.seq (oracleBlock ε) (clearReg rTAG))) hHT (WXExec.seq pf ep))) ?_ le_rfl) ?_
  · have hlen : pre.length + stp ε * (oracleNodeWord nd).length =
        (pre ++ enc ε (natWord (wf nd).1)).length + stp ε * (natWord (wf nd).2.1 ++ natWord (wf nd).2.2).length := by
      rw [hw, hP0, List.length_append, Nat.mul_add, Nat.add_assoc]
    rw [hlen, block_plain C z c nd hnd]
    apply WState.eq
    · funext i; fin_cases i <;> simp [σP, σH, nst]
    · funext i; fin_cases i <;> simp [σP, σH, nst]
    · funext i; revert i; apply fin40_cases; intro i hi
      have ht40 : (wf nd).1 - 4 = 0 := by omega
      interval_cases i <;> simp [σP, σH, nst, hTAG, hTMP, hIMG, hIMG2, ht40]
    · rfl
  · unfold nodeCostB
    have h1 := fieldsCost_mono (k := TCirc.K ℓ) hf1 hf2 hbz hz
    omega

set_option maxHeartbeats 4000000 in
/-- **One node of `C`** at seed `z` (paper §11.6 stage 2): the word head moves past the node's word, `G` gains the
native bytes of `TCirc.block`, `NP` advances by `K`; `ARGS` (head and counter `0`) may change its contents. -/
theorem nodeBody_exec {ℓ : ℕ} (ε : Bool) (cap : ℕ) (C : OracleCircuit ℓ ℓ) (z c : ℕ) (nd : OracleNode ℓ ℓ)
    (σ : WState 3 40) (pre rest : List Bool) (Xm bzM npM zM R7M : ℕ)
    (hst : σ.st sCW = pre ++ enc ε (oracleNodeWord nd) ++ rest) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hTAG : σ.val rTAG = 0) (hIMG : σ.val rIMG = 0) (hIMG2 : σ.val rIMG2 = 0) (hT : σ.val rTN = 0)
    (hTMP : σ.val rTMP = 0) (hT2 : σ.val rT2 = 0) (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0)
    (hW : σ.val rW = 0) (hF1 : σ.val rF1 = 0) (hF2 : σ.val rF2 = 0) (hJ : σ.val rJJ = 0) (hA : σ.val rA = 0)
    (hLC1 : σ.val rLC1 = 0) (hLC2 : σ.val rLC2 = 0) (hLC3 : σ.val rLC3 = 0)
    (hBZ : σ.val rBZ = TCirc.base C z) (hK : σ.val rKK = TCirc.K ℓ) (hTT : σ.val rTT = TCirc.T ℓ)
    (hL : σ.val rL = ℓ) (hZ : σ.val rZ = z) (hNP : σ.val rNP = TCirc.bs C z c)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hG : σ.sh sG = (σ.st sG).length)
    (hAh : σ.sh sARGS = 0) (hCA : σ.val rCA = 0)
    (hfl : FieldsLe Xm nd) (hbz : TCirc.base C z ≤ bzM) (hz : z ≤ zM) (hnp : TCirc.bs C z c ≤ npM)
    (hR7 : σ.val rR7 ≤ R7M) (hcap : NodeCap ℓ Xm bzM npM zM R7M cap) :
    ∃ L1, WXExec cap (nodeBody ε) σ
      (nst σ (pre.length + stp ε * (oracleNodeWord nd).length) (TCirc.bs C z c + TCirc.K ℓ) L1
        ((TCirc.block C z c nd).flatMap PCPPRequestNodeSchema.native))
      (nodeCostB ℓ Xm bzM npM zM) := by
  cases nd with
  | oracle args =>
    have hO : OutOn σ sARGS rCA [] (σ.st sARGS) := ⟨by simp [StablePartition.Workspace.overlay], by simp [hAh],
      by simp [hCA]⟩
    exact ⟨_, nodeOracle_exec ε cap C z c args σ pre rest (σ.st sARGS) Xm bzM npM zM R7M hst hsh hRF hRC hRV hRP hRT
      hTAG hIMG hT hTMP hT2 hX hY hBB hW hF1 hF2 hJ hA hLC1 hLC2 hLC3 hBZ hK hTT hL hNP hwr hG hO hfl hbz hnp hR7 hcap⟩
  | const b =>
    exact ⟨_, nodePlain_exec ε cap C z c _ (by intro a h; cases h) σ pre rest Xm bzM npM zM R7M _ hst hsh hRF hRC hRV
      hRP hRT hTAG hIMG hIMG2 hT hTMP hT2 hX hY hBB hBZ hK hZ hNP hwr hG hfl.1 hfl.2 hbz hz hnp hR7 hcap⟩
  | input i =>
    exact ⟨_, nodePlain_exec ε cap C z c _ (by intro a h; cases h) σ pre rest Xm bzM npM zM R7M _ hst hsh hRF hRC hRV
      hRP hRT hTAG hIMG hIMG2 hT hTMP hT2 hX hY hBB hBZ hK hZ hNP hwr hG hfl.1 hfl.2 hbz hz hnp hR7 hcap⟩
  | not d =>
    exact ⟨_, nodePlain_exec ε cap C z c _ (by intro a h; cases h) σ pre rest Xm bzM npM zM R7M _ hst hsh hRF hRC hRV
      hRP hRT hTAG hIMG hIMG2 hT hTMP hT2 hX hY hBB hBZ hK hZ hNP hwr hG hfl.1 hfl.2 hbz hz hnp hR7 hcap⟩
  | and l r =>
    exact ⟨_, nodePlain_exec ε cap C z c _ (by intro a h; cases h) σ pre rest Xm bzM npM zM R7M _ hst hsh hRF hRC hRV
      hRP hRT hTAG hIMG hIMG2 hT hTMP hT2 hX hY hBB hBZ hK hZ hNP hwr hG hfl.1 hfl.2 hbz hz hnp hR7 hcap⟩
  | or l r =>
    exact ⟨_, nodePlain_exec ε cap C z c _ (by intro a h; cases h) σ pre rest Xm bzM npM zM R7M _ hst hsh hRF hRC hRV
      hRP hRT hTAG hIMG hIMG2 hT hTMP hT2 hX hY hBB hBZ hK hZ hNP hwr hG hfl.1 hfl.2 hbz hz hnp hR7 hcap⟩

end NearCubicGates.Close.ENP.TEmit
