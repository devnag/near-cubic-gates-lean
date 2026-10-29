import Proof.Gates.ENP.TableSpecSeeds

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

/-! ## Bytes and words -/

/-- The bytes of the first `z` seeds. -/
def seedsB {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z : ℕ) : List Bool :=
  (List.range z).flatMap (fun z' => (TCirc.seed C z').flatMap PCPPRequestNodeSchema.native)

/-- The bytes of the first `k` node blocks of seed `z`. -/
def blocksB {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z k : ℕ) : List Bool :=
  (List.range k).flatMap (fun c => (TCirc.block C z c (C.nodes.getD c (.const false))).flatMap
    PCPPRequestNodeSchema.native)

/-- The words of the first `k` nodes. -/
def wordsB {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (k : ℕ) : List Bool := (C.nodes.take k).flatMap oracleNodeWord

theorem seedsB_succ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z : ℕ) :
    seedsB C (z + 1) = seedsB C z ++ (TCirc.seed C z).flatMap PCPPRequestNodeSchema.native := by
  simp [seedsB, List.range_succ, List.flatMap_append]

theorem blocksB_succ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z k : ℕ) (hk : k < C.nodes.length) :
    blocksB C z (k + 1) = blocksB C z k ++ (TCirc.block C z k C.nodes[k]).flatMap PCPPRequestNodeSchema.native := by
  have : C.nodes[k]?.getD (.const false) = C.nodes[k] := by simp [hk]
  simp [blocksB, List.range_succ, List.flatMap_append, this]

theorem wordsB_succ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (k : ℕ) (hk : k < C.nodes.length) :
    wordsB C (k + 1) = wordsB C k ++ oracleNodeWord C.nodes[k] := by
  unfold wordsB
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.flatMap_append]
  simp

theorem words_split {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (k : ℕ) (hk : k < C.nodes.length) :
    C.nodes.flatMap oracleNodeWord =
      wordsB C k ++ (oracleNodeWord C.nodes[k] ++ (C.nodes.drop (k + 1)).flatMap oracleNodeWord) := by
  have h1 : C.nodes = C.nodes.take k ++ C.nodes[k] :: C.nodes.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  calc C.nodes.flatMap oracleNodeWord
      = (C.nodes.take k ++ C.nodes[k] :: C.nodes.drop (k + 1)).flatMap oracleNodeWord := congrArg _ h1
    _ = _ := by rw [List.flatMap_append, List.flatMap_cons]; rfl

theorem tGraph_eq {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : tGraph C = startBytes ℓ ++ seedsB C (TCirc.T ℓ) := by
  simp [tGraph, TCirc.tCircuit, TCirc.nodes, startBytes, seedsB, List.flatMap_append, List.flatMap_assoc]

theorem seed_bytes {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z : ℕ) :
    (TCirc.seed C z).flatMap PCPPRequestNodeSchema.native = blocksB C z C.nodes.length ++
      (PCPPRequestNodeSchema.native (.not (TCirc.img C z C.output.val) : BooleanNode (TCirc.T ℓ)) ++
        PCPPRequestNodeSchema.native (.and (TCirc.base C z - 1) (TCirc.base C z + C.nodes.length * TCirc.K ℓ) :
          BooleanNode (TCirc.T ℓ))) := by
  simp [TCirc.seed, blocksB, List.flatMap_append, List.flatMap_assoc]

theorem word_eq {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) :
    OracleOutput.word ⟨ℓ, C⟩ = natWord ℓ ++ natWord C.nodes.length ++ C.nodes.flatMap oracleNodeWord ++
      natWord C.output.val := rfl

/-! ## States -/

/-- The state at the start of seed `z` (`ARGS` holding `a`). -/
def seedSt {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) (z : ℕ) (a : List Bool) : WState 3 40 :=
  appendO (((((preSeeds C post).sets sARGS a).setv rNP (TCirc.base C z)).setv rZ z).setv rSC (TCirc.T ℓ - z))
    sG rR7 (marks (seedsB C z))

/-- The state in seed `z` after `k` node blocks (`ARGS` holding `b`). -/
def nodeSt {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) (z : ℕ) (a : List Bool) (k : ℕ) (b : List Bool) :
    WState 3 40 :=
  appendO ((((((seedSt C post z a).setv rSC (TCirc.T ℓ - z - 1)).setv rBZ (TCirc.base C z)).seth sCW
    (hdr C + (wordsB C k).length)).sets sARGS b).setv rNP (TCirc.bs C z k)) sG rR7 (marks (blocksB C z k))

/-- The global field bound: node indices and input indices. -/
def xm {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ := C.nodes.length + ℓ

theorem fieldsLe {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (k : ℕ) (hk : k < C.nodes.length) :
    FieldsLe (xm C) C.nodes[k] := by
  have hwf := C.wellFormed ⟨k, hk⟩
  simp only [List.get_eq_getElem] at hwf
  unfold xm
  cases h : C.nodes[k] with
  | const b => rw [h] at hwf; simp [FieldsLe, wf]; cases b <;> simp <;> omega
  | input i => rw [h] at hwf; simp [FieldsLe, wf]; omega
  | not d => rw [h] at hwf; simp [FieldsLe, wf, OracleNode.WellFormedAt] at hwf ⊢; omega
  | and l r => rw [h] at hwf; simp [FieldsLe, wf, OracleNode.WellFormedAt] at hwf ⊢; omega
  | or l r => rw [h] at hwf; simp [FieldsLe, wf, OracleNode.WellFormedAt] at hwf ⊢; omega
  | oracle args => rw [h] at hwf; simp [FieldsLe, OracleNode.WellFormedAt] at hwf ⊢; intro j; have := hwf j; omega

/-! ## Bounds -/

theorem seedsB_le {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z z' : ℕ) (h : z ≤ z') :
    (seedsB C z).length ≤ (seedsB C z').length := by
  induction z' with
  | zero => have : z = 0 := by omega
            subst this; exact le_rfl
  | succ z' ih =>
    by_cases hz : z = z' + 1
    · subst hz; exact le_rfl
    · have := ih (by omega); rw [seedsB_succ, List.length_append]; omega

theorem blocksB_le {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z k : ℕ) (hk : k ≤ C.nodes.length) :
    (blocksB C z k).length ≤ ((TCirc.seed C z).flatMap PCPPRequestNodeSchema.native).length := by
  rw [seed_bytes, List.length_append]
  have : ∀ j, k + j ≤ C.nodes.length → (blocksB C z k).length ≤ (blocksB C z (k + j)).length := by
    intro j; induction j with
    | zero => intro _; exact le_rfl
    | succ j ih => intro hj; have := ih (by omega); rw [← Nat.add_assoc, blocksB_succ C z _ (by omega),
        List.length_append]; omega
  have := this (C.nodes.length - k) (by omega)
  rw [show k + (C.nodes.length - k) = C.nodes.length by omega] at this
  omega

/-- The global maxima at `C`. -/
def bzM {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ := TCirc.base C (TCirc.T ℓ)
/-- The final length of `G`. -/
def r7M {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ := (marks (tGraph C)).length

theorem r7_le {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z k : ℕ) (hz : z < TCirc.T ℓ) (hk : k ≤ C.nodes.length) :
    (marks (startBytes ℓ)).length + (marks (seedsB C z)).length + (marks (blocksB C z k)).length ≤ r7M C := by
  unfold r7M
  simp only [marks_len]
  rw [tGraph_eq, List.length_append]
  have h1 := blocksB_le C z k hk
  have h2 := seedsB_le C (z + 1) (TCirc.T ℓ) hz
  rw [seedsB_succ, List.length_append] at h2
  omega

theorem base_mono {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) {z z' : ℕ} (h : z ≤ z') : TCirc.base C z ≤ TCirc.base C z' := by
  unfold TCirc.base; have := Nat.mul_le_mul_right (TCirc.L C) h; omega

theorem bs_le {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (z k : ℕ) (hz : z < TCirc.T ℓ) (hk : k ≤ C.nodes.length) :
    TCirc.bs C z k ≤ bzM C := by
  unfold bzM TCirc.bs
  have h1 := base_mono C (show z + 1 ≤ TCirc.T ℓ by omega)
  have h2 : TCirc.base C (z + 1) = TCirc.base C z + TCirc.L C := by unfold TCirc.base; ring
  have h3 : k * TCirc.K ℓ ≤ C.nodes.length * TCirc.K ℓ := Nat.mul_le_mul_right _ hk
  unfold TCirc.L at h2
  omega

/-- The capacity a node needs, summed. -/
def nodeCapSum {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ :=
  let Xm := xm C
  let b := bzM C
  (2 * ℓ + 2 ^ (natBitLength Xm + 1) + b + Xm * TCirc.K ℓ + TCirc.K ℓ + ℓ * (b + Xm * TCirc.K ℓ + TCirc.K ℓ) + 10) +
    (2 * TCirc.T ℓ + vbM ℓ Xm b b + 3 * ℓ + ℓ * (b + Xm * TCirc.K ℓ + TCirc.K ℓ) + r7M C +
      2 * (TCirc.T ℓ * (ℓ * (12 * vbM ℓ Xm b b + 18) + (6 * vbM ℓ Xm b b + 9))) +
      14 * ℓ * (6 * vbM ℓ Xm b b + 9) + 300 * (vbM ℓ Xm b b + 10)) +
    (2 * 2 ^ (natBitLength Xm + 1) + b + 2 * (Xm * TCirc.K ℓ) + TCirc.K ℓ + 2 * TCirc.T ℓ + Xm + 24) +
    (r7M C + 18 * TCirc.K ℓ + 20 * (b + Xm * TCirc.K ℓ + TCirc.K ℓ + 5) + 60 + b + TCirc.K ℓ) + 40

theorem nodeCap_of {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) {cap : ℕ} (h : nodeCapSum C ≤ cap) :
    NodeCap ℓ (xm C) (bzM C) (bzM C) (TCirc.T ℓ) (r7M C) cap := by
  unfold nodeCapSum at h
  simp only at h
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ## The nodes loop -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem nst_step {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) (z : ℕ) (a : List Bool) (k : ℕ) (b L1 : List Bool)
    (v1 v2 : ℕ) (hk : k < C.nodes.length) :
    nst (((nodeSt C post z a k b).setv rM v1).setv rLC4 v2)
      (hdr C + (wordsB C k).length + stp false * (oracleNodeWord C.nodes[k]).length) (TCirc.bs C z k + TCirc.K ℓ) L1
      ((TCirc.block C z k C.nodes[k]).flatMap PCPPRequestNodeSchema.native) =
    ((nodeSt C post z a (k + 1) L1).setv rM v1).setv rLC4 v2 := by
  have hb := blocksB_succ C z k hk
  have hw := wordsB_succ C k hk
  have hs : stp false = 1 := rfl
  have hbs : TCirc.bs C z (k + 1) = TCirc.bs C z k + TCirc.K ℓ := by unfold TCirc.bs; ring
  apply WState.eq
  · funext i; fin_cases i <;> simp [nst, nodeSt, hb, hw, hs, Nat.add_assoc]
  · funext i; fin_cases i <;> simp [nst, nodeSt, hb, hw, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
  · funext i; revert i; apply fin40_cases; intro i hi
    interval_cases i <;> simp [nst, nodeSt, hb, hw, hbs, Nat.add_assoc]
  · rfl

/-- The node cost bound of `C`. -/
def nodeCostC {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ := nodeCostB ℓ (xm C) (bzM C) (bzM C) (TCirc.T ℓ)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **The `m` node blocks of seed `z`** (`sec:all-lengths` stage 2). -/
theorem nodesLoop_exec {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) (z : ℕ) (a : List Bool)
    (hz : z < TCirc.T ℓ) (cap : ℕ) (hcap : nodeCapSum C ≤ cap) (hc2 : 2 * C.nodes.length ≤ cap) :
    ∃ b, WXExec cap (repK rM rLC4 (nodeBody false)) (nodeSt C post z a 0 a) (nodeSt C post z a C.nodes.length b)
      (C.nodes.length * (nodeCostC C + 8) + 7 * C.nodes.length + 3) := by
  have hNC := nodeCap_of C hcap
  refine repX (K := rM) (K2 := rLC4) (body := nodeBody false) (by decide) (nodeCostC C) C.nodes.length
    (fun k b => nodeSt C post z a k b) a hc2
    (by intro k b; simp [nodeSt, seedSt, preSeeds, preVal]) (by intro k b; simp [nodeSt, seedSt, preSeeds, preVal])
    ?_ (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
  intro k hk b v1 v2
  have hsplit := words_split C k hk
  set pre := natWord ℓ ++ natWord C.nodes.length ++ wordsB C k with hpre
  set rest := (C.nodes.drop (k + 1)).flatMap oracleNodeWord ++ natWord C.output.val ++ post with hrest
  have hcw : (OracleOutput.word ⟨ℓ, C⟩) ++ post = pre ++ enc false (oracleNodeWord C.nodes[k]) ++ rest := by
    rw [word_eq, hsplit]; simp [pre, rest, WireExponent3_5.PrimAsm.ParseNat.enc]
  have hpl : pre.length = hdr C + (wordsB C k).length := by
    unfold hdr; simp only [pre, List.length_append] <;> omega
  have hR7 := r7_le C z k hz hk.le
  have hbs := bs_le C z k hz hk.le
  have hbz := base_mono C (show z ≤ TCirc.T ℓ by omega)
  obtain ⟨L1, h⟩ := nodeBody_exec false cap C z k C.nodes[k] (((nodeSt C post z a k b).setv rM v1).setv rLC4 v2)
    pre rest (xm C) (bzM C) (bzM C) (TCirc.T ℓ) (r7M C)
    (by simp [nodeSt, seedSt, preSeeds, hcw]) (by simp [nodeSt, seedSt, preSeeds, hpl])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, preVal]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (fun r hr => by fin_cases r <;> simp_all [nodeSt, seedSt, preSeeds, preVal])
    (by simp [nodeSt, seedSt, preSeeds, marks_len, List.length_append]; ring)
    (by simp [nodeSt, seedSt, preSeeds]) (by simp [nodeSt, seedSt, preSeeds, preVal])
    (fieldsLe C k hk) hbz (by omega) hbs
    (by simp [nodeSt, seedSt, preSeeds, preVal]; simp only [marks_len] at hR7; omega) hNC
  refine ⟨L1, WXExec.cast cap h ?_ le_rfl⟩
  rw [hpl]
  exact nst_step C post z a k b L1 v1 v2 hk

/-! ## Closing a seed -/

/-- The cost bound of `closeSeed`. -/
def closeCost (o k bz np V : ℕ) : ℕ := imgCost o k bz + 2 * nodeCost V + 40 * (bz + np + o * k + k + 10)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **Closing seed `z`** (`sec:all-lengths` stage 2): `¬C(z)` (the image of the output node) and the running conjunction. -/
theorem closeSeed_exec {N : ℕ} (cap : ℕ) (σ : WState 3 40) (o k bz np V : ℕ) (pre rest : List Bool)
    (hst : σ.st sCW = pre ++ enc false (natWord o) ++ rest) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG : σ.val rIMG = 0) (hT : σ.val rTN = 0) (hF1 : σ.val rF1 = 0) (hF2 : σ.val rF2 = 0)
    (hBZ : σ.val rBZ = bz) (hK : σ.val rKK = k) (hk : 1 ≤ k) (hNP : σ.val rNP = np)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hG : σ.sh sG = (σ.st sG).length)
    (hV : bz + o * k + k + np + 4 ≤ V)
    (hcap : 2 ^ (natBitLength o + 1) + σ.val rR7 + 40 * V + 60 ≤ cap) :
    WXExec cap (closeSeed false) σ
      (appendO ((σ.seth sCW (pre.length + stp false * (natWord o).length)).setv rNP (np + 2)) sG rR7
        (marks (PCPPRequestNodeSchema.native (.not (bz + o * k + k - 1) : BooleanNode N) ++
          PCPPRequestNodeSchema.native (.and (bz - 1) np : BooleanNode N))))
      (closeCost o k bz np V) := by
  have hxp : o < 2 ^ (natBitLength o) := Nat.lt_pow_succ_log_self (by norm_num) o
  have hp2 : 2 ^ (natBitLength o + 1) = 2 * 2 ^ natBitLength o := by rw [pow_succ]; ring
  have hok : o * k ≤ V := by omega
  -- 1. IMG := img o
  have c1 := imgStep_exec false cap σ o k bz pre rest hst hsh hRF hRC hRV hRP hRT hIMG hT hBZ hK hk (by omega)
  set σ1 := (σ.seth sCW (pre.length + stp false * (natWord o).length)).setv rIMG (bz + o * k + k - 1) with hσ1
  -- 2. not IMG
  have hcl1 : Clean Rw rTN σ1 := clean_of σ1 (fun r hr => by
    have := hwr r hr
    have h1 : r ≠ rIMG := by intro h; subst h; simp at hr
    simp [σ1, Function.update_of_ne h1, this]) (by simp [σ1, hT])
  have hn1 := native_len_le (.not (bz + o * k + k - 1) : BooleanNode N) V
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
  have c2 := nodeW_spec cap sG Rw rTN hTR tNot (by intro i; fin_cases i <;> simp [tNot, FieldOK] <;> decide)
    (.not (bz + o * k + k - 1) : BooleanNode N) σ1
    (by intro i; fin_cases i <;> simp [fieldVal, regSum, tNot, PCPPRequestNodeSchema.fields, σ1])
    (by intro i; fin_cases i <;> simp [tNot]) V
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega) hcl1 (by simp [σ1, hG])
    (by rw [Rw7]; simp [σ1]; omega)
  rw [Rw7] at c2
  set σ2 := appendO σ1 sG rR7 (marks (PCPPRequestNodeSchema.native (.not (bz + o * k + k - 1) : BooleanNode N)))
    with hσ2
  -- 3, 4. NP += 1, clear IMG
  have c3 := WXExec.inc cap rNP σ2 (by simp [σ2, σ1, hNP]; omega)
  set σ3 := σ2.setv rNP (σ2.val rNP + 1) with hσ3
  have c4 := clearReg_exec (cap := cap) rIMG (bz + o * k + k - 1) σ3 (by simp [σ3, σ2, σ1]) (by omega)
  set σ4 := σ3.setv rIMG 0 with hσ4

  have c5 := WXExec.wm (setR_spec cap (D := rF1) (T := rTN) (by decide) [rBZ] 0 σ4 (by simp) (by simp [σ4, σ3, σ2, σ1, hT])
    (by simp [σ4, σ3, σ2, σ1, hF1]) (by simp [σ4, σ3, σ2, σ1, regSum, hBZ]; omega))
  set σ5 := σ4.setv rF1 (regSum σ4 [rBZ] + 0) with hσ5
  have c6 := WXExec.dec cap rF1 σ5 (by simp [σ5, σ4, σ3, σ2, σ1, regSum, hBZ]; omega)
  set σ6 := σ5.setv rF1 (σ5.val rF1 - 1) with hσ6

  have c7 := WXExec.wm (setR_spec cap (D := rF2) (T := rTN) (by decide) [rNP] 0 σ6 (by simp)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hT]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hF2])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, regSum, hNP]; omega))
  set σ7 := σ6.setv rF2 (regSum σ6 [rNP] + 0) with hσ7
  have c8 := WXExec.dec cap rF2 σ7 (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, regSum, hNP]; omega)
  set σ8 := σ7.setv rF2 (σ7.val rF2 - 1) with hσ8

  have hcl8 : Clean Rw rTN σ8 := clean_of σ8 (fun r hr => by
    have := hwr r hr
    have h1 : r ≠ rIMG := by intro h; subst h; simp at hr
    have h2 : r ≠ rF1 := by intro h; subst h; simp at hr
    have h3 : r ≠ rF2 := by intro h; subst h; simp at hr
    have h4 : r ≠ rNP := by intro h; subst h; simp at hr
    have h5 : r ≠ rR7 := by intro h; subst h; simp at hr
    simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5, this])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hT])
  have hn2 := native_len_le (.and (bz - 1) np : BooleanNode N) V
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega)
  have c9 := nodeW_spec cap sG Rw rTN hTR tAnd (by intro i; fin_cases i <;> simp [tAnd, FieldOK] <;> decide)
    (.and (bz - 1) np : BooleanNode N) σ8
    (by intro i; fin_cases i <;> simp [fieldVal, regSum, tAnd, PCPPRequestNodeSchema.fields, σ8, σ7, σ6, σ5, σ4,
      σ3, σ2, σ1, hBZ, hNP])
    (by intro i; fin_cases i <;> simp [tAnd]) V
    (by intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> omega) hcl8
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hG])
    (by rw [Rw7]; simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, marks_len]; omega)
  rw [Rw7] at c9
  set σ9 := appendO σ8 sG rR7 (marks (PCPPRequestNodeSchema.native (.and (bz - 1) np : BooleanNode N))) with hσ9

  have c10 := WXExec.inc cap rNP σ9 (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hNP]; omega)
  set σ10 := σ9.setv rNP (σ9.val rNP + 1) with hσ10
  have c11 := clearReg_exec (cap := cap) rF1 (bz - 1) σ10 (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, regSum, hBZ])
    (by omega)
  set σ11 := σ10.setv rF1 0 with hσ11
  have c12 := clearReg_exec (cap := cap) rF2 np σ11 (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, regSum,
    hNP]) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq c1 (WXExec.seq (WXExec.wm c2) (WXExec.seq c3 (WXExec.seq c4
    (WXExec.seq c5 (WXExec.seq c6 (WXExec.seq c7 (WXExec.seq c8 (WXExec.seq (WXExec.wm c9) (WXExec.seq c10
    (WXExec.seq c11 c12))))))))))) ?_ le_rfl) ?_
  · rw [NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1] <;> omega
    · funext i; fin_cases i <;> simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hIMG, hF1, hF2, hNP] <;> omega
    · rfl
  · unfold closeCost
    simp only [regSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    simp [σ6, σ5, σ4, σ3, σ2, σ1, hBZ, hNP, hIMG, hF1, hF2]
    omega

/-! ## One seed -/

theorem nodeSt_zero {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) (z : ℕ) (a : List Bool) :
    nodeSt C post z a 0 a = ((seedSt C post z a).setv rSC (TCirc.T ℓ - z - 1)).setv rBZ (TCirc.base C z) := by
  apply WState.eq
  · funext i; fin_cases i <;> simp [nodeSt, seedSt, preSeeds, wordsB, blocksB, marks]
  · funext i; fin_cases i <;> simp [nodeSt, seedSt, preSeeds, wordsB, blocksB, marks]
  · funext i; revert i; apply fin40_cases; intro i hi
    interval_cases i <;> simp [nodeSt, seedSt, preSeeds, wordsB, blocksB, marks, preVal]
  · rfl

/-- The close-seed bound `V`. -/
def vC {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ := 2 * bzM C + C.output.val * TCirc.K ℓ + TCirc.K ℓ + 4

/-- The seed cost bound. -/
def seedCostC {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ :=
  (C.nodes.length * (nodeCostC C + 8) + 7 * C.nodes.length + 3) +
    closeCost C.output.val (TCirc.K ℓ) (bzM C) (bzM C) (vC C) + 30 * bzM C + 30 * r7M C +
    (natBitLength ℓ + 2) * (40 * 2 ^ natBitLength ℓ + 40) +
    (natBitLength C.nodes.length + 2) * (40 * 2 ^ natBitLength C.nodes.length + 40) + 3 * ℓ + 3 * C.nodes.length + 60

/-- The capacity the seeds loop needs. -/
def seedCapSum {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ :=
  nodeCapSum C + 2 * C.nodes.length + 2 ^ (natBitLength C.output.val + 1) + 40 * vC C + 3 * r7M C + 2 * bzM C +
    2 ^ (natBitLength ℓ + 1) + 2 ^ (natBitLength C.nodes.length + 1) + TCirc.T ℓ + 100

theorem closeCost_mono {o k bz np V bz' np' : ℕ} (hb : bz ≤ bz') (hn : np ≤ np') :
    closeCost o k bz np V ≤ closeCost o k bz' np' V := by
  unfold closeCost
  have := imgCost_mono (k := k) (le_refl o) hb
  omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **One seed** (`sec:all-lengths` stage 2): the `m` node blocks of seed `z`, its closing nodes, then the word rewound
(by the bytes written, `TBytesSpec`) and its header skipped. -/
theorem seedBody_exec {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) (z : ℕ) (a : List Bool)
    (hz : z < TCirc.T ℓ) (hB : TBytesSpec) (cap : ℕ) (hcap : seedCapSum C ≤ cap) :
    ∃ b, WXExec cap (seedBody false) ((seedSt C post z a).setv rSC (TCirc.T ℓ - z - 1)) (seedSt C post (z + 1) b)
      (seedCostC C) := by
  have hk := K_pos ℓ
  have q1 : 0 < 2 ^ natBitLength C.output.val := Nat.two_pow_pos _
  have q2 : 0 < 2 ^ natBitLength ℓ := Nat.two_pow_pos _
  have q3 : 0 < 2 ^ natBitLength C.nodes.length := Nat.two_pow_pos _
  have q4 : 0 < 2 ^ natBitLength (xm C) := Nat.two_pow_pos _
  have hbz := base_mono C (show z ≤ TCirc.T ℓ by omega)
  have hbzM : TCirc.base C z ≤ bzM C := hbz
  have hR7 := r7_le C z C.nodes.length hz le_rfl
  have hbs := bs_le C z C.nodes.length hz le_rfl
  have hnc : nodeCapSum C ≤ cap := by unfold seedCapSum at hcap; omega
  set S1 := (seedSt C post z a).setv rSC (TCirc.T ℓ - z - 1) with hS1
  -- 1. BZ := base z
  have s1 := copyReg_exec (cap := cap) rNP rBZ rT2 (by decide) (by decide) (by decide) (TCirc.base C z) S1
    (by simp [S1, seedSt, preSeeds, preVal]) (by simp [S1, seedSt, preSeeds, preVal])
    (by simp [S1, seedSt, preSeeds, preVal]; unfold seedCapSum at hcap; omega)
    (by unfold seedCapSum at hcap; omega)
  have e1 : S1.setv rBZ (S1.val rBZ + TCirc.base C z) = nodeSt C post z a 0 a := by
    rw [nodeSt_zero]; simp [S1, seedSt, preSeeds, preVal]
  rw [e1] at s1
  -- 2. the nodes
  obtain ⟨b, s2⟩ := nodesLoop_exec C post z a hz cap hnc (by unfold seedCapSum at hcap; omega)
  set Q := nodeSt C post z a C.nodes.length b with hQ
  -- 3. closing nodes
  have htk : C.nodes.take C.nodes.length = C.nodes := List.take_length
  have hwm : wordsB C C.nodes.length = C.nodes.flatMap oracleNodeWord := by simp [wordsB]
  set pre := natWord ℓ ++ natWord C.nodes.length ++ C.nodes.flatMap oracleNodeWord with hpre
  have hpl : pre.length = hdr C + (wordsB C C.nodes.length).length := by
    rw [hwm]; unfold hdr; simp only [pre, List.length_append] <;> omega
  have hVc : TCirc.base C z + C.output.val * TCirc.K ℓ + TCirc.K ℓ + TCirc.bs C z C.nodes.length + 4 ≤ vC C := by
    unfold vC; omega
  have s3 := closeSeed_exec (N := TCirc.T ℓ) cap Q C.output.val (TCirc.K ℓ) (TCirc.base C z)
    (TCirc.bs C z C.nodes.length) (vC C) pre post
    (by simp [Q, nodeSt, seedSt, preSeeds, word_eq, pre, WireExponent3_5.PrimAsm.ParseNat.enc])
    (by simp [Q, nodeSt, seedSt, preSeeds, hpl])
    (by simp [Q, nodeSt, seedSt, preSeeds, preVal]) (by simp [Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q, nodeSt, seedSt, preSeeds, preVal]) (by simp [Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q, nodeSt, seedSt, preSeeds, preVal]) (by simp [Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q, nodeSt, seedSt, preSeeds, preVal]) (by simp [Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q, nodeSt, seedSt, preSeeds, preVal]) (by simp [Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q, nodeSt, seedSt, preSeeds, preVal]) hk (by simp [Q, nodeSt, seedSt, preSeeds, preVal])
    (fun r hr => by revert hr; fin_cases r <;> simp [Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q, nodeSt, seedSt, preSeeds, marks_len, List.length_append]; ring) hVc
    (by simp [Q, nodeSt, seedSt, preSeeds, preVal]; simp only [marks_len] at hR7; unfold seedCapSum at hcap; omega)
  set Q3 := appendO ((Q.seth sCW (pre.length + stp false * (natWord C.output.val).length)).setv rNP
    (TCirc.bs C z C.nodes.length + 2)) sG rR7
    (marks (PCPPRequestNodeSchema.native (.not (TCirc.base C z + C.output.val * TCirc.K ℓ + TCirc.K ℓ - 1) :
      BooleanNode (TCirc.T ℓ)) ++
      PCPPRequestNodeSchema.native (.and (TCirc.base C z - 1) (TCirc.bs C z C.nodes.length) :
        BooleanNode (TCirc.T ℓ)))) with hQ3
  -- the bytes of seed z
  have hseed : seedsB C (z + 1) = seedsB C z ++ (blocksB C z C.nodes.length ++
      (PCPPRequestNodeSchema.native (.not (TCirc.base C z + C.output.val * TCirc.K ℓ + TCirc.K ℓ - 1) :
        BooleanNode (TCirc.T ℓ)) ++
      PCPPRequestNodeSchema.native (.and (TCirc.base C z - 1) (TCirc.bs C z C.nodes.length) :
        BooleanNode (TCirc.T ℓ)))) := by
    rw [seedsB_succ, seed_bytes]
    have : TCirc.img C z C.output.val = TCirc.base C z + C.output.val * TCirc.K ℓ + TCirc.K ℓ - 1 := by
      unfold TCirc.img; omega
    rw [this]
  -- 4, 5. Z += 1, clear BZ
  have s4 := WXExec.inc cap rZ Q3 (by simp [Q3, Q, nodeSt, seedSt, preSeeds, preVal]; unfold seedCapSum at hcap; omega)
  set Q4 := Q3.setv rZ (Q3.val rZ + 1) with hQ4
  have s5 := clearReg_exec (cap := cap) rBZ (TCirc.base C z) Q4 (by simp [Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by unfold seedCapSum at hcap; omega)
  set Q5 := Q4.setv rBZ 0 with hQ5

  have hR7v : Q5.val rR7 = (marks (startBytes ℓ)).length + (marks (seedsB C (z + 1))).length := by
    simp [Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal, hseed, marks_len, List.length_append]; ring
  have hR7c : Q5.val rR7 ≤ r7M C := by
    rw [hR7v]
    have := seedsB_le C (z + 1) (TCirc.T ℓ) hz
    unfold r7M; simp only [marks_len]; rw [tGraph_eq, List.length_append]; omega
  have hQ5T : Q5.val rTMP = 0 := by simp [Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal]
  have s6 := copyReg_exec (cap := cap) rR7 rTMP rT2 (by decide) (by decide) (by decide) (Q5.val rR7) Q5 rfl
    (by simp [Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by rw [hQ5T]; unfold seedCapSum at hcap; omega)
    (by unfold seedCapSum at hcap; omega)
  set Q6 := Q5.setv rTMP (Q5.val rTMP + Q5.val rR7) with hQ6
  have hQ6T : Q6.val rTMP = Q5.val rR7 := by simp [Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal]
  have s7 := WXExec.wm (wrewind_spec (cap := cap) sCW rTMP (Q5.val rR7) Q6 hQ6T
    (by rw [hQ6T]; unfold seedCapSum at hcap; omega))
  set Q7 := (Q6.setv rTMP 0).seth sCW (Q6.sh sCW - Q5.val rR7) with hQ7
  have hhead : Q6.sh sCW ≤ Q5.val rR7 := by
    have hw := hB C
    have h1a : Q6.sh sCW = pre.length + (natWord C.output.val).length := by simp [Q6, Q5, Q4, Q3, stp]
    have h1b : (OracleOutput.word ⟨ℓ, C⟩).length = pre.length + (natWord C.output.val).length := by
      rw [word_eq]; simp only [pre, List.length_append]
    have h1 : Q6.sh sCW = (OracleOutput.word ⟨ℓ, C⟩).length := by rw [h1a, h1b]
    rw [h1, hR7v]
    have h2 := seedsB_le C 1 (z + 1) (by omega)
    have h3 : seedsB C 1 = (TCirc.seed C 0).flatMap PCPPRequestNodeSchema.native := by simp [seedsB]
    rw [h3] at h2
    simp only [marks_len]
    unfold startBytes at *
    omega
  -- 8. skip the header
  have hW : Q7.st sCW = [] ++ enc false (natWord ℓ) ++ (natWord C.nodes.length ++
      (C.nodes.flatMap oracleNodeWord ++ natWord C.output.val ++ post)) := by
    simp [Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, word_eq, WireExponent3_5.PrimAsm.ParseNat.enc]
  have r1 := WXExec.wm (readNatM_spec (cap := cap) false sCW rRF rRC rRV rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ℓ [] _ Q7 hW
    (by simp [Q7]; omega) (by simp [Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal]; unfold seedCapSum at hcap; omega))
  set Q8 := (Q7.seth sCW ([].length + stp false * (natWord ℓ).length)).setv rRV (Q7.val rRV + ℓ) with hQ8
  have r2 := clearReg_exec (cap := cap) rRV ℓ Q8 (by simp [Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by unfold seedCapSum at hcap; have : ℓ < 2 ^ (natBitLength ℓ + 1) := by
          have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ℓ
          unfold natBitLength; omega
        omega)
  set Q9 := Q8.setv rRV 0 with hQ9
  have hW9 : Q9.st sCW = enc false (natWord ℓ) ++ enc false (natWord C.nodes.length) ++
      (C.nodes.flatMap oracleNodeWord ++ natWord C.output.val ++ post) := by
    simp [Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, word_eq, WireExponent3_5.PrimAsm.ParseNat.enc]
  have r3 := WXExec.wm (readNatM_spec (cap := cap) false sCW rRF rRC rRV rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C.nodes.length
    (enc false (natWord ℓ)) _ Q9 hW9
    (by simp [Q9, Q8, WireExponent3_5.PrimAsm.ParseNat.enc, stp])
    (by simp [Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal])
    (by simp [Q9]; unfold seedCapSum at hcap; omega))
  set Q10 := (Q9.seth sCW ((enc false (natWord ℓ)).length + stp false * (natWord C.nodes.length).length)).setv rRV
    (Q9.val rRV + C.nodes.length) with hQ10
  have r4 := clearReg_exec (cap := cap) rRV C.nodes.length Q10 (by simp [Q10, Q9])
    (by unfold seedCapSum at hcap; omega)
  refine ⟨b, WXExec.mono (WXExec.cast cap (WXExec.seq s1 (WXExec.seq s2 (WXExec.seq s3 (WXExec.seq s4 (WXExec.seq s5
    (WXExec.seq s6 (WXExec.seq s7 (WXExec.seq r1 (WXExec.seq r2 (WXExec.seq r3 r4)))))))))) ?_ le_rfl) ?_⟩
  · have hbase : TCirc.bs C z C.nodes.length + 2 = TCirc.base C (z + 1) := by
      unfold TCirc.bs TCirc.base TCirc.L; ring
    apply WState.eq
    · funext i; fin_cases i <;> simp [Q10, Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, hdr,
        WireExponent3_5.PrimAsm.ParseNat.enc, stp, hseed, marks_len, List.length_append] <;> omega
    · funext i; fin_cases i <;> simp [Q10, Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, hseed,
        NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [Q10, Q9, Q8, Q7, Q6, Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal, hseed, hbase,
        marks_len, List.length_append] <;> omega
    · rfl
  · unfold seedCostC
    have hcm := closeCost_mono (o := C.output.val) (k := TCirc.K ℓ) (V := vC C) hbzM (bs_le C z C.nodes.length hz le_rfl)
    simp [Q5, Q4, Q3, Q, nodeSt, seedSt, preSeeds, preVal] at hR7c ⊢
    omega

/-! ## The seeds loop -/

theorem seedSt_zero {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) : seedSt C post 0 [] = preSeeds C post := by
  apply WState.eq
  · funext i; fin_cases i <;> simp [seedSt, preSeeds, seedsB, marks]
  · funext i; fin_cases i <;> simp [seedSt, preSeeds, seedsB, marks]
  · funext i; revert i; apply fin40_cases; intro i hi
    interval_cases i <;> simp [seedSt, preSeeds, seedsB, marks, preVal, TCirc.base]
  · rfl

theorem seedSt_last {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post a : List Bool) :
    seedSt C post (TCirc.T ℓ) a = postSeeds C post a := by
  have hn : (TCirc.tCircuit C).nodes.length = TCirc.base C (TCirc.T ℓ) := TCirc.nodes_length C
  apply WState.eq
  · funext i; fin_cases i <;> simp [seedSt, preSeeds, postSeeds, tGraph_eq, marks_len, List.length_append] <;> ring
  · funext i; fin_cases i <;> simp [seedSt, preSeeds, postSeeds, tGraph_eq,
      NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
  · funext i; revert i; apply fin40_cases; intro i hi
    interval_cases i <;> simp [seedSt, preSeeds, postSeeds, preVal, postVal, hn, tGraph_eq, marks_len,
      List.length_append] <;> ring
  · rfl

set_option maxHeartbeats 4000000 in
/-- **All `2^ℓ` seeds** (`sec:all-lengths` stage 2): from `preSeeds` to `postSeeds`. -/
theorem seedsLoop_exec {ℓ : ℕ} (hB : TBytesSpec) (C : OracleCircuit ℓ ℓ) (post : List Bool) (cap : ℕ)
    (hcap : seedCapSum C ≤ cap) :
    ∃ junk, WXExec cap (seedsLoop false) (preSeeds C post) (postSeeds C post junk)
      (TCirc.T ℓ * (seedCostC C + 4) + 1) := by
  have q1 : 0 < 2 ^ natBitLength C.output.val := Nat.two_pow_pos _
  have q2 : 0 < 2 ^ natBitLength ℓ := Nat.two_pow_pos _
  have q3 : 0 < 2 ^ natBitLength C.nodes.length := Nat.two_pow_pos _
  have hTc : TCirc.T ℓ ≤ cap := by unfold seedCapSum at hcap; omega
  have key := Runs.whr (cap := cap) (r := rSC) (P := .seq (WMX.dec rSC) (seedBody false))
    (fun k τ => k ≤ TCirc.T ℓ ∧ ∃ a, τ = seedSt C post (TCirc.T ℓ - k) a) (seedCostC C + 2)
    (fun τ => ∃ junk, τ = postSeeds C post junk)
    (by
      rintro τ ⟨-, a, rfl⟩
      refine ⟨by simp [seedSt, preSeeds, preVal], a, ?_⟩
      rw [Nat.sub_zero, seedSt_last])
    (by
      rintro k τ ⟨hk, a, rfl⟩
      refine ⟨by simp [seedSt, preSeeds, preVal]; omega, ?_⟩
      have hd := WXExec.dec cap rSC (seedSt C post (TCirc.T ℓ - (k + 1)) a)
        (by simp [seedSt, preSeeds, preVal]; omega)
      have e : (seedSt C post (TCirc.T ℓ - (k + 1)) a).setv rSC
          ((seedSt C post (TCirc.T ℓ - (k + 1)) a).val rSC - 1) =
          (seedSt C post (TCirc.T ℓ - (k + 1)) a).setv rSC (TCirc.T ℓ - (TCirc.T ℓ - (k + 1)) - 1) := by
        congr 1 <;> (simp [seedSt, preSeeds, preVal] <;> omega)
      rw [e] at hd
      obtain ⟨b, hs⟩ := seedBody_exec C post (TCirc.T ℓ - (k + 1)) a (by omega) hB cap hcap
      refine ⟨_, WXExec.mono (WXExec.seq hd hs) (by omega), by omega, b, ?_⟩
      congr 1 <;> omega)
    (TCirc.T ℓ) (preSeeds C post) ⟨le_rfl, [], by rw [Nat.sub_self, seedSt_zero]⟩
  obtain ⟨τ, h, junk, rfl⟩ := key
  exact ⟨junk, WXExec.mono h (by ring_nf; omega)⟩

end NearCubicGates.Close.ENP.TEmit
