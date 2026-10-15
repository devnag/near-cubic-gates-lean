import Proof.Gates.ENP.TableGroup

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
local notation "rKK" => (12 : Fin 40)
local notation "rBZ" => (14 : Fin 40)
local notation "rA" => (16 : Fin 40)
local notation "rNP" => (22 : Fin 40)
local notation "rCA" => (25 : Fin 40)
local notation "rRF" => (27 : Fin 40)
local notation "rRC" => (28 : Fin 40)
local notation "rRV" => (29 : Fin 40)
local notation "rRP" => (30 : Fin 40)
local notation "rRT" => (31 : Fin 40)
local notation "rIMG" => (34 : Fin 40)
local notation "rLC2" => (35 : Fin 40)
local notation "rLC3" => (36 : Fin 40)
local notation "rJJ" => (17 : Fin 40)
local notation "rX" => (18 : Fin 40)
local notation "rY" => (19 : Fin 40)
local notation "rBB" => (20 : Fin 40)
local notation "rW" => (21 : Fin 40)
local notation "rF1" => (23 : Fin 40)
local notation "rF2" => (24 : Fin 40)
local notation "rLC1" => (33 : Fin 40)
local notation "rT2" => (38 : Fin 40)
local notation "rTMP" => (39 : Fin 40)

/-- `IMG += RV·K` (consuming `RV`). -/
def mulLoop : WMX 3 40 := .whr rRV (.seq (WMX.dec rRV) (.wm (addW rKK rIMG rTN)))

theorem mulLoop_exec (cap : ℕ) : ∀ (n : ℕ) (σ : WState 3 40) (k i : ℕ), σ.val rRV = n → σ.val rKK = k →
    σ.val rIMG = i → σ.val rTN = 0 → i + n * k ≤ cap → n ≤ cap →
    WXExec cap mulLoop σ ((σ.setv rRV 0).setv rIMG (i + n * k)) (n * (18 * k + 7) + 1)
  | 0, σ, k, i, hn, hk, hi, _, _, _ => by
    have e : (σ.setv rRV 0).setv rIMG (i + 0 * k) = σ := by
      rw [Nat.zero_mul, Nat.add_zero, ← hi, ← hn, wsetv_same, wsetv_same]
    rw [e]
    exact WXExec.mono (WXExec.whrF hn) (by omega)
  | n + 1, σ, k, i, hn, hk, hi, hT, hc, hnc => by
    have h1 := WXExec.dec cap rRV σ (by omega)
    have h2 := addW_spec (cap := cap) (A := rKK) (W := rIMG) (T := rTN) (by decide) (by decide) (by decide)
      (σ.setv rRV (σ.val rRV - 1)) (by simp [hT]) (by simp [hk, hi]; nlinarith)
    have ih := mulLoop_exec cap n ((σ.setv rRV (σ.val rRV - 1)).setv rIMG
      ((σ.setv rRV (σ.val rRV - 1)).val rIMG + (σ.setv rRV (σ.val rRV - 1)).val rKK)) k (i + k)
      (by simp [hn]) (by simp [hk]) (by simp [hi, hk]) (by simp [hT]) (by nlinarith) (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 (WXExec.wm h2)) ih) ?_ le_rfl) ?_
    · apply WState.eq <;> try rfl
      funext r
      simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all <;> ring
    · simp only [WState.setv_val, Function.update_apply]
      simp [hk, Nat.succ_mul]
      omega

/-- Write `IMG` ones (consuming `IMG`) to `ARGS`. -/
def onesLoop : WMX 3 40 := .whr rIMG (.seq (WMX.dec rIMG) (emitO sARGS rCA true))

theorem onesLoop_exec (cap : ℕ) : ∀ (n : ℕ) (σ : WState 3 40) (out L0 : List Bool), σ.val rIMG = n →
    OutOn σ sARGS rCA out L0 → out.length + n < cap → n ≤ cap →
    WXExec cap onesLoop σ ((outSt σ sARGS rCA (out ++ List.replicate n true) L0).setv rIMG 0) (n * 12 + 1)
  | 0, σ, out, L0, hn, hO, _, _ => by
    have e : (outSt σ sARGS rCA (out ++ List.replicate 0 true) L0).setv rIMG 0 = σ := by
      simp only [List.replicate_zero, List.append_nil]
      rw [outSt_self σ hO, ← hn, wsetv_same]
    rw [e]
    exact WXExec.mono (WXExec.whrF hn) (by omega)
  | n + 1, σ, out, L0, hn, hO, hc, hnc => by
    have h1 := WXExec.dec cap rIMG σ (by omega)
    have hO1 : OutOn (σ.setv rIMG (σ.val rIMG - 1)) sARGS rCA out L0 := outOn_setv hO rIMG (by decide) _
    have h2 := emitO_spec cap (σ.setv rIMG (σ.val rIMG - 1)) out L0 true hO1 (by omega)
    have ih := onesLoop_exec cap n (outSt (σ.setv rIMG (σ.val rIMG - 1)) sARGS rCA (out ++ [true]) L0)
      (out ++ [true]) L0 (by simp [outSt, hn]) (outOn_outSt _ _ _ _ _) (by simp; omega) (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq h1 h2) ih) ?_ le_rfl) (by omega)
    rw [outSt_outSt]
    have hrep : out ++ [true] ++ List.replicate n true = out ++ List.replicate (n + 1) true := by
      simp [List.replicate_succ]
    rw [hrep]
    apply WState.eq
    · funext i; simp only [outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    · funext i; simp only [outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    · funext i; simp only [outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · rfl

/-- Read one argument, write its image in unary to `ARGS`. -/
def argBody (ε : Bool) : WMX 3 40 :=
  .seq (.wm (readNatM ε sCW rRF rRC rRV rRP rRT)) <|
  .seq (.wm (setR rIMG rTN [rBZ, rKK] 0)) <| .seq (WMX.dec rIMG) <|
  .seq mulLoop <| .seq onesLoop (emitO sARGS rCA false)

/-- The cost bound of one argument. -/
def argCost (x k bz : ℕ) : ℕ :=
  (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) + 40 * (bz + k + 3) + x * (18 * k + 7) +
    (bz + x * k + k) * 12 + 30

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One argument** (paper §11.6 stage 2): reads `args j = x`, writes `w = BZ + x·K + K − 1` in unary. -/
theorem argBody_exec (ε : Bool) (cap : ℕ) (σ : WState 3 40) (x k bz : ℕ) (pre rest out L0 : List Bool)
    (hst : σ.st sCW = pre ++ enc ε (natWord x) ++ rest) (hsh : σ.sh sCW = pre.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG : σ.val rIMG = 0) (hT : σ.val rTN = 0) (hBZ : σ.val rBZ = bz) (hK : σ.val rKK = k) (hk : 1 ≤ k)
    (hO : OutOn σ sARGS rCA out L0)
    (hcap : 2 ^ (natBitLength x + 1) + bz + x * k + k + out.length + 10 ≤ cap) :
    WXExec cap (argBody ε) σ
      (outSt (σ.seth sCW (pre.length + stp ε * (natWord x).length)) sARGS rCA
        (out ++ (List.replicate (bz + x * k + k - 1) true ++ [false])) L0) (argCost x k bz) := by
  have hxp : x < 2 ^ (natBitLength x) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hp2 : 2 ^ (natBitLength x + 1) = 2 * 2 ^ natBitLength x := by rw [pow_succ]; ring
  -- 1. RV := x
  have h1 := WXExec.wm (readNatM_spec (cap := cap) ε sCW rRF rRC rRV rRP rRT (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x pre rest σ hst hsh hRF hRC hRP
    hRT (by rw [hRV]; omega))
  set σ1 := (σ.seth sCW (pre.length + stp ε * (natWord x).length)).setv rRV (σ.val rRV + x) with hσ1
  -- 2, 3. IMG := bz + k − 1
  have h2 := WXExec.wm (setR_spec cap (D := rIMG) (T := rTN) (by decide) [rBZ, rKK] 0 σ1 (by simp) (by simp [σ1, hT])
    (by simp [σ1, hIMG] <;> omega) (by simp [σ1, regSum, hBZ, hK] <;> omega))
  set σ2 := σ1.setv rIMG (regSum σ1 [rBZ, rKK] + 0) with hσ2
  have h3 := WXExec.dec cap rIMG σ2 (by simp [σ2, σ1, regSum, hBZ, hK] <;> omega)
  set σ3 := σ2.setv rIMG (σ2.val rIMG - 1) with hσ3
  -- 4. IMG += x·k
  have h4 := mulLoop_exec cap x σ3 k (bz + k - 1) (by simp [σ3, σ2, σ1, hRV]) (by simp [σ3, σ2, σ1, hK])
    (by simp [σ3, σ2, σ1, regSum, hBZ, hK]) (by simp [σ3, σ2, σ1, hT]) (by omega) (by omega)
  set σ4 := (σ3.setv rRV 0).setv rIMG (bz + k - 1 + x * k) with hσ4
  -- 5. the ones
  have hO4 : OutOn σ4 sARGS rCA out L0 :=
    ⟨by simp [σ4, σ3, σ2, σ1, hO.1], by simp [σ4, σ3, σ2, σ1, hO.2.1], by simp [σ4, σ3, σ2, σ1, hO.2.2]⟩
  have h5 := onesLoop_exec cap (bz + k - 1 + x * k) σ4 out L0 (by simp [σ4]) hO4 (by omega) (by omega)
  set σ5 := (outSt σ4 sARGS rCA (out ++ List.replicate (bz + k - 1 + x * k) true) L0).setv rIMG 0 with hσ5
  -- 6. the separator
  have hO5 : OutOn σ5 sARGS rCA (out ++ List.replicate (bz + k - 1 + x * k) true) L0 :=
    outOn_setv (outOn_outSt _ _ _ _ _) rIMG (by decide) 0
  have h6 := emitO_spec cap σ5 _ L0 false hO5 (by simp; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 (WXExec.seq h5
    h6))))) ?_ le_rfl) ?_
  · have he : bz + k - 1 + x * k = bz + x * k + k - 1 := by omega
    rw [he]
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ5, σ4, σ3, σ2, σ1, outSt]
    · funext i; fin_cases i <;> simp [σ5, σ4, σ3, σ2, σ1, outSt]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ5, σ4, σ3, σ2, σ1, outSt, hRV, hIMG]
    · rfl
  · unfold argCost
    simp only [regSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    have e1 : σ1.val rBZ = bz := by simp [σ1, hBZ]
    have e2 : σ1.val rKK = k := by simp [σ1, hK]
    have e3 : σ1.val rIMG = 0 := by simp [σ1, hIMG]
    rw [e1, e2, e3]
    omega

theorem enc_append (ε : Bool) (u v : List Bool) : enc ε (u ++ v) = enc ε u ++ enc ε v := by
  cases ε <;> simp [WireExponent3_5.PrimAsm.ParseNat.enc, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]

theorem nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength; have := Nat.log_mono_right (b := 2) h; omega

theorem argCost_mono {x x' k bz : ℕ} (h : x ≤ x') : argCost x k bz ≤ argCost x' k bz := by
  unfold argCost
  have h1 := nbl_mono h
  have h2 : 2 ^ natBitLength x ≤ 2 ^ natBitLength x' := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤
      (natBitLength x' + 2) * (40 * 2 ^ natBitLength x' + 40) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : x * (18 * k + 7) ≤ x' * (18 * k + 7) := Nat.mul_le_mul_right _ h
  have h5 : x * k ≤ x' * k := Nat.mul_le_mul_right _ h
  generalize (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) = A at *
  generalize (natBitLength x' + 2) * (40 * 2 ^ natBitLength x' + 40) = A' at *
  generalize x * (18 * k + 7) = B at *
  generalize x' * (18 * k + 7) = B' at *
  generalize x * k = D at *
  generalize x' * k = D' at *
  omega

theorem argsStream_snoc (ws : List ℕ) (w : ℕ) :
    argsStream (ws ++ [w]) = argsStream ws ++ (List.replicate w true ++ [false]) := by
  simp [argsStream, List.flatMap_append]

theorem argsStream_length_le (ws : List ℕ) (B : ℕ) (h : ∀ w ∈ ws, w + 1 ≤ B) :
    (argsStream ws).length ≤ ws.length * B := by
  induction ws with
  | nil => simp [argsStream]
  | cons w ws ih =>
    have h1 := h w (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    have e : argsStream (w :: ws) = (List.replicate w true ++ [false]) ++ argsStream ws := by simp [argsStream]
    rw [e]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    have : (ws.length + 1) * B = ws.length * B + B := by ring
    omega

/-- The state after `k` arguments: the word head past them, their images on `ARGS`. -/
def ast (ε : Bool) (σ : WState 3 40) (p0 : ℕ) (xs : List ℕ) (im : ℕ → ℕ) (L0 : List Bool) (k : ℕ) :
    WState 3 40 :=
  outSt (σ.seth sCW (p0 + stp ε * ((xs.take k).flatMap natWord).length)) sARGS rCA
    (argsStream ((xs.map im).take k)) L0

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The arguments of an oracle gate** (paper §11.6 stage 2): reads all `ℓ` arguments and writes their images. -/
theorem argsLoop_exec (ε : Bool) (cap : ℕ) (σ : WState 3 40) (xs : List ℕ) (kk bz Xm : ℕ) (P0 rest L0 : List Bool)
    (hst : σ.st sCW = P0 ++ enc ε (xs.flatMap natWord) ++ rest) (hsh : σ.sh sCW = P0.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG : σ.val rIMG = 0) (hT : σ.val rTN = 0) (hBZ : σ.val rBZ = bz) (hK : σ.val rKK = kk) (hk : 1 ≤ kk)
    (hL : σ.val rL = xs.length) (hLC2 : σ.val rLC2 = 0)
    (hO : OutOn σ sARGS rCA [] L0) (hXm : ∀ x ∈ xs, x ≤ Xm)
    (hcap : 2 * xs.length + 2 ^ (natBitLength Xm + 1) + bz + Xm * kk + kk + xs.length * (bz + Xm * kk + kk) + 10 ≤
      cap) :
    WXExec cap (repK rL rLC2 (argBody ε)) σ (ast ε σ P0.length xs (fun x => bz + x * kk + kk - 1) L0 xs.length)
      (xs.length * (argCost Xm kk bz + 8) + 7 * xs.length + 3) := by
  set im : ℕ → ℕ := fun x => bz + x * kk + kk - 1 with him
  have h0 : ast ε σ P0.length xs im L0 0 = σ := by
    obtain ⟨o1, o2, o3⟩ := hO
    apply WState.eq
    · funext i; fin_cases i <;> simp [ast, outSt, hsh, o2, argsStream]
    · funext i; fin_cases i <;> simp [ast, outSt, o1, StablePartition.Workspace.overlay, argsStream]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [ast, outSt, o3, argsStream]
    · rfl
  have hrep := Runs.repE (cap := cap) (K := rL) (K2 := rLC2) (body := argBody ε) (by decide) (argCost Xm kk bz)
    xs.length (ast ε σ P0.length xs im L0) (by have := hcap; generalize 2 ^ (natBitLength Xm + 1) = P at this; omega)
    (by intro k; simp [ast, outSt]) (by intro k; simp [ast, outSt]) ?_ (by rw [h0]; exact hL) (by rw [h0]; exact hLC2)
  · rw [h0] at hrep; exact hrep
  intro k hkx v1 v2
  have hkl : k < xs.length := hkx
  set x := xs[k] with hx
  have hxm : x ≤ Xm := hXm _ (List.getElem_mem hkl)
  have htk : xs.take (k + 1) = xs.take k ++ [x] := by rw [List.take_add_one, List.getElem?_eq_getElem hkl]; rfl
  have hsplit : xs = xs.take k ++ [x] ++ xs.drop (k + 1) := by
    rw [← htk, List.take_append_drop]
  set pre := P0 ++ enc ε ((xs.take k).flatMap natWord) with hpre
  set rst := enc ε ((xs.drop (k + 1)).flatMap natWord) ++ rest with hrst
  set out := argsStream ((xs.map im).take k) with hout
  have hcw : σ.st sCW = pre ++ enc ε (natWord x) ++ rst := by
    rw [hst]
    conv_lhs => rw [hsplit]
    simp only [List.flatMap_append, enc_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, pre, rst]
    simp only [List.append_assoc]
  have hprelen : pre.length = P0.length + stp ε * ((xs.take k).flatMap natWord).length := by
    simp [pre, enc_length]
  have houtlen : out.length ≤ xs.length * (bz + Xm * kk + kk) := by
    have h1 : out.length ≤ ((xs.map im).take k).length * (bz + Xm * kk + kk) :=
      argsStream_length_le ((xs.map im).take k) (bz + Xm * kk + kk) (by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hw)
      have hym : y ≤ Xm := hXm y hy
      have : y * kk ≤ Xm * kk := Nat.mul_le_mul_right _ hym
      simp only [im]; omega)
    have hl : ((xs.map im).take k).length ≤ xs.length := by simp
    have := Nat.mul_le_mul_right (bz + Xm * kk + kk) hl
    omega
  have hxk : x * kk ≤ Xm * kk := Nat.mul_le_mul_right _ hxm
  have hp : 2 ^ (natBitLength x + 1) ≤ 2 ^ (natBitLength Xm + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := nbl_mono hxm; omega)
  have hab := argBody_exec ε cap (((ast ε σ P0.length xs im L0 k).setv rL v1).setv rLC2 v2) x kk bz pre rst out L0
    (by simp [ast, outSt, hcw]) (by simp [ast, outSt, hprelen])
    (by simp [ast, outSt, hRF]) (by simp [ast, outSt, hRC]) (by simp [ast, outSt, hRV]) (by simp [ast, outSt, hRP])
    (by simp [ast, outSt, hRT]) (by simp [ast, outSt, hIMG]) (by simp [ast, outSt, hT]) (by simp [ast, outSt, hBZ])
    (by simp [ast, outSt, hK]) hk
    (outOn_setv (outOn_setv (outOn_outSt _ _ _ _ _) rL (by decide) v1) rLC2 (by decide) v2)
    (by omega)
  refine WXExec.mono (WXExec.cast cap hab ?_ le_rfl) (argCost_mono hxm)
  have hsa : argsStream ((xs.map im).take (k + 1)) = out ++ (List.replicate (bz + x * kk + kk - 1) true ++ [false]) := by
    rw [← List.map_take, htk, List.map_append, List.map_singleton, argsStream_snoc, List.map_take]
  have hfl : ((xs.take (k + 1)).flatMap natWord).length = ((xs.take k).flatMap natWord).length + (natWord x).length := by
    rw [htk, List.flatMap_append, List.length_append]; simp
  apply WState.eq
  · funext i; fin_cases i <;> simp [ast, outSt, hsa, hfl, hprelen, Nat.mul_add, Nat.add_assoc]
  · funext i; fin_cases i <;> simp [ast, outSt, hsa]
  · funext i; revert i; apply fin40_cases; intro i hi
    interval_cases i <;> simp [ast, outSt, hsa]
  · rfl

/-! ## The groups of an oracle block -/

theorem groupCost_mono {ℓ a gs Wm P a' gs' : ℕ} (ha : a ≤ a') (hg : gs ≤ gs') :
    groupCost ℓ a gs Wm P ≤ groupCost ℓ a' gs' Wm P := by
  unfold groupCost
  have h1 := pairCost_mono (u := a) (w := Wm) (V := gs + 2 * ℓ + Wm + a + 4) (u' := a') (w' := Wm)
    (V' := gs' + 2 * ℓ + Wm + a' + 4) ha le_rfl (by omega)
  have h2 := nodeCost_mono (V := gs + 2 * ℓ + Wm + a + 4) (V' := gs' + 2 * ℓ + Wm + a' + 4) (by omega)
  have h3 := Nat.mul_le_mul_left ℓ (Nat.add_le_add_right h1 8)
  omega

theorem groupBytes_length_le {ℓ : ℕ} (a gs Vb : ℕ) (ws : List ℕ) (hws : ws.length = ℓ)
    (hw : ∀ w ∈ ws, w + 4 ≤ Vb) (hg : gs + 2 * ℓ + a + 4 ≤ Vb) :
    (groupBytes (ℓ := ℓ) a gs ws).length ≤ ℓ * (12 * Vb + 18) + (6 * Vb + 9) := by
  unfold groupBytes
  rw [List.length_append]
  have h1 := pairsBytes_length_le (ℓ := ℓ) a gs Vb ws ℓ (fun j hj => by
    refine ⟨?_, by omega, by omega⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hw _ (List.getElem_mem _))
  have h2 := native_len_le (.or (if a = 0 then 0 else gs - 1) (if ℓ = 0 then 1 + a else gs + 2 * ℓ - 1) :
    BooleanNode (TCirc.T ℓ)) Vb (by
      intro i; fin_cases i <;> simp [PCPPRequestNodeSchema.fields] <;> (try split) <;> omega)
  omega

/-- The bytes of the first `k` groups. -/
def grpBytes {ℓ : ℕ} (np0 : ℕ) (ws : List ℕ) (k : ℕ) : List Bool :=
  (List.range k).flatMap (fun a => groupBytes (ℓ := ℓ) a (np0 + a * (2 * ℓ + 1)) ws)

theorem grpBytes_succ {ℓ : ℕ} (np0 : ℕ) (ws : List ℕ) (k : ℕ) :
    grpBytes (ℓ := ℓ) np0 ws (k + 1) = grpBytes (ℓ := ℓ) np0 ws k ++ groupBytes (ℓ := ℓ) k (np0 + k * (2 * ℓ + 1)) ws := by
  simp [grpBytes, List.range_succ, List.flatMap_append]

theorem grpBytes_length_le {ℓ : ℕ} (np0 Vb : ℕ) (ws : List ℕ) (hws : ws.length = ℓ) (hw : ∀ w ∈ ws, w + 4 ≤ Vb)
    (n : ℕ) (hn : np0 + n * (2 * ℓ + 1) + n + 3 ≤ Vb) :
    ∀ k ≤ n, (grpBytes (ℓ := ℓ) np0 ws k).length ≤ k * (ℓ * (12 * Vb + 18) + (6 * Vb + 9)) := by
  intro k
  induction k with
  | zero => intro _; simp [grpBytes]
  | succ k ih =>
    intro hk
    rw [grpBytes_succ, List.length_append, Nat.add_mul, Nat.one_mul]
    have h1 := ih (by omega)
    have hkn : (k + 1) * (2 * ℓ + 1) ≤ n * (2 * ℓ + 1) := Nat.mul_le_mul_right _ hk
    have h2 := groupBytes_length_le (ℓ := ℓ) k (np0 + k * (2 * ℓ + 1)) Vb ws hws hw (by
      have : (k + 1) * (2 * ℓ + 1) = k * (2 * ℓ + 1) + (2 * ℓ + 1) := by ring
      omega)
    omega

/-- The state after `k` groups. -/
def gst {ℓ : ℕ} (σ : WState 3 40) (np0 : ℕ) (ws : List ℕ) (k : ℕ) : WState 3 40 :=
  appendO ((σ.setv rA k).setv rNP (np0 + k * (2 * ℓ + 1))) sG rR7 (marks (grpBytes (ℓ := ℓ) np0 ws k))

/-- The cost of the `T` groups. -/
def groupsCost (ℓ T np0 Wm P : ℕ) : ℕ := T * (groupCost ℓ T (np0 + T * (2 * ℓ + 1)) Wm P + 8) + 7 * T + 3

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The `T` groups of a multiplexer** (paper §11.6 stage 2: "each oracle gate becomes a selector over the
`2^{ℓ_out}` oracle variables"). -/
theorem groupsLoop_exec {ℓ : ℕ} (cap : ℕ) (σ : WState 3 40) (T np0 Wm Vb : ℕ) (ws : List ℕ) (hws : ws.length = ℓ)
    (hWm : ∀ w ∈ ws, w ≤ Wm) (hnp : 1 ≤ np0)
    (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0) (hW : σ.val rW = 0) (hF1 : σ.val rF1 = 0)
    (hF2 : σ.val rF2 = 0) (hJ : σ.val rJJ = 0) (hNP : σ.val rNP = np0) (hA : σ.val rA = 0) (hL : σ.val rL = ℓ)
    (hLC1 : σ.val rLC1 = 0) (hTMP : σ.val rTMP = 0) (hT2 : σ.val rT2 = 0) (hTT : σ.val rTT = T)
    (hLC3 : σ.val rLC3 = 0)
    (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hT : σ.val rTN = 0) (hG : σ.sh sG = (σ.st sG).length)
    (junk : List Bool) (hARGS : σ.st sARGS = argsStream ws ++ junk) (hAh : σ.sh sARGS = 0) (hCA : σ.val rCA = 0)
    (hVb : np0 + T * (2 * ℓ + 1) + T + Wm + 4 ≤ Vb)
    (hcap : 2 * T + Vb + 3 * ℓ + argPos ws ℓ + σ.val rR7 + 2 * (T * (ℓ * (12 * Vb + 18) + (6 * Vb + 9))) +
      14 * ℓ * (6 * Vb + 9) + 300 * (Vb + 10) ≤ cap) :
    WXExec cap (repK rTT rLC3 groupBody) σ (gst (ℓ := ℓ) σ np0 ws T) (groupsCost ℓ T np0 Wm (argPos ws ℓ)) := by
  have h0 : gst (ℓ := ℓ) σ np0 ws 0 = σ := by
    apply WState.eq
    · funext i; fin_cases i <;> simp [gst, grpBytes, marks]
    · funext i; fin_cases i <;> simp [gst, grpBytes, marks]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [gst, grpBytes, marks, hA, hNP]
    · rfl
  have hrep := Runs.repE (cap := cap) (K := rTT) (K2 := rLC3) (body := groupBody) (by decide)
    (groupCost ℓ T (np0 + T * (2 * ℓ + 1)) Wm (argPos ws ℓ)) T (gst (ℓ := ℓ) σ np0 ws) (by omega)
    (by intro k; simp [gst]) (by intro k; simp [gst]) ?_ (by rw [h0]; exact hTT) (by rw [h0]; exact hLC3)
  · rw [h0] at hrep; exact hrep
  intro k hk v1 v2
  have hw4 : ∀ w ∈ ws, w + 4 ≤ Vb := fun w hw => by have := hWm w hw; omega
  have hgl := grpBytes_length_le (ℓ := ℓ) np0 Vb ws hws hw4 T (by omega) k hk.le
  have hkT : k * (ℓ * (12 * Vb + 18) + (6 * Vb + 9)) ≤ T * (ℓ * (12 * Vb + 18) + (6 * Vb + 9)) :=
    Nat.mul_le_mul_right _ hk.le
  have hk1 : (k + 1) * (2 * ℓ + 1) ≤ T * (2 * ℓ + 1) := Nat.mul_le_mul_right _ hk
  have hk1' : (k + 1) * (2 * ℓ + 1) = k * (2 * ℓ + 1) + (2 * ℓ + 1) := by ring
  set gs := np0 + k * (2 * ℓ + 1) with hgs
  have hV1 : gs + 2 * ℓ + Wm + k + 4 ≤ Vb := by
    have : ∀ w ∈ ws, w ≤ Wm := hWm
    omega
  have hm1 : 14 * ℓ * (6 * (gs + 2 * ℓ + Wm + k + 4) + 9) ≤ 14 * ℓ * (6 * Vb + 9) :=
    Nat.mul_le_mul_left _ (by omega)
  have hgb := groupBody_exec (ℓ := ℓ) cap (((gst (ℓ := ℓ) σ np0 ws k).setv rTT v1).setv rLC3 v2) k gs Wm ws hws hWm
    (by omega)
    (by simp [gst, hX]) (by simp [gst, hY]) (by simp [gst, hBB]) (by simp [gst, hW]) (by simp [gst, hF1])
    (by simp [gst, hF2]) (by simp [gst, hJ]) (by simp [gst, hgs]) (by simp [gst]) (by simp [gst, hL])
    (by simp [gst, hLC1]) (by simp [gst, hTMP]) (by simp [gst, hT2])
    (fun r hr => by
      have := hwr r hr
      simp only [gst, WState.setv_val, appendO_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all)
    (by simp [gst, hT]) (by simp [gst, hG]) junk (by simp [gst, hARGS]) (by simp [gst, hAh]) (by simp [gst, hCA])
    (by
      have hR : (((gst (ℓ := ℓ) σ np0 ws k).setv rTT v1).setv rLC3 v2).val rR7 =
          σ.val rR7 + 2 * (grpBytes (ℓ := ℓ) np0 ws k).length := by
        simp [gst, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_len]
      rw [hR]
      omega)
  refine WXExec.mono (WXExec.cast cap hgb ?_ le_rfl) (groupCost_mono hk.le (by omega))
  have hbs : grpBytes (ℓ := ℓ) np0 ws (k + 1) = grpBytes (ℓ := ℓ) np0 ws k ++ groupBytes (ℓ := ℓ) k gs ws :=
    grpBytes_succ (ℓ := ℓ) np0 ws k
  apply WState.eq
  · funext i; fin_cases i <;> simp [gst, hbs, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append] <;> omega
  · funext i; fin_cases i <;> simp [gst, hbs, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append]
  · funext i; revert i; apply fin40_cases; intro i hi
    interval_cases i <;> simp [gst, hbs, NearCubicGates.Close.CheckedPCPP.NodeEmit.marks_append, hk1'] <;> omega
  · rfl

/-! ## The oracle block -/

/-- **The block of an oracle gate**: its arguments' images to `ARGS`, rewind, the `T` groups, `A := 0`. -/
def oracleBlock (ε : Bool) : WMX 3 40 :=
  .seq (repK rL rLC2 (argBody ε)) <| .seq (.wm (WM.rewind sARGS rCA)) <| .seq (repK rTT rLC3 groupBody) (clearReg rA)

/-- The state after an oracle block. -/
def ost {ℓ : ℕ} (ε : Bool) (σ : WState 3 40) (p0 : ℕ) (xs ws : List ℕ) (L0 : List Bool) (np0 T : ℕ) : WState 3 40 :=
  appendO (((σ.seth sCW (p0 + stp ε * (xs.flatMap natWord).length)).sets sARGS
    (StablePartition.Workspace.overlay (argsStream ws) L0)).setv rNP
    (np0 + T * (2 * ℓ + 1))) sG rR7 (marks (grpBytes (ℓ := ℓ) np0 ws T))

/-- The cost of an oracle block. -/
def oracleCost (ℓ T np0 Xm kk bz : ℕ) : ℕ :=
  ℓ * (argCost Xm kk bz + 8) + 7 * ℓ + 3 + (5 * (ℓ * (bz + Xm * kk + kk)) + 1) +
    groupsCost ℓ T np0 (bz + Xm * kk + kk) (ℓ * (bz + Xm * kk + kk)) + (3 * T + 1) + 3

theorem argPos_full (ws : List ℕ) : argPos ws ws.length = (argsStream ws).length := by
  rw [argsStream_length]; unfold argPos; rw [List.take_length]

theorem groupsCost_mono {ℓ T np0 Wm P P' : ℕ} (h : P ≤ P') : groupsCost ℓ T np0 Wm P ≤ groupsCost ℓ T np0 Wm P' := by
  unfold groupsCost groupCost
  have := Nat.mul_le_mul_left T (show
    ℓ * (pairCost T Wm (np0 + T * (2 * ℓ + 1) + 2 * ℓ + Wm + T + 4) + 8) + 7 * ℓ + 3 +
      nodeCost (np0 + T * (2 * ℓ + 1) + 2 * ℓ + Wm + T + 4) + 200 * (np0 + T * (2 * ℓ + 1) + 2 * ℓ + Wm + T + 14) +
        5 * P + 8 ≤
    ℓ * (pairCost T Wm (np0 + T * (2 * ℓ + 1) + 2 * ℓ + Wm + T + 4) + 8) + 7 * ℓ + 3 +
      nodeCost (np0 + T * (2 * ℓ + 1) + 2 * ℓ + Wm + T + 4) + 200 * (np0 + T * (2 * ℓ + 1) + 2 * ℓ + Wm + T + 14) +
        5 * P' + 8 by omega)
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **An oracle gate's block** (paper §11.6 stage 2): `K = T(2ℓ+1)` nodes, the multiplexer over the table inputs. -/
theorem oracleBlock_exec {ℓ : ℕ} (ε : Bool) (cap : ℕ) (σ : WState 3 40) (xs : List ℕ) (hxs : xs.length = ℓ)
    (T kk bz Xm np0 Vb : ℕ) (P0 rest L0 : List Bool)
    (hst : σ.st sCW = P0 ++ enc ε (xs.flatMap natWord) ++ rest) (hsh : σ.sh sCW = P0.length)
    (hRF : σ.val rRF = 0) (hRC : σ.val rRC = 0) (hRV : σ.val rRV = 0) (hRP : σ.val rRP = 0) (hRT : σ.val rRT = 0)
    (hIMG : σ.val rIMG = 0) (hT : σ.val rTN = 0) (hBZ : σ.val rBZ = bz) (hK : σ.val rKK = kk) (hk : 1 ≤ kk)
    (hL : σ.val rL = ℓ) (hLC2 : σ.val rLC2 = 0) (hO : OutOn σ sARGS rCA [] L0) (hXm : ∀ x ∈ xs, x ≤ Xm)
    (hX : σ.val rX = 0) (hY : σ.val rY = 0) (hBB : σ.val rBB = 0) (hW : σ.val rW = 0) (hF1 : σ.val rF1 = 0)
    (hF2 : σ.val rF2 = 0) (hJ : σ.val rJJ = 0) (hNP : σ.val rNP = np0) (hnp : 1 ≤ np0) (hA : σ.val rA = 0)
    (hLC1 : σ.val rLC1 = 0) (hTMP : σ.val rTMP = 0) (hT2 : σ.val rT2 = 0) (hTT : σ.val rTT = T)
    (hLC3 : σ.val rLC3 = 0) (hwr : ∀ r : Fin 40, r.val ≤ 6 → σ.val r = 0) (hG : σ.sh sG = (σ.st sG).length)
    (hVb : np0 + T * (2 * ℓ + 1) + T + (bz + Xm * kk + kk) + 4 ≤ Vb)
    (hcap1 : 2 * ℓ + 2 ^ (natBitLength Xm + 1) + bz + Xm * kk + kk + ℓ * (bz + Xm * kk + kk) + 10 ≤ cap)
    (hcap2 : 2 * T + Vb + 3 * ℓ + ℓ * (bz + Xm * kk + kk) + σ.val rR7 +
      2 * (T * (ℓ * (12 * Vb + 18) + (6 * Vb + 9))) + 14 * ℓ * (6 * Vb + 9) + 300 * (Vb + 10) ≤ cap) :
    WXExec cap (oracleBlock ε) σ
      (ost (ℓ := ℓ) ε σ P0.length xs (xs.map (fun x => bz + x * kk + kk - 1)) L0 np0 T)
      (oracleCost ℓ T np0 Xm kk bz) := by
  set im : ℕ → ℕ := fun x => bz + x * kk + kk - 1 with him
  set ws := xs.map im with hws
  have hwsl : ws.length = ℓ := by simp [ws, hxs]
  have hWm : ∀ w ∈ ws, w ≤ bz + Xm * kk + kk := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    have := Nat.mul_le_mul_right kk (hXm y hy)
    simp only [im]; omega
  have hsl : (argsStream ws).length ≤ ℓ * (bz + Xm * kk + kk) := by
    have := argsStream_length_le ws (bz + Xm * kk + kk) (by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
      have := Nat.mul_le_mul_right kk (hXm y hy)
      simp only [im]; omega)
    rwa [hwsl] at this
  -- 1. the arguments
  have h1 := argsLoop_exec ε cap σ xs kk bz Xm P0 rest L0 hst hsh hRF hRC hRV hRP hRT hIMG hT hBZ hK hk
    (by rw [hL, hxs]) hLC2 hO hXm (by rw [hxs]; exact hcap1)
  rw [hxs] at h1
  have htk : (xs.map im).take ℓ = ws := by rw [← hxs]; simp [ws]
  have htk2 : List.take ℓ (List.map im xs) = List.map im xs := List.take_of_length_le (by simp [hxs])
  have htx : xs.take ℓ = xs := List.take_of_length_le (by simp [hxs])
  set σ1 := ast ε σ P0.length xs im L0 ℓ with hσ1
  have hσ1CA : σ1.val rCA = (argsStream ws).length := by simp [σ1, ast, outSt, htk, htk2, ws]
  have hσ1sh : σ1.sh sARGS = (argsStream ws).length := by simp [σ1, ast, outSt, htk, htk2, ws]
  -- 2. rewind
  have h2 := WXExec.wm (wrewind_spec (cap := cap) sARGS rCA (argsStream ws).length σ1 hσ1CA (by omega))
  set σ2 := (σ1.setv rCA 0).seth sARGS (σ1.sh sARGS - (argsStream ws).length) with hσ2
  -- 3. the groups
  have hap : argPos ws ℓ = (argsStream ws).length := by rw [← hwsl]; exact argPos_full ws
  have h3 := groupsLoop_exec (ℓ := ℓ) cap σ2 T np0 (bz + Xm * kk + kk) Vb ws hwsl hWm hnp
    (by simp [σ2, σ1, ast, outSt, hX]) (by simp [σ2, σ1, ast, outSt, hY]) (by simp [σ2, σ1, ast, outSt, hBB])
    (by simp [σ2, σ1, ast, outSt, hW]) (by simp [σ2, σ1, ast, outSt, hF1]) (by simp [σ2, σ1, ast, outSt, hF2])
    (by simp [σ2, σ1, ast, outSt, hJ]) (by simp [σ2, σ1, ast, outSt, hNP]) (by simp [σ2, σ1, ast, outSt, hA])
    (by simp [σ2, σ1, ast, outSt, hL]) (by simp [σ2, σ1, ast, outSt, hLC1]) (by simp [σ2, σ1, ast, outSt, hTMP])
    (by simp [σ2, σ1, ast, outSt, hT2]) (by simp [σ2, σ1, ast, outSt, hTT]) (by simp [σ2, σ1, ast, outSt, hLC3])
    (fun r hr => by
      have := hwr r hr
      simp only [σ2, σ1, ast, outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all)
    (by simp [σ2, σ1, ast, outSt, hT]) (by simp [σ2, σ1, ast, outSt, hG])
    (L0.drop (argsStream ws).length) (by simp [σ2, σ1, ast, outSt, htk, htk2, ws, StablePartition.Workspace.overlay])
    (by simp [σ2, σ1, ast, outSt, htk2, ws]) (by simp [σ2, σ1, ast, outSt]) hVb
    (by
      have hR : σ2.val rR7 = σ.val rR7 := by simp [σ2, σ1, ast, outSt]
      rw [hR, hap]; omega)
  set σ3 := gst (ℓ := ℓ) σ2 np0 ws T with hσ3
  -- 4. A := 0
  have h4 := clearReg_exec (cap := cap) rA T σ3 (by simp [σ3, gst]) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 h4))) ?_ le_rfl) ?_
  · have hO1 := hO.1
    have hO2 := hO.2.1
    have hO3 := hO.2.2
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ3, σ2, σ1, gst, ast, outSt, ost, htk, htk2, htx, ws, hO2]
    · funext i; fin_cases i <;> simp [σ3, σ2, σ1, gst, ast, outSt, ost, htk, htk2, htx, ws]
    · funext i; revert i; apply fin40_cases; intro i hi
      interval_cases i <;> simp [σ3, σ2, σ1, gst, ast, outSt, ost, htk, htk2, htx, ws, hO3, hA]
    · rfl
  · unfold oracleCost
    have := groupsCost_mono (ℓ := ℓ) (T := T) (np0 := np0) (Wm := bz + Xm * kk + kk) (P := argPos ws ℓ)
      (P' := ℓ * (bz + Xm * kk + kk)) (by rw [hap]; exact hsl)
    omega

/-! ## Meaning of the oracle block -/

/-- The argument list of an oracle gate, as read from its word. -/
theorem args_word {ℓ : ℕ} (args : Fin ℓ → ℕ) :
    (List.ofFn fun j => natWord (args j)).flatten = (List.ofFn args).flatMap natWord := by
  simp [List.flatMap_def, List.map_ofFn, Function.comp_def]

/-- **The oracle block's bytes** are the native bytes of `TCirc.block` at an oracle gate. -/
theorem oracle_bytes {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ) (z c : ℕ) (args : Fin ℓ → ℕ) :
    (TCirc.block C z c (.oracle args)).flatMap PCPPRequestNodeSchema.native =
      grpBytes (ℓ := ℓ) (TCirc.bs C z c)
        ((List.ofFn args).map (fun x => TCirc.base C z + x * TCirc.K ℓ + TCirc.K ℓ - 1)) (TCirc.T ℓ) := by
  have hK : 1 ≤ TCirc.K ℓ := Nat.mul_pos (Nat.two_pow_pos ℓ) (by omega)
  unfold TCirc.block grpBytes
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro a _
  rw [group_bytes C z c args a]
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn]
  simp [List.ofFnNthVal, hj, TCirc.img]
  omega

end NearCubicGates.Close.ENP.TEmit
