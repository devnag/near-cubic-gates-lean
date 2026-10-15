import Proof.Gates.Succinct.SubstitutionHeader

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct
open RepairRepresentation (natWord)

variable {q ℓ : ℕ}

/-! ## Node words -/

/-- The tag of a node word. -/
def otag : OracleNode ℓ ℓ → ℕ
  | .const _ => 0
  | .input _ => 1
  | .not _ => 2
  | .and _ _ => 3
  | .or _ _ => 4
  | .oracle _ => 5

/-- The two fields after the tag of a plain node word. -/
def ofld : OracleNode ℓ ℓ → ℕ × ℕ
  | .const b => (b.toNat, 0)
  | .input i => (i.val, 0)
  | .not c => (c, 0)
  | .and l r => (l, r)
  | .or l r => (l, r)
  | .oracle _ => (0, 0)

/-- The arguments of an oracle gate. -/
def oargs : OracleNode ℓ ℓ → List ℕ
  | .oracle args => List.ofFn args
  | _ => []

theorem plain_word (nd : OracleNode ℓ ℓ) (h : isO nd = false) :
    oracleNodeWord nd = natWord (otag nd) ++ natWord (ofld nd).1 ++ natWord (ofld nd).2 ∧ otag nd ≤ 4 := by
  cases nd <;> simp [isO] at h <;> simp [oracleNodeWord, otag, ofld]

theorem oracle_word (nd : OracleNode ℓ ℓ) (h : isO nd = true) :
    oracleNodeWord nd = natWord 5 ++ (oargs nd).flatMap natWord ∧ otag nd = 5 ∧ (oargs nd).length = ℓ := by
  cases nd <;> simp [isO] at h
  rename_i args
  refine ⟨?_, rfl, by simp [oargs]⟩
  simp only [oracleNodeWord, oargs, List.flatMap, List.map_ofFn]
  rfl

theorem flatMap_split' {α β : Type} (f : α → List β) (xs : List α) (k : ℕ) (hk : k < xs.length) :
    xs.flatMap f = (xs.take k).flatMap f ++ f xs[k] ++ (xs.drop (k + 1)).flatMap f := by
  have h1 : (xs.take (k + 1)).flatMap f = (xs.take k).flatMap f ++ f xs[k] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]; simp
  rw [← h1, ← List.flatMap_append, List.take_append_drop]

/-! ## The pieces -/

/-- **`ℓ` from its copied field** (exact). -/
theorem getL_spec (cap : ℕ) (σ : WState 4 nrH) (ℓ : ℕ) (hL : σ.st sL = natWord ℓ) (hLh : σ.sh sL = 0)
    (hf : ∀ r, σ.val (regH (.f r)) = 0) (hpk : σ.val (regH .pk) = 0) (hpt : σ.val (regH .pt) = 0)
    (hl : σ.val (regH .L) = 0) (hcd : σ.val (regH .cdL) = 0) (hcap : 8 * ℓ + 2 * (natWord ℓ).length + 20 ≤ cap) :
    WExec cap getL σ (σ.setv (regH .L) ℓ) (readCost ℓ + 5 * (natWord ℓ).length + 2) := by
  have hnl := natWord_length ℓ
  have e1 := readEx_spec cap sL RL (regH .pk) (regH .pt) (regH .L) (rdRegs .cdL .L (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp)) σ [] [] ℓ (by simp [hL]) (by simp [hLh]) (famZero _ _ hf) hpk hpt hl
    (by simp only [RL, fam_cd, hcd]; omega)
  set σ1 := ((σ.seth sL ([].length + (natWord ℓ).length)).setv (RL .cd) (σ.val (RL .cd) + (natWord ℓ).length)).setv
    (regH .L) ℓ with hσ1
  have e2 := wrewind_spec cap sL (regH .cdL) (natWord ℓ).length σ1 (by simp [σ1, hcd]) (by simp [σ1, hcd]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl) (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext i; by_cases hi : i = sL
    · rw [hi]; simp [σ1, hLh]
    · simp [σ1, Function.update_apply, hi]
  · funext r; simp only [σ1, WState.setv_val, WState.seth_val, Function.update_apply, RL, fam_cd]
    split_ifs <;> simp_all

/-- **Count pass, a plain node** (exact). -/
theorem cPlain_spec (cap : ℕ) (σ : WState 4 nrH) (pre rest fl : List Bool) (a b : ℕ)
    (hW : σ.st sW = pre ++ natWord a ++ natWord b ++ rest) (hWh : σ.sh sW = pre.length)
    (hF : σ.st sF = fl) (hFh : σ.sh sF = fl.length)
    (hf : ∀ r, σ.val (regH (.f r)) = 0) (hz : σ.val (regH .z) = 0) (hj : σ.val (regH .jk) = 0)
    (hcap : σ.val (regH .cdW) + (natWord a).length + 2 * natBitLength a + 2 * natBitLength b + 12 ≤ cap) :
    WExec cap cPlain σ
      ((((σ.seth sW (pre.length + (natWord a).length + (natWord b).length)).setv (regH .cdW)
        (σ.val (regH .cdW) + (natWord a).length + (natWord b).length)).sets sF (fl ++ [false])).seth sF (fl.length + 1))
      (skipCost a + skipCost b + 6) := by
  have hna := natWord_length a
  have hnb := natWord_length b
  have e1 := skipF_spec cap sW RW (fam_inj _ (by simp)) (regH .z) (regH .jk) (famNe _ _ (by simp) (by simp))
    (famNe _ _ (by simp) (by simp)) σ pre (natWord b ++ rest) a (by rw [hW]; simp [List.append_assoc]) hWh
    (famZero _ _ hf) hz hj (by simp only [RW, fam_cd]; omega)
  set σ1 := (σ.seth sW (pre.length + (natWord a).length)).setv (RW .cd) (σ.val (RW .cd) + (natWord a).length)
    with hσ1
  have e2 := skipF_spec cap sW RW (fam_inj _ (by simp)) (regH .z) (regH .jk) (famNe _ _ (by simp) (by simp))
    (famNe _ _ (by simp) (by simp)) σ1 (pre ++ natWord a) rest b (by simp [σ1, hW]) (by simp [σ1])
    (famZero _ _ (fun r => by simp [σ1, hf])) (by simp [σ1, hz]) (by simp [σ1, hj])
    (by simp only [σ1, RW, fam_cd, WState.setv_val, Function.update_self]; omega)
  set σ2 := (σ1.seth sW ((pre ++ natWord a).length + (natWord b).length)).setv (RW .cd)
    (σ1.val (RW .cd) + (natWord b).length) with hσ2
  have e3 := WExec.wr (cap := cap) sF false σ2
  have hw : writeTapeBit (σ2.st sF) (σ2.sh sF) false = fl ++ [false] := by
    simp only [σ2, σ1, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_apply,
      sF_ne_sW, if_false, hF, hFh]
    exact FinalPass.Tm.writeTapeBit_end' _ _
  rw [hw] at e3
  have e4 := WExec.fwd (cap := cap) sF (σ2.sets sF (fl ++ [false]))
  refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl) (by omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext i; by_cases hi : i = sF
    · rw [hi]; simp [σ2, σ1, hFh]
    · by_cases hi2 : i = sW
      · rw [hi2]; simp [σ2, σ1] <;> omega
      · simp [σ2, σ1, Function.update_apply, hi, hi2]
  · funext i; by_cases hi : i = sF
    · rw [hi]; simp [σ2, σ1]
    · simp [σ2, σ1, Function.update_apply, hi]
  · funext r; simp only [σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply, RW, fam_cd]
    split_ifs <;> simp_all <;> omega

/-- The cost of an oracle gate in the count pass. -/
def cOracleCost (ℓ VB : ℕ) : ℕ := readCost ℓ + ℓ * (1000 * (VB + 3) + 30) + 10 * (natWord ℓ).length + 40

/-- **Count pass, an oracle gate** (exact). -/
theorem cOracle_spec (cap : ℕ) (σ : WState 4 nrH) (pre rest fl : List Bool) (args : List ℕ) (ℓ VB : ℕ)
    (hlen : args.length = ℓ) (hVB : ∀ x ∈ args, natBitLength x ≤ VB)
    (hW : σ.st sW = pre ++ args.flatMap natWord ++ rest) (hWh : σ.sh sW = pre.length)
    (hF : σ.st sF = fl) (hFh : σ.sh sF = fl.length) (hL : σ.st sL = natWord ℓ) (hLh : σ.sh sL = 0)
    (hf : ∀ r, σ.val (regH (.f r)) = 0) (hpk : σ.val (regH .pk) = 0) (hpt : σ.val (regH .pt) = 0)
    (hl : σ.val (regH .L) = 0) (hcd : σ.val (regH .cdL) = 0) (hsk : σ.val (regH .sk) = 0)
    (ht : σ.val (regH .t) = 0) (hz : σ.val (regH .z) = 0) (hj : σ.val (regH .jk) = 0)
    (hcap : σ.val (regH .cdW) + σ.val (regH .k) + (args.flatMap natWord).length + 8 * ℓ + 2 * (natWord ℓ).length +
      2 * VB + 30 ≤ cap) :
    WExec cap cOracle σ
      (((((σ.sets sF (fl ++ [true])).seth sF (fl.length + 1)).setv (regH .k) (σ.val (regH .k) + 1)).seth sW
        (pre.length + (args.flatMap natWord).length)).setv (regH .cdW)
        (σ.val (regH .cdW) + (args.flatMap natWord).length)) (cOracleCost ℓ VB) := by
  have hnl := natWord_length ℓ
  have e1 := WExec.wr (cap := cap) sF true σ
  rw [hF, hFh, FinalPass.Tm.writeTapeBit_end'] at e1
  set σ1 := σ.sets sF (fl ++ [true]) with hσ1
  have e2 := WExec.fwd (cap := cap) sF σ1
  rw [show σ1.sh sF + 1 = fl.length + 1 by simp [σ1, hFh]] at e2
  set σ2 := σ1.seth sF (fl.length + 1) with hσ2
  have e3 := WExec.inc (cap := cap) (regH .k) σ2 (by simp [σ2, σ1]; omega)
  set σ3 := σ2.setv (regH .k) (σ2.val (regH .k) + 1) with hσ3
  have e4 := getL_spec cap σ3 ℓ (by simp [σ3, σ2, σ1, hL]) (by simp [σ3, σ2, σ1, hLh])
    (fun r => by simp [σ3, σ2, σ1, hf]) (by simp [σ3, σ2, σ1, hpk]) (by simp [σ3, σ2, σ1, hpt])
    (by simp [σ3, σ2, σ1, hl]) (by simp [σ3, σ2, σ1, hcd]) (by omega)
  set σ4 := σ3.setv (regH .L) ℓ with hσ4
  have e5 := addTo_spec cap (regH .L) (regH .sk) (regH .t) (by simp) (by simp) (by simp) σ4
    (by simp [σ4, σ3, σ2, σ1, ht]) (by simp [σ4]; omega) (by simp [σ4, σ3, σ2, σ1, hsk]; omega)
  rw [show σ4.val (regH .sk) + σ4.val (regH .L) = ℓ by simp [σ4, σ3, σ2, σ1, hsk]] at e5
  set σ5 := σ4.setv (regH .sk) ℓ with hσ5
  have e6 := skipN_spec cap sW RW (fam_inj _ (by simp)) (regH .z) (regH .jk) (regH .sk) (famNe _ _ (by simp) (by simp))
    (famNe _ _ (by simp) (by simp)) (famNe _ _ (by simp) (by simp)) (by simp) (by simp) σ5 pre rest args VB hVB
    (by simp [σ5, σ4, σ3, σ2, σ1, hW]) (by simp [σ5, σ4, σ3, σ2, σ1, hWh]) (famZero _ _ (fun r => by
      simp [σ5, σ4, σ3, σ2, σ1, hf])) (by simp [σ5, σ4, σ3, σ2, σ1, hz]) (by simp [σ5, σ4, σ3, σ2, σ1, hj])
    (by simp [σ5, hlen]) (by
      have c : σ5.val (RW .cd) = σ.val (regH .cdW) := by simp [σ5, σ4, σ3, σ2, σ1, RW]
      rw [c]; omega) (by omega)
  set σ6 := ((σ5.seth sW (pre.length + (args.flatMap natWord).length)).setv (RW .cd)
    (σ5.val (RW .cd) + (args.flatMap natWord).length)).setv (regH .sk) 0 with hσ6
  have e7 := wclear_spec cap (regH .L) ℓ σ6 (by simp [σ6, σ5, σ4]) (by simp [σ6, σ5, σ4]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7)))))) ?_ le_rfl) ?_
  · refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]
    · funext i; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]
    · funext r; simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val,
        Function.update_apply, RW, fam_cd]
      split_ifs <;> simp_all
  · have c5 : σ4.val (regH .L) = ℓ := by simp [σ4]
    rw [c5]; unfold cOracleCost; nlinarith

/-! ## The loop -/

section Loop
variable (o : OracleOutput) (B : BooleanCircuit q)

/-- The length of the first `j` node words of `C`. -/
def lenC (j : ℕ) : ℕ := ((o.circuit.nodes.take j).flatMap oracleNodeWord).length

/-- The start of `C`'s node words. -/
def pC : ℕ := (natWord o.ell).length + (natWord o.circuit.nodes.length).length

/-- The start of `B`'s node words. -/
def pB (B : BooleanCircuit q) : ℕ := (natWord q).length + (natWord B.nodes.length).length

/-- The registers during the count pass, after `j` nodes. -/
def cntV (j : ℕ) : HReg → ℕ := fun u =>
  if u = .cdW then lenC o j else if u = .k then kOf o.circuit j else if u = .iC then o.circuit.nodes.length - j
  else V1 o B u

/-- The state of the count pass after `j` nodes. -/
def CntInv (j : ℕ) (τ : WState 4 nrH) : Prop :=
  StrAt τ o.word (PCPPNative.descriptor B) [] ((ofl o.circuit).take j) (natWord o.ell) (pC o + lenC o j) (pB B) 0 j 0 ∧
    RV τ (cntV o B j) ∧ τ.cell = false

theorem word_split (j : ℕ) (hj : j < o.circuit.nodes.length) :
    o.word = (natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take j).flatMap oracleNodeWord) ++
      oracleNodeWord o.circuit.nodes[j] ++
      ((o.circuit.nodes.drop (j + 1)).flatMap oracleNodeWord ++ natWord o.circuit.output.val) := by
  rw [word_eq, flatMap_split' oracleNodeWord o.circuit.nodes j hj]
  simp only [List.append_assoc]

theorem lenC_succ (j : ℕ) (hj : j < o.circuit.nodes.length) :
    lenC o (j + 1) = lenC o j + (oracleNodeWord o.circuit.nodes[j]).length := by
  unfold lenC
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]; simp

theorem ofl_take_succ (j : ℕ) (hj : j < o.circuit.nodes.length) :
    (ofl o.circuit).take (j + 1) = (ofl o.circuit).take j ++ [isO o.circuit.nodes[j]] := by
  unfold ofl
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hj), Option.toList_some]; simp

theorem ofl_take_len (j : ℕ) (hj : j ≤ o.circuit.nodes.length) : ((ofl o.circuit).take j).length = j := by
  simp [ofl]; omega

theorem lenC_le (j : ℕ) : pC o + lenC o j ≤ o.word.length := by
  unfold pC lenC
  rw [word_eq]
  simp only [List.length_append]
  have : ((o.circuit.nodes.take j).flatMap oracleNodeWord).length ≤ (o.circuit.nodes.flatMap oracleNodeWord).length := by
    conv_rhs => rw [← List.take_append_drop j o.circuit.nodes]
    rw [List.flatMap_append, List.length_append]; omega
  omega

end Loop

/-- The cost of one node in the count pass. -/
def cntIter (S : ℕ) : ℕ := 1000000 * (S + 2) ^ 2

theorem cbranch_plain (t : ℕ) (ht : t ≤ 4) :
    [cPlain, cPlain, cPlain, cPlain, cPlain, cOracle][t]'(by simp; omega) = cPlain := by
  interval_cases t <;> rfl

theorem oargs_lt (o : OracleOutput) (j : ℕ) (hj : j < o.circuit.nodes.length) :
    ∀ x ∈ oargs o.circuit.nodes[j], x < j := by
  intro x hx
  have hw := o.circuit.wellFormed ⟨j, hj⟩
  simp only [List.get_eq_getElem] at hw
  revert hx
  cases h : o.circuit.nodes[j] with
  | oracle args =>
    rw [h] at hw
    intro hx
    simp only [oargs, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hw i
  | _ => simp [oargs]

theorem skip2_le (a b S : ℕ) (ha : natBitLength a ≤ S) (hb : natBitLength b ≤ S) :
    skipCost a + skipCost b ≤ 2000 * (S + 3) := by unfold skipCost; omega

theorem sq_le (x : ℕ) : x + 4 ≤ (x + 2) ^ 2 := by nlinarith

theorem oracleCost_le (ℓ S : ℕ) (hℓ : ℓ ≤ S) (hn : (natWord ℓ).length ≤ S) :
    cOracleCost ℓ S + readCost 5 + 20 ≤ 1000000 * (S + 2) ^ 2 := by
  unfold cOracleCost readCost
  have h1 : (ℓ + 2) ^ 2 ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : ℓ * (1000 * (S + 3) + 30) ≤ (S + 2) * (1000 * (S + 3) + 30) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **One node of the count pass.** -/
theorem countStep (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (j : ℕ) (hj : j < o.circuit.nodes.length)
    (σ : WState 4 nrH) (hI : CntInv o B j σ) (hcap : 20 * sizeS o B + 100 ≤ cap) :
    ∃ τ, WExec cap countBody (σ.setv (regH .iC) (o.circuit.nodes.length - j - 1)) τ (cntIter (sizeS o B)) ∧
      CntInv o B (j + 1) τ ∧ τ.val (regH .iC) = o.circuit.nodes.length - j - 1 := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, hv, hcell⟩ := hI
  have hv' : ∀ u, σ.val (regH u) = cntV o B j u := hv
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have hS : sizeS o B = o.word.length + (PCPPNative.descriptor B).length + q + 1 := rfl
  have hle := lenC_le o j
  have hle1 := lenC_le o (j + 1)
  have hls := lenC_succ o j hj
  have hsplit := word_split o j hj
  set nd := o.circuit.nodes[j] with hnd
  set pre := natWord o.ell ++ natWord o.circuit.nodes.length ++ (o.circuit.nodes.take j).flatMap oracleNodeWord
    with hpre
  set rst := (o.circuit.nodes.drop (j + 1)).flatMap oracleNodeWord ++ natWord o.circuit.output.val with hrst
  have hprel : pre.length = pC o + lenC o j := by simp only [pre, pC, lenC, List.length_append]
  set σ' := σ.setv (regH .iC) (o.circuit.nodes.length - j - 1) with hσ'
  have v' : ∀ u, σ'.val (regH u) = if u = .iC then o.circuit.nodes.length - j - 1 else cntV o B j u := by
    intro u; simp [σ', Function.update_apply, hv']
  have hcdW : σ'.val (regH .cdW) = lenC o j := by rw [v']; simp [cntV]
  have hcd' : σ'.val (RW .cd) = lenC o j := by rw [show RW .cd = regH .cdW from fam_cd _, hcdW]
  have hfz : ∀ r, σ'.val (regH (.f r)) = 0 := fun r => by rw [v']; simp [cntV, V1]
  have hW0 : σ'.st sW = pre ++ oracleNodeWord nd ++ rst := by simp [σ', a1, hsplit, pre, rst, nd]
  have hWh0 : σ'.sh sW = pre.length := by simp [σ', a6, hprel]
  have hwl : (oracleNodeWord nd).length + pre.length ≤ o.word.length := by
    have := lenC_le o (j + 1); rw [hls] at this; omega
  rcases hO : isO nd with _ | _
  · -- a plain node
    obtain ⟨hw, ht4⟩ := plain_word nd hO
    have hnt := natWord_length (otag nd)
    have hlw : (natWord (otag nd)).length + (natWord (ofld nd).1).length + (natWord (ofld nd).2).length =
        (oracleNodeWord nd).length := by rw [hw]; simp only [List.length_append]
    have hba := nbl_le (ofld nd).1
    have hbb := nbl_le (ofld nd).2
    have hna := natWord_length (ofld nd).1
    have hnb := natWord_length (ofld nd).2
    have e1 := readEx_spec cap sW RW (regH .pk) (regH .pt) (regH .tag) (rdRegs .cdW .tag (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)) σ' pre (natWord (ofld nd).1 ++ natWord (ofld nd).2 ++ rst) (otag nd)
      (by rw [hW0, hw]; simp only [List.append_assoc]) hWh0 (famZero _ _ hfz) (by rw [v']; simp [cntV, V1])
      (by rw [v']; simp [cntV, V1]) (by rw [v']; simp [cntV, V1]) (by rw [hcd']; omega)
    set σ1 := ((σ'.seth sW (pre.length + (natWord (otag nd)).length)).setv (RW .cd)
      (σ'.val (RW .cd) + (natWord (otag nd)).length)).setv (regH .tag) (otag nd) with hσ1
    have e2 := cPlain_spec cap (σ1.setv (regH .tag) 0) (pre ++ natWord (otag nd)) rst ((ofl o.circuit).take j)
      (ofld nd).1 (ofld nd).2 (by simp [σ1, σ', a1, hsplit, hw, pre, rst, nd, List.append_assoc])
      (by simp [σ1]) (by simp [σ1, σ', a4]) (by simp [σ1, σ', a9, ofl_take_len o j hj.le])
      (fun r => by simp [σ1, Function.update_apply, hfz]) (by simp [σ1, Function.update_apply, v', cntV, V1])
      (by simp [σ1, Function.update_apply, v', cntV, V1])
      (by have : (σ1.setv (regH .tag) 0).val (regH .cdW) = lenC o j + (natWord (otag nd)).length := by
            simp [σ1, RW, hcdW]
          rw [this]; omega)
    have e3 := caseL_spec cap (regH .tag) [cPlain, cPlain, cPlain, cPlain, cPlain, cOracle] (otag nd)
      (by simp; omega) σ1 _ _ (by simp [σ1]) (by simp [σ1]; omega) (by rw [cbranch_plain _ ht4]; exact e2)
    refine ⟨_, WExec.mono (WExec.seq e1 e3) ?_, ?_, ?_⟩
    rotate_left
    · unfold CntInv StrAt
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp [σ1, σ', a1]
      · simp [σ1, σ', a2]
      · simp [σ1, σ', a3]
      · simp [σ1, σ', ofl_take_succ o j hj, hO, nd]
      · simp [σ1, σ', a5]
      · simp [σ1, hls]; omega
      · simp [σ1, σ', a7]
      · simp [σ1, σ', a8]
      · simp [σ1, σ', ofl_take_len o j hj.le]
      · simp [σ1, σ', a10]
      · intro u
        by_cases h1 : u = .cdW
        · subst h1; simp [σ1, RW, hcd', cntV, hls]; omega
        · by_cases h2 : u = .k
          · subst h2; simp [σ1, Function.update_apply, v', cntV, kOf_succ o.circuit j hj, hO, nd]
          · by_cases h3 : u = .iC
            · subst h3; simp [σ1, Function.update_apply, v', cntV]; omega
            · by_cases h4 : u = .tag
              · subst h4; simp [σ1, Function.update_apply, cntV, V1]
              · simp [σ1, Function.update_apply, v', cntV, h1, h2, h3, h4]
      · simp [σ1, σ', hcell]
    · simp [σ1, Function.update_apply, v']
    · have hrc : readCost (otag nd) ≤ 10000 * 7 ^ 2 := by
        unfold readCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      have hsk := skip2_le (ofld nd).1 (ofld nd).2 (sizeS o B) (by omega) (by omega)
      have := sq_le (sizeS o B)
      unfold cntIter; omega
  · -- an oracle gate
    obtain ⟨hw, ht5, hal⟩ := oracle_word nd hO
    have hn5 := natWord_length (otag nd)
    have hwords := flatMap_natWord_len (oargs nd)
    have hlw : (natWord (otag nd)).length + ((oargs nd).flatMap natWord).length = (oracleNodeWord nd).length := by
      rw [hw, ht5]; simp only [List.length_append]
    have hnℓ := hwh
    have e1 := readEx_spec cap sW RW (regH .pk) (regH .pt) (regH .tag) (rdRegs .cdW .tag (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)) σ' pre ((oargs nd).flatMap natWord ++ rst) (otag nd)
      (by rw [hW0, hw, ht5]; simp only [List.append_assoc]) hWh0 (famZero _ _ hfz) (by rw [v']; simp [cntV, V1])
      (by rw [v']; simp [cntV, V1]) (by rw [v']; simp [cntV, V1]) (by rw [hcd', ht5]; omega)
    set σ1 := ((σ'.seth sW (pre.length + (natWord (otag nd)).length)).setv (RW .cd)
      (σ'.val (RW .cd) + (natWord (otag nd)).length)).setv (regH .tag) (otag nd) with hσ1
    have hk : kOf o.circuit j ≤ j := by
      unfold kOf; exact (List.countP_le_length).trans (by simp)
    have e2 := cOracle_spec cap (σ1.setv (regH .tag) 0) (pre ++ natWord (otag nd)) rst ((ofl o.circuit).take j)
      (oargs nd) o.ell (sizeS o B) hal
      (fun x hx => (nbl_le x).trans (by have := oargs_lt o j hj x hx; omega))
      (by simp [σ1, σ', a1, hsplit, hw, ht5, pre, rst, nd, List.append_assoc]) (by simp [σ1])
      (by simp [σ1, σ', a4]) (by simp [σ1, σ', a9, ofl_take_len o j hj.le]) (by simp [σ1, σ', a5])
      (by simp [σ1, σ', a10]) (fun r => by simp [σ1, Function.update_apply, hfz])
      (by simp [σ1, Function.update_apply, v', cntV, V1]) (by simp [σ1, Function.update_apply, v', cntV, V1])
      (by simp [σ1, Function.update_apply, v', cntV, V1]) (by simp [σ1, Function.update_apply, v', cntV, V1])
      (by simp [σ1, Function.update_apply, v', cntV, V1]) (by simp [σ1, Function.update_apply, v', cntV, V1])
      (by simp [σ1, Function.update_apply, v', cntV, V1]) (by simp [σ1, Function.update_apply, v', cntV, V1])
      (by have h1 : (σ1.setv (regH .tag) 0).val (regH .cdW) = lenC o j + (natWord (otag nd)).length := by
            simp [σ1, RW, hcdW]
          have h2 : (σ1.setv (regH .tag) 0).val (regH .k) = kOf o.circuit j := by
            simp [σ1, Function.update_apply, v', cntV]
          rw [h1, h2]; omega)
    have hb5 : [cPlain, cPlain, cPlain, cPlain, cPlain, cOracle][otag nd]'(by simp; omega) = cOracle := by
      simp [ht5]
    have e3 := caseL_spec cap (regH .tag) [cPlain, cPlain, cPlain, cPlain, cPlain, cOracle] (otag nd)
      (by simp; omega) σ1 _ _ (by simp [σ1]) (by simp [σ1]; omega) (by rw [hb5]; exact e2)
    refine ⟨_, WExec.mono (WExec.seq e1 e3) ?_, ?_, ?_⟩
    rotate_left
    · unfold CntInv StrAt
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp [σ1, σ', a1]
      · simp [σ1, σ', a2]
      · simp [σ1, σ', a3]
      · simp [σ1, σ', ofl_take_succ o j hj, hO, nd]
      · simp [σ1, σ', a5]
      · have hlw' := hlw
        have hpre' := hprel
        simp [σ1, hls] at hlw' hpre' ⊢; omega
      · simp [σ1, σ', a7]
      · simp [σ1, σ', a8]
      · simp [σ1, σ', ofl_take_len o j hj.le]
      · simp [σ1, σ', a10]
      · intro u
        by_cases h1 : u = .cdW
        · have hlw' := hlw
          subst h1; simp [σ1, RW, hcdW, cntV, hls] at hlw' ⊢; omega
        · by_cases h2 : u = .k
          · subst h2; simp [σ1, Function.update_apply, v', cntV, kOf_succ o.circuit j hj, hO, nd]
          · by_cases h3 : u = .iC
            · subst h3; simp [σ1, Function.update_apply, v', cntV]; omega
            · by_cases h4 : u = .tag
              · subst h4; simp [σ1, Function.update_apply, cntV, V1]
              · simp [σ1, Function.update_apply, v', cntV, h1, h2, h3, h4]
      · simp [σ1, σ', hcell]
    · simp [σ1, Function.update_apply, v']
    · rw [ht5]
      have := oracleCost_le o.ell (sizeS o B) (by omega) (by omega)
      unfold cntIter; omega

/-- The registers after the count pass. -/
def V2 (o : OracleOutput) (B : BooleanCircuit q) : HReg → ℕ := fun u =>
  if u = .k then kOf o.circuit o.circuit.nodes.length else if u = .oC then o.circuit.output.val else
  if u = .cdW then 0 else V1 o B u

/-- The state after the count pass. -/
def CntPost (o : OracleOutput) (B : BooleanCircuit q) (τ : WState 4 nrH) : Prop :=
  StrAt τ o.word (PCPPNative.descriptor B) [] (ofl o.circuit) (natWord o.ell) (pC o) (pB B) 0 0 0 ∧
    RV τ (V2 o B) ∧ τ.cell = false

/-- The cost class of the count pass. -/
def cntCost (S : ℕ) : ℕ := 3000000 * (S + 2) ^ 3

theorem cnt_arith (X n : ℕ) (hn : n + 2 ≤ X) :
    n * (1000000 * X ^ 2 + 4) + 10000 * X ^ 2 + 200 * X ≤ 3000000 * X ^ 3 := by
  have h1 : n * (1000000 * X ^ 2 + 4) ≤ X * (1000000 * X ^ 2 + 4) := Nat.mul_le_mul_right _ (by omega)
  have h2 : 1 ≤ X := by omega
  nlinarith

theorem cntPass_cost (X n lw rc lc no : ℕ) (hlw : lw ≤ X) (hn : n + 2 ≤ X) (hrc : rc ≤ 10000 * X ^ 2)
    (hlc : lc + no ≤ X) :
    3 * lw + 1 + 1 + (18 * n + 3 + 1 + (n * (1000000 * X ^ 2 + 4) + 1 + 1 + (rc + 1 +
      (5 * (lc + no) + 1 + 1 + (18 * n + 3 + 1 + (5 * n + 1)))))) ≤ 3000000 * X ^ 3 := by
  have := cnt_arith X n hn
  omega

set_option maxHeartbeats 1600000 in

theorem countPass_spec (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (σ : WState 4 nrH) (hH : HeadPost o B σ)
    (hcap : 20 * sizeS o B + 100 ≤ cap) :
    ∃ τ, WExec cap countPass σ τ (cntCost (sizeS o B)) ∧ CntPost o B τ := by
  obtain ⟨hzC, hzB, hzq, hwh, hlb, hdl, hnCw⟩ := sizes_le o B
  have hS : sizeS o B = o.word.length + (PCPPNative.descriptor B).length + q + 1 := rfl
  have hv : ∀ u, σ.val (regH u) = V1 o B u := hH.val
  have e1 := wclear_spec cap (regH .cdW) (natWord o.circuit.nodes.length).length σ (by rw [hv]; rfl) (by rw [hv]; simp only [V1]; omega)
  set σ1 := σ.setv (regH .cdW) 0 with hσ1
  have e2 := addTo_spec cap (regH .nC) (regH .iC) (regH .t) (by simp) (by simp) (by simp) σ1
    (by simp [σ1, Function.update_apply, hv, V1]) (by simp [σ1, Function.update_apply, hv, V1]; omega)
    (by simp [σ1, Function.update_apply, hv, V1]; omega)
  rw [show σ1.val (regH .iC) + σ1.val (regH .nC) = o.circuit.nodes.length by simp [σ1, Function.update_apply, hv, V1]] at e2
  set σ2 := σ1.setv (regH .iC) o.circuit.nodes.length with hσ2
  have hI0 : CntInv o B 0 σ2 := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [σ2, σ1, hH.stW]
    · simp [σ2, σ1, hH.stD]
    · simp [σ2, σ1, hH.stO]
    · simp [σ2, σ1, hH.stF]
    · simp [σ2, σ1, hH.stL]
    · simp [σ2, σ1, hH.shW, pC, lenC]
    · simp [σ2, σ1, hH.shD, pB]
    · simp [σ2, σ1, hH.shO]
    · simp [σ2, σ1, hH.shF]
    · simp [σ2, σ1, hH.shL]
    · intro u; simp [σ2, σ1, Function.update_apply, hv, cntV, lenC, kOf]
      split_ifs <;> simp_all [V1]
    · simp [σ2, σ1, hH.cell]
  obtain ⟨τ3, e3, hI3, hi3⟩ := UnionMachine.Round.wloopE cap (regH .iC) countBody (cntIter (sizeS o B)) o.circuit.nodes.length
    (fun j τ => CntInv o B j τ) (by omega)
    (fun j hj τ hτ hiC => countStep cap o B j hj τ hτ hcap) σ2 hI0 (by simp [σ2])
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, hv3, hc3⟩ := hI3
  have hv3' : ∀ u, τ3.val (regH u) = cntV o B o.circuit.nodes.length u := hv3
  have hlenC : lenC o o.circuit.nodes.length = (o.circuit.nodes.flatMap oracleNodeWord).length := by simp [lenC]
  have hoC := o.circuit.output.isLt
  have e4 := readEx_spec cap sW RW (regH .pk) (regH .pt) (regH .oC) (rdRegs .cdW .oC (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)) τ3
    (natWord o.ell ++ natWord o.circuit.nodes.length ++ o.circuit.nodes.flatMap oracleNodeWord) [] o.circuit.output.val
    (by rw [a1, word_eq]; simp only [List.append_nil]) (by rw [a6, hlenC]; simp [pC]; ring) (famZero _ _ (fun r => by rw [hv3']; simp [cntV, V1]))
    (by rw [hv3']; simp [cntV, V1]) (by rw [hv3']; simp [cntV, V1]) (by rw [hv3']; simp [cntV, V1])
    (by have : τ3.val (RW .cd) = lenC o o.circuit.nodes.length := by simp [RW, hv3', cntV]
        rw [this]; have := lenC_le o o.circuit.nodes.length; omega)
  set σ4 := ((τ3.seth sW ((natWord o.ell ++ natWord o.circuit.nodes.length ++ o.circuit.nodes.flatMap oracleNodeWord).length +
    (natWord o.circuit.output.val).length)).setv (RW .cd) (τ3.val (RW .cd) + (natWord o.circuit.output.val).length)).setv
    (regH .oC) o.circuit.output.val with hσ4
  have h4cd : σ4.val (regH .cdW) = lenC o o.circuit.nodes.length + (natWord o.circuit.output.val).length := by
    simp [σ4, RW, hv3', cntV]
  have e5 := wrewind_spec cap sW (regH .cdW) (lenC o o.circuit.nodes.length + (natWord o.circuit.output.val).length) σ4 h4cd
    (by rw [h4cd]; have := lenC_le o o.circuit.nodes.length; have : (natWord o.circuit.output.val).length ≤ o.word.length := by
          rw [word_eq]; simp only [List.length_append]; omega
        omega)
  set σ5 := (σ4.setv (regH .cdW) 0).seth sW (σ4.sh sW - (lenC o o.circuit.nodes.length + (natWord o.circuit.output.val).length))
    with hσ5
  have e6 := addTo_spec cap (regH .nC) (regH .sb) (regH .t) (by simp) (by simp) (by simp) σ5
    (by simp [σ5, σ4, Function.update_apply, hv3', cntV, V1]) (by simp [σ5, σ4, Function.update_apply, hv3', cntV, V1]; omega)
    (by simp [σ5, σ4, Function.update_apply, hv3', cntV, V1]; omega)
  rw [show σ5.val (regH .sb) + σ5.val (regH .nC) = o.circuit.nodes.length by simp [σ5, σ4, Function.update_apply, hv3', cntV, V1]] at e6
  set σ6 := σ5.setv (regH .sb) o.circuit.nodes.length with hσ6
  have e7 := wrewind_spec cap sF (regH .sb) o.circuit.nodes.length σ6 (by simp [σ6]) (by simp [σ6]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have c2 : σ1.val (regH .nC) = o.circuit.nodes.length := by simp [σ1, hv, V1]
    have c6 : σ5.val (regH .nC) = o.circuit.nodes.length := by simp [σ5, σ4, Function.update_apply, hv3', cntV, V1]
    rw [c2, c6]
    have hr : readCost o.circuit.output.val ≤ 10000 * (sizeS o B + 2) ^ 2 := by
      unfold readCost; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have hlc := lenC_le o o.circuit.nodes.length
    have hno : (natWord o.circuit.output.val).length ≤ o.word.length := by
      rw [word_eq]; simp only [List.length_append]; omega
    have hsum : lenC o o.circuit.nodes.length + (natWord o.circuit.output.val).length ≤ o.word.length := by
      rw [hlenC, word_eq]; simp only [List.length_append]; omega
    unfold cntCost cntIter
    exact cntPass_cost _ _ _ _ _ _ (by omega) (by omega) hr (by omega)
  · simp [σ6, σ5, σ4, a1]
  · simp [σ6, σ5, σ4, a2]
  · simp [σ6, σ5, σ4, a3]
  · simp [σ6, σ5, σ4, a4, ofl]
  · simp [σ6, σ5, σ4, a5]
  · have := hlenC
    simp [σ6, σ5, σ4, pC] at this ⊢; omega
  · simp [σ6, σ5, σ4, a7]
  · simp [σ6, σ5, σ4, a8]
  · simp [σ6, σ5, σ4, a9]
  · simp [σ6, σ5, σ4, a10]
  · intro u; simp [σ6, σ5, σ4, Function.update_apply, hv3', cntV, V2, RW]
    split_ifs <;> simp_all [V1]
  · simp [σ6, σ5, σ4, hc3]

end NearCubicGates.Close.Succinct.SubstMachine
