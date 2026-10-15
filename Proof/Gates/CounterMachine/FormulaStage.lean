import Proof.Gates.CounterMachine.FormulaCost
import Proof.Gates.CounterMachine.FormulaSeek

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ} (cap : ℕ)

def encI (zs : List ℤ) : List Bool := (zs.map fun z => enc true (Interfaces.intWord z)).flatten

theorem encI_append (a b : List ℤ) : encI (a ++ b) = encI a ++ encI b := by simp [encI]

theorem encI_flatten (xs : List (List ℤ)) : encI xs.flatten = xs.flatMap encI := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatten_cons, encI_append, ih, List.flatMap_cons]

theorem linToks_length (o : ℕ) (as : List ℤ) : (linToks o as).length = 4 * as.length + 1 := by
  have e : ((List.range as.length).map fun t => [Tok.const (as.getD t 0), Tok.var (o + t), Tok.mul]).flatten.length =
      3 * as.length := by
    rw [List.length_flatten, List.map_map]
    have : (List.map (List.length ∘ fun t => [Tok.const (as.getD t 0), Tok.var (o + t), Tok.mul])
        (List.range as.length)) = List.replicate as.length 3 := by
      apply List.ext_getElem <;> simp
    rw [this, List.sum_replicate]; ring
  unfold linToks
  rw [List.length_append, List.length_append, e, List.length_singleton, List.length_replicate]; ring

section Stage
variable (S CW : Fin (ns + 1)) (F : Fin 24 ↪ Fin nr)

/-- The printer's register file: the first sixteen of `F`. -/
def Rf : Fin 16 ↪ Fin nr := (Fin.castLEEmb (by norm_num : 16 ≤ 24)).trans F

theorem Rf_apply (i : Fin 16) : Rf F i = F (Fin.castLE (by norm_num) i) := rfl

/-- After printing the tokens `ts` to `S`, counted in `F 16`. -/
def emitT (σ : WState ns nr) (ts : List Tok) : WState ns nr :=
  (appendO σ S (F 7) (marks (ts.flatMap tokWord))).setv (F 16) (σ.val (F 16) + ts.length)

theorem emitT_append (σ : WState ns nr) (a b : List Tok) :
    emitT S F (emitT S F σ a) b = emitT S F σ (a ++ b) := by
  have h716 : F 7 ≠ F 16 := F.injective.ne (by decide)
  unfold emitT
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp [appendO, List.flatMap_append, marksApp]; ring
    · simp [appendO, Function.update_of_ne hj]
  · funext j; by_cases hj : j = S
    · subst hj; simp [appendO, List.flatMap_append, marksApp]
    · simp [appendO, Function.update_of_ne hj]
  · funext r; by_cases r1 : r = F 16
    · subst r1; simp [appendO, Function.update_of_ne h716.symm]; ring
    · by_cases r2 : r = F 7
      · subst r2; simp [appendO, Function.update_of_ne h716, List.flatMap_append, marksApp]; ring
      · simp [appendO, Function.update_of_ne r1, Function.update_of_ne r2]
  · simp [appendO]

theorem emitT_nil (σ : WState ns nr) (ho : σ.sh S = (σ.st S).length) : emitT S F σ [] = σ := by
  unfold emitT
  simp only [List.flatMap_nil, List.length_nil, Nat.add_zero]
  rw [show marks ([] : List Bool) = [] by simp [marks], appendO_nil σ S (F 7) ho, wsetv_same]

/-- The token printer at rest. -/
structure TRest (σ : WState ns nr) : Prop where
  pr : PrRest S (Rf F) σ
  z9 : σ.val (F 9) = 0
  z10 : σ.val (F 10) = 0
  z17 : σ.val (F 17) = 0
  z18 : σ.val (F 18) = 0
  z19 : σ.val (F 19) = 0

theorem TRest.zero {σ : WState ns nr} (h : TRest S F σ) (i : Fin 24)
    (hi : i ∈ ([0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 17, 18, 19] : List (Fin 24))) : σ.val (F i) = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.pr.zero 0 (by decide)
  · exact h.pr.zero 1 (by decide)
  · exact h.pr.zero 2 (by decide)
  · exact h.pr.zero 3 (by decide)
  · exact h.pr.zero 4 (by decide)
  · exact h.pr.zero 5 (by decide)
  · exact h.pr.zero 6 (by decide)
  · exact h.pr.zero 8 (by decide)
  · exact h.z9
  · exact h.z10
  · exact h.z17
  · exact h.z18
  · exact h.z19

theorem TRest.of_zero {σ : WState ns nr} (ho : σ.sh S = (σ.st S).length)
    (hz : ∀ i : Fin 24, i ∈ ([0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 17, 18, 19] : List (Fin 24)) → σ.val (F i) = 0) :
    TRest S F σ :=
  ⟨⟨ho, fun i hi => by
    rw [Rf_apply]
    exact hz _ (by revert i; decide)⟩, hz 9 (by decide), hz 10 (by decide), hz 17 (by decide), hz 18 (by decide),
    hz 19 (by decide)⟩

theorem TRest.emitT {σ : WState ns nr} (h : TRest S F σ) (ts : List Tok) : TRest S F (emitT S F σ ts) := by
  refine TRest.of_zero S F (by simp [CounterMachine.emitT, appendO, h.pr.out]) (fun i hi => ?_)
  have k : i ≠ 7 ∧ i ≠ 16 := by revert i; decide
  have h7 : F i ≠ F 7 := F.injective.ne k.1
  have h16 : F i ≠ F 16 := F.injective.ne k.2
  simp [CounterMachine.emitT, appendO, Function.update_of_ne h7, Function.update_of_ne h16]
  exact h.zero S F i hi

/-! ## Skipping whole blocks -/

/-- Step over `F 17` blocks of `G` (in `Gr`) integers on `CW`. -/
def skipB (Gr : Fin nr) : WM ns nr :=
  listLoop (F 17) (.seq (copyR Gr (F 18) (F 8)) (listLoop (F 18) (skipInt true CW (F 1) (F 2))))

def blockCost (G : ℕ) (b : List ℤ) : ℕ := 18 * G + 3 + 1 + ((b.map fun z => skipIntCost z + 4).sum + 1)

theorem skipB_spec (Gr : Fin nr) (hG : ∀ i : Fin 24, F i ≠ Gr) (G : ℕ) (blocks : List (List ℤ))
    (hb : ∀ b ∈ blocks, b.length = G) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st CW = pre ++ encI blocks.flatten ++ rest) (hsh : σ.sh CW = pre.length)
    (hT1 : σ.val (F 17) = blocks.length) (hT2 : σ.val (F 18) = 0) (h1 : σ.val (F 1) = 0) (h2 : σ.val (F 2) = 0)
    (h8 : σ.val (F 8) = 0) (hGv : σ.val Gr = G) (hcap1 : blocks.length ≤ cap) (hcapG : G ≤ cap)
    (hz : ∀ b ∈ blocks, ∀ z ∈ b, natBitLength z.natAbs + 2 ≤ cap) :
    WExec cap (skipB CW F Gr) σ ((σ.setv (F 17) 0).seth CW (pre.length + (encI blocks.flatten).length))
      ((blocks.map fun b => blockCost G b + 4).sum + 1) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  have hfl := encI_flatten blocks
  rw [hfl] at hst ⊢
  refine listLoop_spec cap CW (F 17) _ encI (blockCost G)
    (fun τ => τ.val (F 1) = 0 ∧ τ.val (F 2) = 0 ∧ τ.val (F 8) = 0 ∧ τ.val (F 18) = 0 ∧ τ.val Gr = G)
    (fun τ x h => by simpa using h)
    (fun τ x h => by
      simp only [WState.setv_val]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (hne (by decide))]; exact h.1
      · rw [Function.update_of_ne (hne (by decide))]; exact h.2.1
      · rw [Function.update_of_ne (hne (by decide))]; exact h.2.2.1
      · rw [Function.update_of_ne (hne (by decide))]; exact h.2.2.2.1
      · rw [Function.update_of_ne (hG 17).symm]; exact h.2.2.2.2)
    blocks ?_ pre rest σ ⟨h1, h2, h8, hT2, hGv⟩ hst hsh hT1 hcap1
  intro b hbm pre' rest' τ hτ hst' hsh'
  obtain ⟨t1, t2, t8, t18, tG⟩ := hτ
  have e1 := copyR_spec cap (v := Gr) (d := F 18) (t := F 8) (hG 18).symm (hG 8).symm (hne (by decide)) τ t8
    (by rw [t18, tG]; omega)
  rw [t18, tG, Nat.zero_add] at e1
  set τ1 := τ.setv (F 18) G with hτ1
  have e2 := listLoop_spec cap CW (F 18) (skipInt true CW (F 1) (F 2)) (fun z => enc true (Interfaces.intWord z))
    skipIntCost (fun υ => υ.val (F 1) = 0 ∧ υ.val (F 2) = 0)
    (fun υ x h => by simpa using h)
    (fun υ x h => by
      simp only [WState.setv_val]
      exact ⟨by rw [Function.update_of_ne (hne (by decide))]; exact h.1,
        by rw [Function.update_of_ne (hne (by decide))]; exact h.2⟩)
    b (fun z hzb pre'' rest'' υ hυ hst'' hsh'' => by
      have := skipInt_spec cap true CW (F 1) (F 2) (hne (by decide)) z pre'' rest'' υ hst'' hsh'' hυ.1 hυ.2
        (hz b hbm z hzb)
      simpa [stp, enc_length] using this)
    pre' rest' τ1
    ⟨by simp [hτ1, Function.update_of_ne (hne (show (1 : Fin 24) ≠ 18 by decide)), t1],
     by simp [hτ1, Function.update_of_ne (hne (show (2 : Fin 24) ≠ 18 by decide)), t2]⟩
    (by simp only [hτ1, WState.setv_st]; rw [hst']; rfl) (by simp [hτ1, hsh']) (by simp [hτ1, hb b hbm])
    (by rw [hb b hbm]; exact hcapG)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by unfold blockCost; omega)
  apply WState.eq
  · funext j; by_cases hj : j = CW
    · subst hj; simp [hτ1, encI, Function.comp_def]
    · simp [hτ1, Function.update_of_ne hj]
  · simp [hτ1]
  · funext r; by_cases hr : r = F 18
    · subst hr; simp [hτ1, t18]
    · simp [hτ1, Function.update_of_ne hr]
  · simp [hτ1]

/-! ## The stage printer -/

/-- `F 16 += 4·G + 1` (`G` in `Gr`). -/
def countLin (Gr : Fin nr) : WM ns nr :=
  .seq (copyR Gr (F 16) (F 8)) (.seq (copyR Gr (F 16) (F 8)) (.seq (copyR Gr (F 16) (F 8))
    (.seq (copyR Gr (F 16) (F 8)) (.inc (F 16)))))

theorem countLin_spec (Gr : Fin nr) (hG : ∀ i : Fin 24, F i ≠ Gr) (σ : WState ns nr) (h8 : σ.val (F 8) = 0)
    (hcap : σ.val (F 16) + 4 * σ.val Gr + 1 ≤ cap) :
    WExec cap (countLin F Gr) σ (σ.setv (F 16) (σ.val (F 16) + (4 * σ.val Gr + 1))) (4 * (18 * σ.val Gr + 3) + 7) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  have h168 : F 16 ≠ F 8 := hne (by decide)
  have vG : ∀ (τ : WState ns nr) x, (τ.setv (F 16) x).val Gr = τ.val Gr := fun τ x => by
    simp [Function.update_of_ne (hG 16).symm]
  have v8 : ∀ (τ : WState ns nr) x, (τ.setv (F 16) x).val (F 8) = τ.val (F 8) := fun τ x => by
    simp [Function.update_of_ne h168.symm]
  set g := σ.val Gr
  set c0 := σ.val (F 16)
  have e1 := copyR_spec cap (hG 16).symm (hG 8).symm h168 σ h8 (by omega)
  have e2 := copyR_spec cap (hG 16).symm (hG 8).symm h168 (σ.setv (F 16) (c0 + g)) (by rw [v8]; exact h8)
    (by rw [vG]; simp; omega)
  rw [vG] at e2; simp only [WState.setv_val, Function.update_self] at e2
  have e3 := copyR_spec cap (hG 16).symm (hG 8).symm h168 ((σ.setv (F 16) (c0 + g)).setv (F 16) (c0 + g + g))
    (by rw [v8, v8]; exact h8) (by rw [vG, vG]; simp; omega)
  rw [vG, vG] at e3; simp only [WState.setv_val, Function.update_self] at e3
  have e4 := copyR_spec cap (hG 16).symm (hG 8).symm h168
    (((σ.setv (F 16) (c0 + g)).setv (F 16) (c0 + g + g)).setv (F 16) (c0 + g + g + g))
    (by rw [v8, v8, v8]; exact h8) (by rw [vG, vG, vG]; simp; omega)
  rw [vG, vG, vG] at e4; simp only [WState.setv_val, Function.update_self] at e4
  have e5 := WExec.inc (cap := cap) (F 16)
    ((((σ.setv (F 16) (c0 + g)).setv (F 16) (c0 + g + g)).setv (F 16) (c0 + g + g + g)).setv (F 16)
      (c0 + g + g + g + g)) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by omega)
  apply WState.eq <;> simp
  funext r; by_cases hr : r = F 16
  · subst hr; simp; ring
  · simp [Function.update_of_ne hr]

/-- **The stage printer**: the tokens of `linF o G (blocks[s])` (`linToks`), counted. -/
def stP (Gr off LB Sj : Fin nr) : WM ns nr :=
  .seq (copyR Sj (F 17) (F 8))
  (.seq (skipB CW F Gr)
  (.seq (copyR off (F 9) (F 8))
  (.seq (linP S CW (Rf F) Gr)
  (.seq (WM.clear (F 9))
  (.seq (copyR LB (F 19) (F 8))
  (.seq (WM.rewind CW (F 19)) (countLin F Gr)))))))

theorem flatten_split (blocks : List (List ℤ)) (s : ℕ) (hs : s < blocks.length) :
    blocks.flatten = (blocks.take s).flatten ++ blocks[s] ++ (blocks.drop (s + 1)).flatten := by
  conv_lhs => rw [← List.take_append_drop s blocks]
  rw [List.flatten_append, List.drop_eq_getElem_cons hs, List.flatten_cons, List.append_assoc]

theorem take_succ_flatten (blocks : List (List ℤ)) (s : ℕ) (hs : s < blocks.length) :
    (blocks.take (s + 1)).flatten = (blocks.take s).flatten ++ blocks[s] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hs, List.flatten_append]
  simp

theorem stP_spec (hSC : S ≠ CW) (Gr off LB Sj : Fin nr) (hG : ∀ i : Fin 24, F i ≠ Gr) (ho : ∀ i : Fin 24, F i ≠ off)
    (hL : ∀ i : Fin 24, F i ≠ LB) (hJ : ∀ i : Fin 24, F i ≠ Sj)
    (G s o lb : ℕ) (blocks : List (List ℤ)) (hb : ∀ b ∈ blocks, b.length = G) (hs : s < blocks.length)
    (rest : List Bool) (σ : WState ns nr) (h : TRest S F σ)
    (hst : σ.st CW = encI blocks.flatten ++ rest) (hsh : σ.sh CW = 0)
    (hGv : σ.val Gr = G) (hov : σ.val off = o) (hLv : σ.val LB = lb) (hJv : σ.val Sj = s)
    (hlb : (encI (blocks.take (s + 1)).flatten).length ≤ lb)
    (V : ℕ) (hV : σ.val (F 7) + (marks ((linToks o blocks[s]).flatMap tokWord)).length ≤ V)
    (hcap : V + 7 * (o + G) + 40 ≤ cap) (hcs : s ≤ cap) (hcl : lb ≤ cap) (hcG : σ.val (F 16) + 4 * G + 1 ≤ cap)
    (hz : ∀ b ∈ blocks, ∀ z ∈ b, natBitLength z.natAbs + 2 ≤ cap) :
    WExec cap (stP S CW F Gr off LB Sj) σ (emitT S F σ (linToks o blocks[s]))
      (18 * s + 3 + 1 + ((((blocks.take s).map fun b => blockCost G b + 4).sum + 1) + 1 + (18 * o + 3 + 1 +
        (linCost o blocks[s] + 1 + (3 * (o + G) + 1 + 1 + (18 * lb + 3 + 1 + (5 * lb + 1 + 1 +
          (4 * (18 * G + 3) + 7)))))))) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  have hz0 := h.zero S F
  have hsplit := flatten_split blocks s hs
  set b := blocks[s] with hbdef
  have hbl : b.length = G := hb b (List.getElem_mem hs)
  have hts : (blocks.take s).length = s := by simp; omega
  -- 1. F 17 := s
  have e1 := copyR_spec cap (v := Sj) (d := F 17) (t := F 8) (hJ 17).symm (hJ 8).symm (hne (by decide)) σ
    (hz0 8 (by decide)) (by rw [hz0 17 (by decide), hJv]; omega)
  rw [hz0 17 (by decide), hJv, Nat.zero_add] at e1
  set σ1 := σ.setv (F 17) s with hσ1
  -- 2. skip s blocks
  have e2 := skipB_spec cap CW F Gr hG G (blocks.take s) (fun x hx => hb x (List.mem_of_mem_take hx)) []
    (encI b ++ encI (blocks.drop (s + 1)).flatten ++ rest) σ1
    (by simp only [hσ1, WState.setv_st]; rw [hst, hsplit, encI_append, encI_append]; simp [List.append_assoc])
    (by simp [hσ1, hsh]) (by simp [hσ1, hts])
    (by simp [hσ1, Function.update_of_ne (hne (show (18 : Fin 24) ≠ 17 by decide))]; exact hz0 18 (by decide))
    (by simp [hσ1, Function.update_of_ne (hne (show (1 : Fin 24) ≠ 17 by decide))]; exact hz0 1 (by decide))
    (by simp [hσ1, Function.update_of_ne (hne (show (2 : Fin 24) ≠ 17 by decide))]; exact hz0 2 (by decide))
    (by simp [hσ1, Function.update_of_ne (hne (show (8 : Fin 24) ≠ 17 by decide))]; exact hz0 8 (by decide))
    (by simp [hσ1, Function.update_of_ne (hG 17).symm, hGv]) (by omega) (by omega)
    (fun x hx z hzx => hz x (List.mem_of_mem_take hx) z hzx)
  set P1 := (encI (blocks.take s).flatten).length with hP1
  simp only [List.length_nil, Nat.zero_add] at e2
  set σ2 := (σ1.setv (F 17) 0).seth CW P1 with hσ2
  have v2 : ∀ r, r ≠ F 17 → σ2.val r = σ.val r := fun r hr => by simp [hσ2, hσ1, Function.update_of_ne hr]
  have v217 : σ2.val (F 17) = 0 := by simp [hσ2]
  -- 3. F 9 := o
  have e3 := copyR_spec cap (v := off) (d := F 9) (t := F 8) (ho 9).symm (ho 8).symm (hne (by decide)) σ2
    (by rw [v2 _ (hne (by decide))]; exact hz0 8 (by decide))
    (by rw [v2 _ (hne (by decide)), v2 _ (ho 17).symm, hz0 9 (by decide), hov]; omega)
  rw [v2 _ (hne (by decide)), v2 _ (ho 17).symm, hz0 9 (by decide), hov, Nat.zero_add] at e3
  set σ3 := σ2.setv (F 9) o with hσ3
  have v3 : ∀ r, r ≠ F 17 → r ≠ F 9 → σ3.val r = σ.val r := fun r h1 h2 => by
    simp [hσ3, Function.update_of_ne h2, v2 r h1]
  -- 4. the tokens
  have hpr3 : PrRest S (Rf F) σ3 := ⟨by simp [hσ3, hσ2, hσ1, h.pr.out, Function.update_of_ne hSC], fun i hi => by
    rw [Rf_apply, v3 _ (hne (by revert i; decide)) (hne (by revert i; decide))]
    exact h.pr.zero i hi⟩
  have e4 := linP_spec cap S CW (Rf F) hSC.symm Gr (fun i _ => by rw [Rf_apply]; exact hG _) o b
    (encI (blocks.take s).flatten)
    (encI (blocks.drop (s + 1)).flatten ++ rest) σ3 hpr3
    (by simp only [hσ3, hσ2, hσ1, WState.setv_st, WState.seth_st]; rw [hst, hsplit, encI_append, encI_append]
        simp [encI, P1, List.append_assoc])
    (by simp [hσ3, hσ2, hP1]) (by rw [Rf_apply]; simp [hσ3]) (by
      rw [Rf_apply]; exact (v3 _ (hne (by decide)) (hne (by decide))).trans (hz0 10 (by decide)))
    (by rw [v3 _ (hG 17).symm (hG 9).symm, hGv, hbl]) V
    (by rw [Rf_apply, v3 _ (hne (by decide)) (hne (by decide))]; exact hV) (by rw [hbl]; exact hcap)
  have hencb : (b.map fun a => enc true (Interfaces.intWord a)).flatten = encI b := rfl
  rw [hencb] at e4
  set W := marks ((linToks o b).flatMap tokWord) with hW
  set P2 := P1 + (encI b).length with hP2
  set σ4 := ((appendO σ3 S (Rf F 7) W).seth CW P2).setv (Rf F 9) (o + b.length) with hσ4
  have hR7 : Rf F 7 = F 7 := rfl
  have hR9 : Rf F 9 = F 9 := rfl
  -- 5. clear F 9
  have e5 := wclear_spec cap (F 9) (o + b.length) σ4 (by simp [hσ4, hR9]) (by simp [hσ4, hR9]; omega)
  set σ5 := σ4.setv (F 9) 0 with hσ5
  have v5 : ∀ r, r ≠ F 17 → r ≠ F 7 → σ5.val r = σ.val r := fun r h1 h7 => by
    by_cases h9 : r = F 9
    · subst h9; simp [hσ5]; exact (hz0 9 (by decide)).symm
    · simp [hσ5, hσ4, hR9, hR7, appendO, Function.update_of_ne h9, Function.update_of_ne h7, v3 r h1 h9]
  -- 6. rewind CW
  have e6 := copyR_spec cap (v := LB) (d := F 19) (t := F 8) (hL 19).symm (hL 8).symm (hne (by decide)) σ5
    (by rw [v5 _ (hne (by decide)) (hne (by decide))]; exact hz0 8 (by decide))
    (by rw [v5 _ (hne (by decide)) (hne (by decide)), v5 _ (hL 17).symm (hL 7).symm, hz0 19 (by decide), hLv]
        omega)
  rw [v5 _ (hne (by decide)) (hne (by decide)), v5 _ (hL 17).symm (hL 7).symm, hz0 19 (by decide), hLv,
    Nat.zero_add] at e6
  set σ6 := σ5.setv (F 19) lb with hσ6
  have e7 := wrewind_spec cap CW (F 19) lb σ6 (by simp [hσ6]) (by simp [hσ6]; omega)
  have hP2lb : P2 ≤ lb := by
    have := take_succ_flatten blocks s hs
    rw [this, encI_append, List.length_append] at hlb; omega
  have hsh6 : σ6.sh CW = P2 := by simp [hσ6, hσ5, hσ4, appendO, Function.update_of_ne hSC.symm]
  rw [hsh6, show P2 - lb = 0 by omega] at e7
  set σ7 := (σ6.setv (F 19) 0).seth CW 0 with hσ7
  -- 7. count
  have v7 : ∀ r, r ≠ F 17 → r ≠ F 7 → r ≠ F 19 → σ7.val r = σ.val r := fun r h1 h7 h19 => by
    simp [hσ7, hσ6, Function.update_of_ne h19, v5 r h1 h7]
  have e8 := countLin_spec cap F Gr hG σ7
    (by rw [v7 _ (hne (by decide)) (hne (by decide)) (hne (by decide))]; exact hz0 8 (by decide))
    (by rw [v7 _ (hne (by decide)) (hne (by decide)) (hne (by decide)), v7 _ (hG 17).symm (hG 7).symm (hG 19).symm,
        hGv]; exact hcG)
  rw [v7 _ (hne (by decide)) (hne (by decide)) (hne (by decide)), v7 _ (hG 17).symm (hG 7).symm (hG 19).symm, hGv]
    at e8
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ (by rw [hbl] <;> omega)
  have hlt : (linToks o b).length = 4 * G + 1 := by rw [linToks_length, hbl]
  have h7eq : σ7 = appendO σ S (F 7) W := by
    apply WState.eq
    · funext j; by_cases hj : j = CW
      · subst hj; simp [hσ7, appendO, Function.update_of_ne hSC.symm, hsh]
      · by_cases hjS : j = S
        · subst hjS; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj, hR7]
        · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjS]
    · funext j; by_cases hjS : j = S
      · subst hjS; simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hSC, hR7]
      · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hjS]
    · funext r
      by_cases r7 : r = F 7
      · subst r7
        have v37 : σ3.val (F 7) = σ.val (F 7) := v3 _ (hne (by decide)) (hne (by decide))
        simp only [hσ7, hσ6, hσ5, hσ4, WState.seth_val, WState.setv_val, hR7, hR9,
          Function.update_of_ne (hne (show (7 : Fin 24) ≠ 19 by decide)),
          Function.update_of_ne (hne (show (7 : Fin 24) ≠ 9 by decide)), Function.update_self]
        simp [appendO, v37]
      · rw [show (appendO σ S (F 7) W).val r = σ.val r by simp [appendO, Function.update_of_ne r7]]
        by_cases r19 : r = F 19
        · subst r19; simp [hσ7]; exact (hz0 19 (by decide)).symm
        · by_cases r17 : r = F 17
          · subst r17
            simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, appendO, hR7, hR9,
              Function.update_of_ne (hne (show (17 : Fin 24) ≠ 19 by decide)),
              Function.update_of_ne (hne (show (17 : Fin 24) ≠ 9 by decide)),
              Function.update_of_ne (hne (show (17 : Fin 24) ≠ 7 by decide))]
            exact (hz0 17 (by decide)).symm
          · exact v7 r r17 r7 r19
    · simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO]
  unfold emitT
  rw [← h7eq, hlt]

end Stage

end NearCubicGates.Close.CounterMachine
