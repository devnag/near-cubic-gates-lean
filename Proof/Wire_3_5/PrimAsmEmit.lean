import Proof.Wire_3_5.PrimAsmFiltRec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec

variable {ns nr : ℕ} (cap : ℕ)

/-- Emit a constant word. -/
def emitW (O : Fin (ns + 1)) (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | b :: u => .seq (emitC O OP b) (emitW O OP u)

theorem emitW_spec (O : Fin (ns + 1)) (OP : Fin nr) :
    ∀ (u : List Bool) (σ : WState ns nr), σ.sh O = (σ.st O).length → σ.val OP + u.length ≤ cap →
      WExec cap (emitW O OP u) σ (appendO σ O OP u) (8 * u.length)
  | [], σ, _, _ => by rw [appendO_nil]; exact WExec.skip σ
  | b :: u, σ, ho, hc => by
    have h1 := emitC_spec cap O OP b σ ho (by simp at hc; omega)
    have h2 := emitW_spec O OP u (((σ.sets O ((σ.st O) ++ [b])).seth O (σ.sh O + 1)).setv OP (σ.val OP + 1))
      (by simp [ho]) (by simp at hc ⊢; omega)
    have e : appendO (((σ.sets O ((σ.st O) ++ [b])).seth O (σ.sh O + 1)).setv OP (σ.val OP + 1)) O OP u =
        appendO σ O OP (b :: u) := by
      rw [show b :: u = [b] ++ u from rfl, ← appendO_append]
      congr 1
    rw [e] at h2
    exact WExec.mono (WExec.seq h1 h2) (by simp; omega)

/-- `K` copies of `u`, consuming `K`. -/
def repW (O : Fin (ns + 1)) (OP K : Fin nr) (u : List Bool) : WM ns nr := .whr K (.seq (.dec K) (emitW O OP u))

theorem repW_spec (O : Fin (ns + 1)) (OP K : Fin nr) (hK : K ≠ OP) (u : List Bool) (n : ℕ) (σ : WState ns nr)
    (hKn : σ.val K = n) (ho : σ.sh O = (σ.st O).length) (hc : σ.val OP + n * u.length ≤ cap) (hn : n ≤ cap) :
    WExec cap (repW O OP K u) σ ((appendO σ O OP (reps n u)).setv K 0) (n * (8 * u.length + 4) + 1) := by
  let S : ℕ → WState ns nr := fun k => (appendO σ O OP (reps k u)).setv K (n - k)
  have hS0 : S 0 = σ := by
    simp only [S, reps_zero, appendO_nil, Nat.sub_zero, ← hKn, wsetv_same]
  have hloop := UnionMachine.Round.wloop cap K (emitW O OP u) (8 * u.length) n S
    (fun k _ => by simp [S])
    hn
    (fun k hk => by
      have e1 : (S k).setv K (n - k - 1) = (appendO σ O OP (reps k u)).setv K (n - k - 1) := by
        simp only [S, wsetv_setv]
      rw [e1]
      have hlen : (reps k u).length = k * u.length := by
        unfold reps; simp
      have hk1 : (k + 1) * u.length ≤ n * u.length := Nat.mul_le_mul_right _ (by omega)
      have h := emitW_spec cap O OP u ((appendO σ O OP (reps k u)).setv K (n - k - 1))
        (by simp [ho]) (by simp [Function.update_apply, Ne.symm hK, hlen]; rw [Nat.succ_mul] at hk1; omega)
      refine WExec.cast cap h ?_ le_rfl
      simp only [S]
      rw [← appendO_setv _ O OP K hK, appendO_append, ← reps_succ]
      rw [appendO_setv _ O OP K hK, show n - k - 1 = n - (k + 1) by omega])
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  simp [S]

/-- `A` copies of `u`, keeping `A` (through `K`, `T` at `0`). -/
def repRegW (O : Fin (ns + 1)) (OP A K T : Fin nr) (u : List Bool) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR A K T) (repW O OP K u)

theorem repRegW_spec (O : Fin (ns + 1)) (OP A K T : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T) (hKO : K ≠ OP)
    (u : List Bool) (σ : WState ns nr) (hK : σ.val K = 0) (hT : σ.val T = 0) (ho : σ.sh O = (σ.st O).length)
    (hA : σ.val A ≤ cap) (hc : σ.val OP + σ.val A * u.length ≤ cap) :
    WExec cap (repRegW O OP A K T u) σ (appendO σ O OP (reps (σ.val A) u))
      (18 * σ.val A + 3 + 1 + (σ.val A * (8 * u.length + 4) + 1)) := by
  have h1 := FinalPass.Hash4.wcopyR_spec cap A K T hAK hAT hKT σ hK hT hA
  have h2 := repW_spec cap O OP K hKO u (σ.val A) (σ.setv K (σ.val A)) (by simp) (by simp [ho])
    (by simp [Function.update_apply, Ne.symm hKO]; exact hc) hA
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  rw [← appendO_setv _ O OP K hKO, wsetv_setv, ← hK, wsetv_same]

def copyLoop (O S : Fin (ns + 1)) (OP SP K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (.ifs S (emitW O OP (m2 true)) (emitW O OP (m2 false))) (WM.fwdC S SP)))

theorem copyLoop_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP K : Fin nr) (hKO : K ≠ OP) (hKS : K ≠ SP)
    (hOSP : OP ≠ SP) (w : List Bool) (σ : WState ns nr) (hKn : σ.val K = w.length)
    (hw : ∀ i < w.length, readTapeBit (σ.st S) (σ.sh S + i) = w.getD i false)
    (ho : σ.sh O = (σ.st O).length) (hc : σ.val OP + 4 * w.length ≤ cap) (hsp : σ.val SP + w.length ≤ cap)
    (hn : w.length ≤ cap) :
    WExec cap (copyLoop O S OP SP K) σ
      ((((appendO σ O OP (w.flatMap m2)).seth S (σ.sh S + w.length)).setv SP (σ.val SP + w.length)).setv K 0)
      (w.length * (8 * 4 + 1 + 1 + 5 + 4) + 1) := by
  let S' : ℕ → WState ns nr := fun k =>
    (((appendO σ O OP ((w.take k).flatMap m2)).seth S (σ.sh S + k)).setv SP (σ.val SP + k)).setv K (w.length - k)
  have hS0 : S' 0 = σ := by
    simp only [S', List.take_zero, List.flatMap_nil, appendO_nil, Nat.add_zero, Nat.sub_zero, ← hKn]
    apply WState.eq <;> simp [Function.update_eq_self]
  have hloop := UnionMachine.Round.wloop cap K
    (.seq (.ifs S (emitW O OP (m2 true)) (emitW O OP (m2 false))) (WM.fwdC S SP)) (8 * 4 + 1 + 1 + 5) w.length S'
    (fun k _ => by simp [S'])
    hn
    (fun k hk => by
      set τ := ((((appendO σ O OP ((w.take k).flatMap m2)).seth S (σ.sh S + k)).setv SP (σ.val SP + k)).setv K
        (w.length - k - 1)) with hτ
      have hτS : (S' k).setv K (w.length - k - 1) = τ := by simp only [S', hτ, wsetv_setv]
      rw [hτS]
      have hlt : (w.take k).flatMap m2 = (w.take k).flatMap m2 := rfl
      have hlen : ((w.take k).flatMap m2).length = 4 * k := by
        rw [List.length_flatMap]
        simp only [m2, List.length_cons, List.length_nil]
        rw [List.map_const', List.sum_replicate, List.length_take, min_eq_left (by omega)]
        ring
      have hbit : wbit τ S = w.getD k false := by
        simp only [hτ, wbit]
        simp [hOS.symm, Function.update_apply, hw k hk]
      have hoτ : τ.sh O = (τ.st O).length := by simp [hτ, hOS, ho]
      have hcτ : τ.val OP + (m2 (w.getD k false)).length ≤ cap := by
        simp only [hτ]
        simp [Function.update_apply, Ne.symm hKO, hOSP, hlen, m2]
        omega
      have hE : WExec cap (.ifs S (emitW O OP (m2 true)) (emitW O OP (m2 false))) τ
          (appendO τ O OP (m2 (w.getD k false))) (8 * 4 + 1) := by
        cases hb : w.getD k false
        · rw [hb] at hbit hcτ
          exact WExec.ifsF hbit (emitW_spec cap O OP (m2 false) τ hoτ hcτ)
        · rw [hb] at hbit hcτ
          exact WExec.ifsT hbit (emitW_spec cap O OP (m2 true) τ hoτ hcτ)
      have hF := wfwdC_spec cap S SP (appendO τ O OP (m2 (w.getD k false)))
        (by simp [hτ, Function.update_apply, Ne.symm hKS, Ne.symm hOSP]; omega)
      refine WExec.cast cap (WExec.seq hE hF) ?_ (by omega)
      have htake : (w.take (k + 1)).flatMap m2 = (w.take k).flatMap m2 ++ m2 (w.getD k false) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append,
          List.getD_eq_getElem _ _ hk]
        simp
      simp only [S', hτ, htake]
      apply WState.eq
      · funext j
        by_cases hjS : j = S
        · subst hjS; simp [Function.update_apply, Ne.symm hOS]; try omega
        · by_cases hj : j = O
          · subst hj; simp [Function.update_apply, hjS]; try omega
          · simp [Function.update_apply, hj, hjS]
      · funext j; by_cases hj : j = O
        · subst hj; simp [hOS]
        · simp [Function.update_apply, hj]
      · funext j; by_cases hj : j = K
        · subst hj; simp [Function.update_apply, hKS, hKO]; omega
        · by_cases hjS : j = SP
          · subst hjS; simp [Function.update_apply, hj, Ne.symm hOSP]; omega
          · by_cases hjO : j = OP
            · subst hjO; simp [Function.update_apply, hj, hjS]; omega
            · simp [Function.update_apply, hj, hjS, hjO]
      · simp)
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  simp only [S', List.take_length, Nat.sub_self]

/-! ## Unary increments -/

/-- `r += n`. -/
def incN (r : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | n + 1 => .seq (.inc r) (incN r n)

theorem incN_spec (r : Fin nr) : ∀ (n : ℕ) (σ : WState ns nr), σ.val r + n ≤ cap →
    WExec cap (incN r n) σ (σ.setv r (σ.val r + n)) (4 * n)
  | 0, σ, _ => by simp only [Nat.add_zero, wsetv_same]; exact WExec.skip σ
  | n + 1, σ, h => by
    have h1 := WExec.inc (cap := cap) r σ (by omega)
    have h2 := incN_spec r n (σ.setv r (σ.val r + 1)) (by simp; omega)
    rw [wsetv_setv] at h2
    simp only [WState.setv_val, Function.update_self] at h2
    rw [show σ.val r + 1 + n = σ.val r + (n + 1) by omega] at h2
    exact WExec.mono (WExec.seq h1 h2) (by omega)

/-! ## One label -/

abbrev LReg (nr : ℕ) := Fin 13 ↪ Fin nr

section Label
variable (O : Fin (ns + 1)) (R : LReg nr)

theorem Rne {i j : Fin 13} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

/-- The multiply-add registers `(a, b, c, t, w) = (R4K, G, LAB, T, W)`. -/
def mR : Fin 5 ↪ Fin 13 := ⟨![5, 2, 8, 9, 10], by decide⟩

/-- One label `lab = GI + R4K·G`: `CAP1 += 2·lab + 10`, emit `labE lab`. -/
def labOne : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 6) (R 8) (R 9))
    (.seq (UnaryArith.mulAddW (mR.trans R))
      (.seq (ParseNat.addTo (R 8) (R 11) (R 9)) (.seq (ParseNat.addTo (R 8) (R 11) (R 9))
        (.seq (incN (R 11) 10) (.seq (repW O (R 0) (R 8) (m2 true)) (emitW O (R 0) (m2 false)))))))

/-- The cost of one label. -/
def labCost1 (a g G : ℕ) : ℕ :=
  (18 * g + 3) + 1 + (G * (18 * a + 8) + 18 * G + 10) + 1 + (18 * (g + a * G) + 3) + 1 + (18 * (g + a * G) + 3) + 1 +
    4 * 10 + 1 + ((g + a * G) * (8 * 4 + 4) + 1) + 1 + 8 * 4

theorem labOne_spec (σ : WState ns nr) (a g G c : ℕ) (ha : σ.val (R 5) = a) (hg : σ.val (R 6) = g)
    (hG : σ.val (R 2) = G) (hL : σ.val (R 8) = 0) (hT : σ.val (R 9) = 0) (hW : σ.val (R 10) = 0)
    (hc : σ.val (R 11) = c) (ho : σ.sh O = (σ.st O).length)
    (hcap : g + a * G + 2 * (g + a * G) + 10 + c + σ.val (R 0) + 4 * (g + a * G) + 4 + a + G ≤ cap) :
    WExec cap (labOne O R) σ ((appendO σ O (R 0) (labE (g + a * G))).setv (R 11) (c + 2 * (g + a * G) + 10))
      (labCost1 a g G) := by
  have hne : ∀ {i j : Fin 13}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have n80 : R 8 ≠ R 0 := hne (by decide)
  have n110 : R 11 ≠ R 0 := hne (by decide)
  have n811 : R 8 ≠ R 11 := hne (by decide)
  obtain ⟨lab, hlab⟩ : ∃ lab, lab = g + a * G := ⟨_, rfl⟩
  rw [← hlab] at hcap ⊢
  -- step 1: LAB := GI
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 6) (R 8) (R 9) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ hL hT (by omega)
  rw [hg] at h1
  -- step 2: LAB += R4K·G
  have h2 := UnaryArith.mulAddW_spec cap (mR.trans R) (σ.setv (R 8) g)
    (by simp [mR, Function.update_apply, hne (show (9 : Fin 13) ≠ 8 by decide), hT])
    (by simp [mR, Function.update_apply, hne (show (10 : Fin 13) ≠ 8 by decide), hW])
    (by simp [mR, Function.update_apply, hne (show (2 : Fin 13) ≠ 8 by decide), hG]; omega)
    (by simp [mR, Function.update_apply, hne (show (2 : Fin 13) ≠ 8 by decide),
      hne (show (5 : Fin 13) ≠ 8 by decide), hG, ha]; rw [← hlab]; omega)
    (by simp [mR, Function.update_apply, hne (show (5 : Fin 13) ≠ 8 by decide), ha]; omega)
  have e2 : (σ.setv (R 8) g).setv ((mR.trans R) 2)
      ((σ.setv (R 8) g).val ((mR.trans R) 2) + (σ.setv (R 8) g).val ((mR.trans R) 0) *
        (σ.setv (R 8) g).val ((mR.trans R) 1)) = σ.setv (R 8) lab := by
    simp [mR, Function.update_apply, hne (show (5 : Fin 13) ≠ 8 by decide), hne (show (2 : Fin 13) ≠ 8 by decide),
      ha, hG, wsetv_setv, hlab]
  have c2 : (σ.setv (R 8) g).val ((mR.trans R) 1) * (18 * (σ.setv (R 8) g).val ((mR.trans R) 0) + 8) +
      18 * (σ.setv (R 8) g).val ((mR.trans R) 1) + 10 = G * (18 * a + 8) + 18 * G + 10 := by
    simp [mR, Function.update_apply, hne (show (5 : Fin 13) ≠ 8 by decide), hne (show (2 : Fin 13) ≠ 8 by decide),
      ha, hG]
  rw [e2, c2] at h2
  -- step 3, 4: CAP1 += LAB twice
  have h3 := ParseNat.addTo_spec cap (R 8) (R 11) (R 9) n811 (hne (by decide)) (hne (by decide)) (σ.setv (R 8) lab)
    (by simp [Function.update_apply, hne (show (9 : Fin 13) ≠ 8 by decide), hT]) (by simp; omega)
    (by simp [Function.update_apply, Ne.symm n811, hc]; omega)
  have e3 : (σ.setv (R 8) lab).setv (R 11) ((σ.setv (R 8) lab).val (R 11) + (σ.setv (R 8) lab).val (R 8)) =
      (σ.setv (R 8) lab).setv (R 11) (c + lab) := by simp [Function.update_apply, Ne.symm n811, hc]
  rw [e3, show (σ.setv (R 8) lab).val (R 8) = lab by simp] at h3
  have h4 := ParseNat.addTo_spec cap (R 8) (R 11) (R 9) n811 (hne (by decide)) (hne (by decide))
    ((σ.setv (R 8) lab).setv (R 11) (c + lab))
    (by simp [Function.update_apply, hne (show (9 : Fin 13) ≠ 8 by decide), hne (show (9 : Fin 13) ≠ 11 by decide), hT])
    (by simp [Function.update_apply, n811]; omega) (by simp [Function.update_apply, n811]; omega)
  have e4 : ((σ.setv (R 8) lab).setv (R 11) (c + lab)).setv (R 11)
      (((σ.setv (R 8) lab).setv (R 11) (c + lab)).val (R 11) + ((σ.setv (R 8) lab).setv (R 11) (c + lab)).val (R 8)) =
      (σ.setv (R 8) lab).setv (R 11) (c + 2 * lab) := by
    simp [Function.update_apply, n811, wsetv_setv]; congr 1; omega
  rw [e4, show ((σ.setv (R 8) lab).setv (R 11) (c + lab)).val (R 8) = lab by simp [Function.update_apply, n811]] at h4
  -- step 5: CAP1 += 10
  have h5 := incN_spec cap (R 11) 10 ((σ.setv (R 8) lab).setv (R 11) (c + 2 * lab)) (by simp; omega)
  rw [wsetv_setv, show ((σ.setv (R 8) lab).setv (R 11) (c + 2 * lab)).val (R 11) + 10 = c + 2 * lab + 10 by simp] at h5
  -- step 6: emit the ones, LAB := 0
  have h6 := repW_spec cap O (R 0) (R 8) n80 (m2 true) lab ((σ.setv (R 8) lab).setv (R 11) (c + 2 * lab + 10))
    (by simp [Function.update_apply, n811]) (by simp [ho]) (by simp [Function.update_apply, Ne.symm n80, Ne.symm n110, m2]; omega)
    (by omega)
  have e6 : (appendO ((σ.setv (R 8) lab).setv (R 11) (c + 2 * lab + 10)) O (R 0) (reps lab (m2 true))).setv (R 8) 0 =
      (appendO σ O (R 0) (reps lab (m2 true))).setv (R 11) (c + 2 * lab + 10) := by
    unfold appendO
    apply WState.eq
    · simp
    · simp
    · funext j
      simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · simp
  rw [e6] at h6
  -- step 7: the code's end
  have h7 := emitW_spec cap O (R 0) (m2 false) ((appendO σ O (R 0) (reps lab (m2 true))).setv (R 11) (c + 2 * lab + 10))
    (by simp [ho]) (by simp [Function.update_apply, Ne.symm n110, m2, reps]; omega)
  have hall := WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 (WExec.seq h6 h7)))))
  refine WExec.cast cap hall ?_ (le_of_eq ?_)
  · rw [appendO_setv _ O (R 0) (R 11) n110, appendO_append]; rfl
  · unfold labCost1; subst hlab; simp only [m2, List.length_cons, List.length_nil]; ring

end Label

/-! ## One gate: four labels -/

section Gate
variable (O : Fin (ns + 1)) (R : LReg nr)

/-- The labels of gate `gi` at row offset `r4 = 4·row`: `(r4 + k)·G + gi`, `k < 4` (C3a's numbering). -/
def gateLabs (r4 G gi : ℕ) : List ℕ := (List.range 4).map fun k => gi + (r4 + k) * G

def gateBody : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 1) (R 5) (R 9))
    (.seq (incN (R 12) 4)
      (.seq (.whr (R 12) (.seq (.dec (R 12)) (.seq (labOne O R) (.inc (R 5)))))
        (.seq (WM.clear (R 5)) (.inc (R 6)))))

/-- The label sum's increment of one gate. -/
def labAdd (ls : List ℕ) : ℕ := (ls.map fun lab => 2 * lab + 10).sum

theorem labCost1_mono (a a' g G : ℕ) (h : a ≤ a') : labCost1 a g G ≤ labCost1 a' g G := by
  unfold labCost1
  have h1 : a * G ≤ a' * G := Nat.mul_le_mul_right _ h
  have h2 : G * (18 * a + 8) ≤ G * (18 * a' + 8) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The cost of one gate. -/
def gateCost (r4 G gi : ℕ) : ℕ :=
  (18 * r4 + 3) + 1 + (4 * 4) + 1 + (4 * (labCost1 (r4 + 3) gi G + 1 + 3 + 4) + 1) + 1 + (3 * (r4 + 4) + 1) + 1 + 3

theorem gateLabs_take_succ (r4 G gi k : ℕ) (hk : k < 4) :
    (gateLabs r4 G gi).take (k + 1) = (gateLabs r4 G gi).take k ++ [gi + (r4 + k) * G] := by
  unfold gateLabs
  rw [List.take_add_one, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- The gate loop's state: the output extended by `u`, `CAP1 = c`, `R4K = x`, `K4 = y`. -/
def gSt (σ : WState ns nr) (u : List Bool) (c x y : ℕ) : WState ns nr :=
  (((appendO σ O (R 0) u).setv (R 11) c).setv (R 5) x).setv (R 12) y

section GSt
variable {O R}

theorem gSt_val (σ : WState ns nr) (u : List Bool) (c x y : ℕ) (j : Fin nr) :
    (gSt O R σ u c x y).val j =
      if j = R 12 then y else if j = R 5 then x else if j = R 11 then c
      else if j = R 0 then σ.val (R 0) + u.length else σ.val j := by
  simp only [gSt, WState.setv_val, appendO_val, Function.update_apply]

theorem gSt_sh (σ : WState ns nr) (u : List Bool) (c x y : ℕ) :
    (gSt O R σ u c x y).sh = Function.update σ.sh O (σ.sh O + u.length) := by simp [gSt]

theorem gSt_st (σ : WState ns nr) (u : List Bool) (c x y : ℕ) :
    (gSt O R σ u c x y).st = Function.update σ.st O (σ.st O ++ u) := by simp [gSt]

theorem gSt_setv12 (σ : WState ns nr) (u : List Bool) (c x y z : ℕ) :
    (gSt O R σ u c x y).setv (R 12) z = gSt O R σ u c x z := by
  unfold gSt; rw [wsetv_setv]

theorem gSt_setv11 (σ : WState ns nr) (u : List Bool) (c x y z : ℕ) :
    (gSt O R σ u c x y).setv (R 11) z = gSt O R σ u z x y := by
  have hR : ∀ i j : Fin 13, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  unfold gSt
  rw [wsetv_comm _ _ _ (by simp [hR] : R 12 ≠ R 11), wsetv_comm _ _ _ (by simp [hR] : R 5 ≠ R 11), wsetv_setv]

theorem gSt_setv5 (σ : WState ns nr) (u : List Bool) (c x y z : ℕ) :
    (gSt O R σ u c x y).setv (R 5) z = gSt O R σ u c z y := by
  have hR : ∀ i j : Fin 13, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  unfold gSt
  rw [wsetv_comm _ _ _ (by simp [hR] : R 12 ≠ R 5), wsetv_setv]

theorem gSt_append (σ : WState ns nr) (u v : List Bool) (c x y : ℕ) :
    appendO (gSt O R σ u c x y) O (R 0) v = gSt O R σ (u ++ v) c x y := by
  have hR : ∀ i j : Fin 13, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  unfold gSt
  rw [appendO_setv _ O (R 0) (R 12) (by simp [hR]), appendO_setv _ O (R 0) (R 5) (by simp [hR]),
    appendO_setv _ O (R 0) (R 11) (by simp [hR]), appendO_append]

end GSt

theorem gateBody_spec (σ : WState ns nr) (r4 G gi c : ℕ) (h1 : σ.val (R 1) = r4) (h2 : σ.val (R 2) = G)
    (h6 : σ.val (R 6) = gi) (h5 : σ.val (R 5) = 0) (h8 : σ.val (R 8) = 0) (h9 : σ.val (R 9) = 0)
    (h10 : σ.val (R 10) = 0) (h12 : σ.val (R 12) = 0) (h11 : σ.val (R 11) = c) (ho : σ.sh O = (σ.st O).length)
    (hcap : σ.val (R 0) + 4 * (4 * (gi + (r4 + 4) * G) + 4) + c + 4 * (2 * (gi + (r4 + 4) * G) + 10) +
      7 * (gi + (r4 + 4) * G) + r4 + G + 20 ≤ cap) :
    WExec cap (gateBody O R) σ
      (((appendO σ O (R 0) ((gateLabs r4 G gi).flatMap labE)).setv (R 11) (c + labAdd (gateLabs r4 G gi))).setv (R 6)
        (gi + 1))
      (gateCost r4 G gi) := by
  have hR : ∀ i j : Fin 13, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  have hne : ∀ {i j : Fin 13}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  obtain ⟨M, hM⟩ : ∃ M, M = gi + (r4 + 4) * G := ⟨_, rfl⟩
  rw [← hM] at hcap
  have hlabM : ∀ k ≤ 4, gi + (r4 + k) * G ≤ M := fun k hk => by
    rw [hM]; have := Nat.mul_le_mul_right G (show r4 + k ≤ r4 + 4 by omega); omega
  have hGM : G ≤ M + 1 := by
    rw [hM]; rcases Nat.eq_zero_or_pos G with hG0 | hG0
    · omega
    · have : G ≤ (r4 + 4) * G := Nat.le_mul_of_pos_left G (by omega); omega

  have s1 := FinalPass.Hash4.wcopyR_spec cap (R 1) (R 5) (R 9) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ h5 h9 (by omega)
  rw [h1] at s1
  have s2 := incN_spec cap (R 12) 4 (σ.setv (R 5) r4) (by simp [hR, h12]; omega)
  have hv12 : (σ.setv (R 5) r4).val (R 12) = 0 := by simp [hR, h12]
  have e2 : (σ.setv (R 5) r4).setv (R 12) ((σ.setv (R 5) r4).val (R 12) + 4) = gSt O R σ [] c r4 4 := by
    rw [hv12]; unfold gSt; rw [appendO_nil, ← h11, wsetv_same]
  rw [e2] at s2
  -- the loop over `k < 4`
  let S : ℕ → WState ns nr := fun k =>
    gSt O R σ (((gateLabs r4 G gi).take k).flatMap labE) (c + labAdd ((gateLabs r4 G gi).take k)) (r4 + k) (4 - k)
  have hS0 : S 0 = gSt O R σ [] c r4 4 := by simp [S, labAdd]
  have hloop := UnionMachine.Round.wloop cap (R 12) (.seq (labOne O R) (.inc (R 5)))
    (labCost1 (r4 + 3) gi G + 1 + 3) 4 S
    (fun k _ => by simp [S, gSt_val])
    (by omega)
    (fun k hk => by
      set u := ((gateLabs r4 G gi).take k).flatMap labE with hu
      set ck := c + labAdd ((gateLabs r4 G gi).take k) with hck
      have hlen : u.length ≤ k * (4 * M + 4) := by
        rw [hu, List.length_flatMap]
        have hb : ∀ lab ∈ (gateLabs r4 G gi).take k, (labE lab).length ≤ 4 * M + 4 := by
          intro lab hl
          have hl' := List.mem_of_mem_take hl
          unfold gateLabs at hl'
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hl'
          have := hlabM k' (by simp at hk'; omega)
          unfold labE reps; simp [m2]; omega
        calc (((gateLabs r4 G gi).take k).map fun lab => (labE lab).length).sum
            ≤ (((gateLabs r4 G gi).take k).map fun _ => 4 * M + 4).sum := List.sum_le_sum (fun lab hl => hb lab hl)
          _ = ((gateLabs r4 G gi).take k).length * (4 * M + 4) := by simp
          _ ≤ k * (4 * M + 4) := Nat.mul_le_mul_right _ (by simp)
      have hadd : ck ≤ c + k * (2 * M + 10) := by
        rw [hck]; unfold labAdd
        have : (((gateLabs r4 G gi).take k).map fun lab => 2 * lab + 10).sum ≤ k * (2 * M + 10) :=
          calc (((gateLabs r4 G gi).take k).map fun lab => 2 * lab + 10).sum
              ≤ (((gateLabs r4 G gi).take k).map fun _ => 2 * M + 10).sum := by
                apply List.sum_le_sum
                intro lab hl
                have hl' := List.mem_of_mem_take hl
                unfold gateLabs at hl'
                obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hl'
                have := hlabM k' (by simp at hk'; omega)
                omega
            _ = ((gateLabs r4 G gi).take k).length * (2 * M + 10) := by simp
            _ ≤ k * (2 * M + 10) := Nat.mul_le_mul_right _ (by simp)
        omega
      have hk4 : k * (4 * M + 4) ≤ 4 * (4 * M + 4) := Nat.mul_le_mul_right _ (by omega)
      have hk2 : k * (2 * M + 10) ≤ 4 * (2 * M + 10) := Nat.mul_le_mul_right _ (by omega)
      have hlk := hlabM k (by omega)
      have eX : (S k).setv (R 12) (4 - k - 1) = gSt O R σ u ck (r4 + k) (4 - k - 1) := gSt_setv12 _ _ _ _ _ _
      rw [eX]
      have hL := labOne_spec cap O R (gSt O R σ u ck (r4 + k) (4 - k - 1)) (r4 + k) gi G ck
        (by rw [gSt_val]; simp [hR]) (by rw [gSt_val]; simp [hR, h6]) (by rw [gSt_val]; simp [hR, h2])
        (by rw [gSt_val]; simp [hR, h8]) (by rw [gSt_val]; simp [hR, h9]) (by rw [gSt_val]; simp [hR, h10])
        (by rw [gSt_val]; simp [hR]) (by rw [gSt_sh, gSt_st]; simp [ho])
        (by rw [gSt_val]; simp [hR]; omega)
      rw [gSt_append, gSt_setv11] at hL
      have hI := WExec.inc (cap := cap) (R 5)
        (gSt O R σ (u ++ labE (gi + (r4 + k) * G)) (ck + 2 * (gi + (r4 + k) * G) + 10) (r4 + k) (4 - k - 1))
        (by rw [gSt_val]; simp [hR]; omega)
      have e5 : (gSt O R σ (u ++ labE (gi + (r4 + k) * G)) (ck + 2 * (gi + (r4 + k) * G) + 10) (r4 + k) (4 - k - 1)).setv
          (R 5) ((gSt O R σ (u ++ labE (gi + (r4 + k) * G)) (ck + 2 * (gi + (r4 + k) * G) + 10) (r4 + k)
            (4 - k - 1)).val (R 5) + 1) =
          gSt O R σ (u ++ labE (gi + (r4 + k) * G)) (ck + 2 * (gi + (r4 + k) * G) + 10) (r4 + k + 1) (4 - k - 1) := by
        rw [gSt_setv5, gSt_val]; simp [hR]
      rw [e5] at hI
      refine WExec.cast cap (WExec.seq (WExec.mono hL (labCost1_mono _ _ _ _ (by omega))) hI) ?_ le_rfl
      simp only [S]
      rw [gateLabs_take_succ r4 G gi k hk, List.flatMap_append, List.flatMap_singleton]
      have hA : labAdd ((gateLabs r4 G gi).take k ++ [gi + (r4 + k) * G]) =
          labAdd ((gateLabs r4 G gi).take k) + (2 * (gi + (r4 + k) * G) + 10) := by
        unfold labAdd; simp
      rw [hA, show 4 - k - 1 = 4 - (k + 1) by omega, show r4 + k + 1 = r4 + (k + 1) by omega, ← hu,
        show ck + 2 * (gi + (r4 + k) * G) + 10 = c + (labAdd ((gateLabs r4 G gi).take k) + (2 * (gi + (r4 + k) * G) + 10))
          by rw [hck]; omega])
  rw [hS0] at hloop
  -- R4K := 0, GI += 1
  have hfull : (gateLabs r4 G gi).take 4 = gateLabs r4 G gi := by simp [gateLabs]
  have s4 := wclear_spec cap (R 5) (r4 + 4) (S 4) (by simp only [S, gSt_val]; simp [hR]) (by
    simp only [S, gSt_val]; simp [hR]; omega)
  have e4 : (S 4).setv (R 5) 0 = gSt O R σ ((gateLabs r4 G gi).flatMap labE) (c + labAdd (gateLabs r4 G gi)) 0 0 := by
    simp only [S, gSt_setv5, hfull, Nat.sub_self]
  rw [e4] at s4
  have s5 := WExec.inc (cap := cap) (R 6) (gSt O R σ ((gateLabs r4 G gi).flatMap labE) (c + labAdd (gateLabs r4 G gi)) 0 0)
    (by rw [gSt_val]; simp [hR, h6]; omega)
  have hall := WExec.seq s1 (WExec.seq s2 (WExec.seq hloop (WExec.seq s4 s5)))
  refine WExec.cast cap hall ?_ (le_of_eq (by unfold gateCost; ring))
  rw [gSt_val]
  simp only [if_neg (hne (show (6 : Fin 13) ≠ 12 by decide)), if_neg (hne (show (6 : Fin 13) ≠ 5 by decide)),
    if_neg (hne (show (6 : Fin 13) ≠ 11 by decide)), if_neg (hne (show (6 : Fin 13) ≠ 0 by decide)), h6]
  unfold gSt
  apply WState.eq
  · simp
  · simp
  · funext j
    simp only [WState.setv_val, appendO_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp

/-! ## All gates of a slice -/

/-- The labels of the gates `off … off + Lg − 1` (C3a's `labsOf` at `r4 = 4·row`, `labs_eq`). -/
def sliceLabs (r4 G off Lg : ℕ) : List ℕ := (List.range' off Lg).flatMap fun gi => gateLabs r4 G gi

theorem labs_eq (G row off Lg : ℕ) :
    CompilerMachine.Pool.labsOf G row (List.range' off Lg) = sliceLabs (4 * row) G off Lg := by
  unfold CompilerMachine.Pool.labsOf sliceLabs gateLabs CompilerMachine.Pool.poolIndex
  refine List.flatMap_congr fun gi _ => ?_
  refine List.map_congr_left fun k _ => ?_
  ring

/-- The slice's labels: `GI := off`, `LG := Lg`; per gate the four labels; `GI := 0`. -/
def labsW : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 3) (R 6) (R 9))
    (.seq (FinalPass.Hash4.wcopyR (R 4) (R 7) (R 9))
      (.seq (.whr (R 7) (.seq (.dec (R 7)) (gateBody O R))) (WM.clear (R 6))))

/-- The slice loop's state: the output extended by `u`, `CAP1 = c`, `GI = x`, `LG = y`. -/
def hSt (σ : WState ns nr) (u : List Bool) (c x y : ℕ) : WState ns nr :=
  (((appendO σ O (R 0) u).setv (R 11) c).setv (R 6) x).setv (R 7) y

section HSt
variable {O R}

theorem hSt_val (σ : WState ns nr) (u : List Bool) (c x y : ℕ) (j : Fin nr) :
    (hSt O R σ u c x y).val j =
      if j = R 7 then y else if j = R 6 then x else if j = R 11 then c
      else if j = R 0 then σ.val (R 0) + u.length else σ.val j := by
  simp only [hSt, WState.setv_val, appendO_val, Function.update_apply]

theorem hSt_sh (σ : WState ns nr) (u : List Bool) (c x y : ℕ) :
    (hSt O R σ u c x y).sh = Function.update σ.sh O (σ.sh O + u.length) := by simp [hSt]

theorem hSt_st (σ : WState ns nr) (u : List Bool) (c x y : ℕ) :
    (hSt O R σ u c x y).st = Function.update σ.st O (σ.st O ++ u) := by simp [hSt]

theorem hSt_setv7 (σ : WState ns nr) (u : List Bool) (c x y z : ℕ) :
    (hSt O R σ u c x y).setv (R 7) z = hSt O R σ u c x z := by
  unfold hSt; rw [wsetv_setv]

theorem hSt_setv11 (σ : WState ns nr) (u : List Bool) (c x y z : ℕ) :
    (hSt O R σ u c x y).setv (R 11) z = hSt O R σ u z x y := by
  have hR : ∀ i j : Fin 13, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  unfold hSt
  rw [wsetv_comm _ _ _ (by simp [hR] : R 7 ≠ R 11), wsetv_comm _ _ _ (by simp [hR] : R 6 ≠ R 11), wsetv_setv]

theorem hSt_setv6 (σ : WState ns nr) (u : List Bool) (c x y z : ℕ) :
    (hSt O R σ u c x y).setv (R 6) z = hSt O R σ u c z y := by
  have hR : ∀ i j : Fin 13, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  unfold hSt
  rw [wsetv_comm _ _ _ (by simp [hR] : R 7 ≠ R 6), wsetv_setv]

theorem hSt_append (σ : WState ns nr) (u v : List Bool) (c x y : ℕ) :
    appendO (hSt O R σ u c x y) O (R 0) v = hSt O R σ (u ++ v) c x y := by
  have hR : ∀ i j : Fin 13, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  unfold hSt
  rw [appendO_setv _ O (R 0) (R 7) (by simp [hR]), appendO_setv _ O (R 0) (R 6) (by simp [hR]),
    appendO_setv _ O (R 0) (R 11) (by simp [hR]), appendO_append]

end HSt

theorem labCost1_mono_g (a g g' G : ℕ) (h : g ≤ g') : labCost1 a g G ≤ labCost1 a g' G := by
  unfold labCost1; omega

theorem gateCost_mono (r4 G gi gi' : ℕ) (h : gi ≤ gi') : gateCost r4 G gi ≤ gateCost r4 G gi' := by
  unfold gateCost
  have := labCost1_mono_g (r4 + 3) gi gi' G h
  omega

theorem sliceLabs_succ (r4 G off j : ℕ) :
    sliceLabs r4 G off (j + 1) = sliceLabs r4 G off j ++ gateLabs r4 G (off + j) := by
  unfold sliceLabs
  rw [List.range'_1_concat, List.flatMap_append, List.flatMap_singleton]

theorem labE_length (lab : ℕ) : (labE lab).length = 4 * lab + 4 := by
  unfold labE reps; simp [m2]; ring

theorem gateLabs_le (r4 G gi M : ℕ) (hM : gi + (r4 + 4) * G ≤ M) : ∀ lab ∈ gateLabs r4 G gi, lab ≤ M := by
  intro lab hl
  unfold gateLabs at hl
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
  have := Nat.mul_le_mul_right G (show r4 + k ≤ r4 + 4 by simp at hk; omega)
  omega

theorem flat_len_le (ls : List ℕ) (M : ℕ) (h : ∀ lab ∈ ls, lab ≤ M) :
    (ls.flatMap labE).length ≤ ls.length * (4 * M + 4) := by
  rw [List.length_flatMap]
  calc (ls.map fun lab => (labE lab).length).sum ≤ (ls.map fun _ => 4 * M + 4).sum :=
        List.sum_le_sum fun lab hl => by rw [labE_length]; have := h lab hl; omega
    _ = ls.length * (4 * M + 4) := by simp

theorem labAdd_le (ls : List ℕ) (M : ℕ) (h : ∀ lab ∈ ls, lab ≤ M) : labAdd ls ≤ ls.length * (2 * M + 10) := by
  unfold labAdd
  calc (ls.map fun lab => 2 * lab + 10).sum ≤ (ls.map fun _ => 2 * M + 10).sum :=
        List.sum_le_sum fun lab hl => by have := h lab hl; omega
    _ = ls.length * (2 * M + 10) := by simp

theorem sliceLabs_length (r4 G off j : ℕ) : (sliceLabs r4 G off j).length = 4 * j := by
  induction j with
  | zero => simp [sliceLabs]
  | succ j ih => rw [sliceLabs_succ, List.length_append, ih]; simp [gateLabs]; ring

theorem sliceLabs_le (r4 G off Lg M : ℕ) (hM : off + Lg + (r4 + 4) * G ≤ M) (j : ℕ) (hj : j ≤ Lg) :
    ∀ lab ∈ sliceLabs r4 G off j, lab ≤ M := by
  intro lab hl
  unfold sliceLabs at hl
  obtain ⟨gi, hgi, hl⟩ := List.mem_flatMap.mp hl
  rw [List.mem_range'_1] at hgi
  exact gateLabs_le r4 G gi M (by omega) lab hl

/-- The cost of a slice. -/
def labsCost (r4 G off Lg : ℕ) : ℕ :=
  (18 * off + 3) + 1 + ((18 * Lg + 3) + 1 + ((Lg * (gateCost r4 G (off + Lg) + 4) + 1) + 1 + (3 * (off + Lg) + 1)))

theorem labsW_spec (σ : WState ns nr) (r4 G off Lg c : ℕ) (h1 : σ.val (R 1) = r4) (h2 : σ.val (R 2) = G)
    (h3 : σ.val (R 3) = off) (h4 : σ.val (R 4) = Lg) (h5 : σ.val (R 5) = 0) (h6 : σ.val (R 6) = 0)
    (h7 : σ.val (R 7) = 0) (h8 : σ.val (R 8) = 0) (h9 : σ.val (R 9) = 0) (h10 : σ.val (R 10) = 0)
    (h12 : σ.val (R 12) = 0) (h11 : σ.val (R 11) = c) (ho : σ.sh O = (σ.st O).length) (M : ℕ)
    (hM : off + Lg + (r4 + 4) * G ≤ M)
    (hcap : σ.val (R 0) + Lg * (4 * (4 * M + 4)) + c + Lg * (4 * (2 * M + 10)) + 4 * (4 * M + 4) +
      4 * (2 * M + 10) + 7 * M + r4 + G + off + Lg + 20 ≤ cap) :
    WExec cap (labsW O R) σ
      ((appendO σ O (R 0) ((sliceLabs r4 G off Lg).flatMap labE)).setv (R 11) (c + labAdd (sliceLabs r4 G off Lg)))
      (labsCost r4 G off Lg) := by
  have hR : ∀ i j : Fin 13, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  have hne : ∀ {i j : Fin 13}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have s1 := FinalPass.Hash4.wcopyR_spec cap (R 3) (R 6) (R 9) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ h6 h9 (by omega)
  rw [h3] at s1
  have s2 := FinalPass.Hash4.wcopyR_spec cap (R 4) (R 7) (R 9) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (σ.setv (R 6) off) (by simp [hR, h7]) (by simp [hR, h9]) (by simp [hR, h4]; omega)
  have e2 : (σ.setv (R 6) off).setv (R 7) ((σ.setv (R 6) off).val (R 4)) = hSt O R σ [] c off Lg := by
    have hv : (σ.setv (R 6) off).val (R 4) = Lg := by simp [hR, h4]
    rw [hv]; unfold hSt; rw [appendO_nil, ← h11, wsetv_same]
  rw [e2, show (σ.setv (R 6) off).val (R 4) = Lg by simp [hR, h4]] at s2
  let T : ℕ → WState ns nr := fun j =>
    hSt O R σ ((sliceLabs r4 G off j).flatMap labE) (c + labAdd (sliceLabs r4 G off j)) (off + j) (Lg - j)
  have hT0 : T 0 = hSt O R σ [] c off Lg := by simp [T, sliceLabs, labAdd]
  have hloop := UnionMachine.Round.wloop cap (R 7) (gateBody O R) (gateCost r4 G (off + Lg)) Lg T
    (fun j _ => by simp [T, hSt_val])
    (by omega)
    (fun j hj => by
      set u := (sliceLabs r4 G off j).flatMap labE with hu
      set cj := c + labAdd (sliceLabs r4 G off j) with hcj
      have hbound := sliceLabs_le r4 G off Lg M hM j (by omega)
      have hlen := flat_len_le _ M hbound
      have hadd := labAdd_le _ M hbound
      rw [sliceLabs_length] at hlen hadd
      rw [← hu] at hlen
      have hj1 : 4 * j * (4 * M + 4) ≤ Lg * (4 * (4 * M + 4)) := by
        have := Nat.mul_le_mul_right (4 * (4 * M + 4)) (show j ≤ Lg by omega); nlinarith
      have hj2 : 4 * j * (2 * M + 10) ≤ Lg * (4 * (2 * M + 10)) := by
        have := Nat.mul_le_mul_right (4 * (2 * M + 10)) (show j ≤ Lg by omega); nlinarith
      have hgM : off + j + (r4 + 4) * G ≤ M := by omega
      have eX : (T j).setv (R 7) (Lg - j - 1) = hSt O R σ u cj (off + j) (Lg - j - 1) := hSt_setv7 _ _ _ _ _ _
      rw [eX]
      have hv0 : (hSt O R σ u cj (off + j) (Lg - j - 1)).val (R 0) = σ.val (R 0) + u.length := by
        rw [hSt_val]; simp [hR]
      have hcapG : (hSt O R σ u cj (off + j) (Lg - j - 1)).val (R 0) +
          4 * (4 * (off + j + (r4 + 4) * G) + 4) + cj + 4 * (2 * (off + j + (r4 + 4) * G) + 10) +
          7 * (off + j + (r4 + 4) * G) + r4 + G + 20 ≤ cap := by
        rw [hv0, hcj]
        generalize (r4 + 4) * G = X at hgM ⊢
        omega
      have hG := gateBody_spec cap O R (hSt O R σ u cj (off + j) (Lg - j - 1)) r4 G (off + j) cj
        (by rw [hSt_val]; simp [hR, h1]) (by rw [hSt_val]; simp [hR, h2]) (by rw [hSt_val]; simp [hR])
        (by rw [hSt_val]; simp [hR, h5]) (by rw [hSt_val]; simp [hR, h8]) (by rw [hSt_val]; simp [hR, h9])
        (by rw [hSt_val]; simp [hR, h10]) (by rw [hSt_val]; simp [hR, h12]) (by rw [hSt_val]; simp [hR])
        (by rw [hSt_sh, hSt_st]; simp [ho]) hcapG
      rw [hSt_append, hSt_setv11, hSt_setv6] at hG
      refine WExec.cast cap (WExec.mono hG (gateCost_mono r4 G _ _ (by omega))) ?_ le_rfl
      simp only [T]
      rw [sliceLabs_succ, List.flatMap_append, ← hu]
      have hA : labAdd (sliceLabs r4 G off j ++ gateLabs r4 G (off + j)) =
          labAdd (sliceLabs r4 G off j) + labAdd (gateLabs r4 G (off + j)) := by
        unfold labAdd; simp
      rw [hA, hcj, show off + j + 1 = off + (j + 1) by omega, show Lg - j - 1 = Lg - (j + 1) by omega, Nat.add_assoc])
  rw [hT0] at hloop
  have s4 := wclear_spec cap (R 6) (off + Lg) (T Lg) (by simp [T, hSt_val]) (by simp [T, hSt_val]; omega)
  have hall := WExec.seq s1 (WExec.seq s2 (WExec.seq hloop s4))
  refine WExec.cast cap hall ?_ (le_of_eq (by unfold labsCost; ring))
  simp only [T, Nat.sub_self]
  rw [hSt_setv6]
  generalize (sliceLabs r4 G off Lg).flatMap labE = U
  generalize c + labAdd (sliceLabs r4 G off Lg) = C
  unfold hSt
  apply WState.eq
  · simp
  · simp
  · funext x
    simp only [WState.setv_val, appendO_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp
end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.Emit
