import Proof.Gates.CounterMachine.FormulaTokC

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

section Dig
variable (S : Fin (ns + 1)) (F : Fin 24 ↪ Fin nr)

/-- The digit printer. -/
def digP (CW FA : Fin (ns + 1)) (Gr off LB LBF Jc Jp : Fin nr) : WM ns nr :=
  .ifr Jc
    (.seq (stP S CW F Gr off LB Jc)
    (.seq (copyR Jc Jp (F 8))
    (.seq (.dec Jp)
    (.seq (rateC S F FA LBF Jp)
    (.seq (stP S CW F Gr off LB Jp)
    (.seq (WM.clear Jp)
    (.seq (litC S F .mul) (litC S F .sub))))))))
    (stP S CW F Gr off LB Jc)

theorem tokWord_mul_length : (tokWord .mul).length = 7 := by decide
theorem tokWord_sub_length : (tokWord .sub).length = 7 := by decide

theorem encI_take_mono (blocks : List (List ℤ)) {a b : ℕ} (h : a ≤ b) :
    (encI (blocks.take a).flatten).length ≤ (encI (blocks.take b).flatten).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.flatten_append, encI_append, List.length_append]; omega

theorem encN_take_mono (L : List ℕ) {a b : ℕ} (h : a ≤ b) : (encN (L.take a)).length ≤ (encN (L.take b)).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, encN_append, List.length_append]; omega

theorem digP_run (CW FA : Fin (ns + 1)) (hSC : S ≠ CW) (hFS : FA ≠ S) (Gr off LB LBF Jc Jp : Fin nr)
    (hG : ∀ i : Fin 24, F i ≠ Gr) (ho : ∀ i : Fin 24, F i ≠ off) (hL : ∀ i : Fin 24, F i ≠ LB)
    (hLF : ∀ i : Fin 24, F i ≠ LBF) (hJc : ∀ i : Fin 24, F i ≠ Jc) (hJp : ∀ i : Fin 24, F i ≠ Jp)
    (hcp : Jc ≠ Jp) (hfp : LBF ≠ Jp) (hgp : Gr ≠ Jp) (hop : off ≠ Jp) (hlp : LB ≠ Jp)
    (G j o lb lbf Λ : ℕ) (blocks : List (List ℤ)) (L : List ℕ) (hb : ∀ b ∈ blocks, b.length = G)
    (hj : j < blocks.length) (hjL : j ≤ L.length)
    (restC restF : List Bool) (σ : WState ns nr) (h : TRest S F σ)
    (hstC : σ.st CW = encI blocks.flatten ++ restC) (hshC : σ.sh CW = 0)
    (hstF : σ.st FA = encN L ++ restF) (hshF : σ.sh FA = 0)
    (hGv : σ.val Gr = G) (hov : σ.val off = o) (hLv : σ.val LB = lb) (hLFv : σ.val LBF = lbf)
    (hJcv : σ.val Jc = j) (hJpv : σ.val Jp = 0)
    (hlb : (encI (blocks.take (j + 1)).flatten).length ≤ lb) (hlbf : (encN (L.take j)).length ≤ lbf)
    (hjΛ : j ≤ Λ) (hoG : o + G ≤ Λ) (hlbΛ : lb ≤ Λ) (hlbfΛ : lbf ≤ Λ)
    (hz : ∀ b ∈ blocks, ∀ z ∈ b, natBitLength z.natAbs ≤ Λ) (hLΛ : ∀ x ∈ L, natBitLength x ≤ Λ)
    (hcap : TCap cap F σ (digToks o (fun s => blocks.getD s []) (fun i => (L.getD i 0 : ℤ)) j) Λ) :
    WExec cap (digP S F CW FA Gr off LB LBF Jc Jp) σ
      (emitT S F σ (digToks o (fun s => blocks.getD s []) (fun i => (L.getD i 0 : ℤ)) j)) (9000 * (Λ + 1) ^ 3) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → F a ≠ F b := fun h => F.injective.ne h
  have hz0 := h.zero S F
  have hzc : ∀ b ∈ blocks, ∀ z ∈ b, natBitLength z.natAbs ≤ Λ := hz
  cases j with
  | zero =>
    have hg : blocks.getD 0 [] = blocks[0] := List.getD_eq_getElem _ _ hj
    simp only [digToks, hg] at hcap ⊢
    have e := stP_run cap S F CW hSC Gr off LB Jc hG ho hL hJc G 0 o lb Λ blocks hb hj restC σ h hstC hshC hGv hov hLv
      hJcv hlb (by omega) hoG hlbΛ hz hcap
    have : 1 ≤ (Λ + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact WExec.mono (WExec.ifrF hJcv e) (by omega)
  | succ j =>
    have hg1 : blocks.getD (j + 1) [] = blocks[j + 1] := List.getD_eq_getElem _ _ hj
    have hg0 : blocks.getD j [] = blocks[j] := List.getD_eq_getElem _ _ (by omega : j < blocks.length)
    have hjL' : j < L.length := by omega
    have hgL : L.getD j 0 = L[j] := List.getD_eq_getElem _ _ hjL'
    simp only [digToks, hg1, hg0, hgL] at hcap ⊢
    set A1 := linToks o blocks[j + 1]
    set A0 := linToks o blocks[j]
    -- 1. stage j + 1
    have c1 := TCap.left cap F (TCap.left cap F (TCap.left cap F hcap))
    have e1 := stP_run cap S F CW hSC Gr off LB Jc hG ho hL hJc G (j + 1) o lb Λ blocks hb hj restC σ h hstC hshC
      hGv hov hLv hJcv hlb hjΛ hoG hlbΛ hz c1
    set σ1 := emitT S F σ A1 with hσ1
    have h1 : TRest S F σ1 := h.emitT S F A1
    have v1 : ∀ r, r ≠ F 7 → r ≠ F 16 → σ1.val r = σ.val r := fun r a b => emitT_val_ne S F r a b σ A1
    -- 2. Jp := j
    have e2 := copyR_spec cap (v := Jc) (d := Jp) (t := F 8) hcp (hJc 8).symm (hJp 8).symm σ1
      (by rw [v1 _ (hne (by decide)) (hne (by decide))]; exact hz0 8 (by decide))
      (by rw [v1 _ (hJp 7).symm (hJp 16).symm, v1 _ (hJc 7).symm (hJc 16).symm, hJpv, hJcv]; unfold TCap at hcap; omega)
    rw [v1 _ (hJp 7).symm (hJp 16).symm, v1 _ (hJc 7).symm (hJc 16).symm, hJpv, hJcv, Nat.zero_add] at e2
    have e3 := WExec.dec (cap := cap) Jp (σ1.setv Jp (j + 1)) (by simp; unfold TCap at hcap; omega)
    simp only [WState.setv_val, Function.update_self, Nat.add_sub_cancel] at e3
    rw [wsetv_setv] at e3
    set σ3 := σ1.setv Jp j with hσ3
    -- 3. the rate a_j
    have c3 := TCap.left cap F (TCap.left cap F hcap)
    have c3' : TCap cap F σ3 [Tok.const (L[j] : ℤ)] Λ := by
      have := TCap.right cap S F c3; rw [hσ3]; exact this.setv cap F Jp hJp j
    have hlbf' : (encN (L.take (j + 1))).length ≤ lbf := hlbf
    have e4 := rateC_spec cap S F FA hFS LBF Jp hLF hJp hfp L restF j lbf Λ hjL' σ3 (h1.setv S F Jp hJp j)
      (by simp [hσ3, hσ1, emitT_st_ne S F FA hFS, hstF]) (by simp [hσ3, hσ1, emitT_sh_ne S F FA hFS, hshF])
      (by simp [hσ3]) (by rw [hσ3, WState.setv_val, Function.update_of_ne hfp, v1 _ (hLF 7).symm (hLF 16).symm, hLFv])
      hlbf' hlbfΛ (by omega) hLΛ
      (by unfold TCap at c3'
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at c3'
          rw [tokWord_const_nat] at c3'
          simp only [List.length_append] at c3' ⊢; omega)
      (by unfold TCap at hcap; omega) (fun x hx => by have := hLΛ x hx; unfold TCap at hcap; omega)
      (by unfold TCap at c3'; simp at c3'; omega)
    set σ4 := emitT S F σ3 [Tok.const (L[j] : ℤ)] with hσ4
    -- 4. stage j
    have c4 : TCap cap F σ4 A0 Λ := by
      have := TCap.right cap S F (TCap.left cap F hcap)
      rw [hσ4, hσ3, hσ1, emitT_setv S F Jp (hJp 7).symm (hJp 16).symm, emitT_append]
      exact this.setv cap F Jp hJp j
    have h4 : TRest S F σ4 := (h1.setv S F Jp hJp j).emitT S F _
    have v4 : ∀ r, r ≠ F 7 → r ≠ F 16 → r ≠ Jp → σ4.val r = σ.val r := fun r a b c => by
      rw [hσ4, emitT_val_ne S F r a b, hσ3, WState.setv_val, Function.update_of_ne c, v1 r a b]
    have e5 := stP_run cap S F CW hSC Gr off LB Jp hG ho hL hJp G j o lb Λ blocks hb (by omega) restC σ4 h4
      (by simp [hσ4, hσ3, hσ1, emitT_st_ne S F CW hSC.symm, hstC])
      (by simp [hσ4, hσ3, hσ1, emitT_sh_ne S F CW hSC.symm, hshC])
      (by rw [v4 _ (hG 7).symm (hG 16).symm hgp]; exact hGv)
      (by rw [v4 _ (ho 7).symm (ho 16).symm hop]; exact hov)
      (by rw [v4 _ (hL 7).symm (hL 16).symm hlp]; exact hLv)
      (by simp [hσ4, hσ3, emitT_val_ne S F Jp (hJp 7).symm (hJp 16).symm])
      (le_trans (encI_take_mono blocks (by omega)) hlb) (by omega) hoG hlbΛ hz c4
    set σ5 := emitT S F σ4 A0 with hσ5
    -- 5. clear Jp, then mul, sub
    have e6 := wclear_spec cap Jp j σ5 (by simp [hσ5, hσ4, hσ3, emitT_val_ne S F Jp (hJp 7).symm (hJp 16).symm])
      (by simp [hσ5, hσ4, hσ3, emitT_val_ne S F Jp (hJp 7).symm (hJp 16).symm]; unfold TCap at hcap; omega)
    set σ6 := σ5.setv Jp 0 with hσ6
    have h6 : TRest S F σ6 := (h4.emitT S F A0).setv S F Jp hJp 0
    have hσ6' : σ6 = emitT S F σ (A1 ++ [Tok.const (L[j] : ℤ)] ++ A0) := by
      rw [hσ6, hσ5, hσ4, hσ3, emitT_setv S F Jp (hJp 7).symm (hJp 16).symm,
        emitT_setv S F Jp (hJp 7).symm (hJp 16).symm, wsetv_setv, hσ1, emitT_append, emitT_append]
      have : (emitT S F σ (A1 ++ ([Tok.const (L[j] : ℤ)] ++ A0))).val Jp = 0 := by
        rw [emitT_val_ne S F Jp (hJp 7).symm (hJp 16).symm, hJpv]
      rw [← this, wsetv_same, List.append_assoc]
    have c7 := TCap.right cap S F hcap
    rw [← hσ6'] at c7
    have e7 := litC_spec cap S F .mul σ6 h6 (by unfold TCap at c7; simp at c7; omega)
      (by unfold TCap at c7; simp at c7; omega)
    have e8 := litC_spec cap S F .sub (emitT S F σ6 [Tok.mul]) (h6.emitT S F _)
      (by unfold TCap at c7; rw [emitT_val7]; simp at c7 ⊢; omega)
      (by unfold TCap at c7; rw [emitT_val16]; simp at c7 ⊢; omega)
    refine WExec.mono (WExec.ifrT (by rw [hJcv]; omega) (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3
      (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7 e8))))))) ?_ le_rfl)) ?_
    · rw [emitT_append, hσ6', emitT_append]; simp [List.append_assoc]
    · have hl1 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have hl2 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      rw [tokWord_mul_length, tokWord_sub_length]
      nlinarith

end Dig

end NearCubicGates.Close.CounterMachine
