import Proof.Wire_3_5.UnionMachineRegRatOps

/-! # C1.2: the product of two words (shift and add)

`mulB A B C S F R G` sets `C := a·b` (`A`, `B` kept; scratch word `S` back to `0`). The multiplier's bits are read
in place on `B`, low bit first (its head walks the frame, counted in `G`, then rewinds): at bit `i` the shifted
multiplicand `S = a·2^i` is added to `C` when the bit is set (`addB`), then doubled (`shlB`). After `i` bits,
`C = a·(b mod 2^i)` (**`mulBody_spec`**); every partial sum is at most `a·b < 2^W`, so no pass overflows
(**`mulB_spec`**). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort

variable {ns nr : ℕ}

/-! ## Bits of a framed word -/

theorem binary_getD : ∀ (w n i : ℕ), i < w → (binary w n).getD i false = (n / 2 ^ i % 2 == 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | w + 1, n, 0, _ => by simp [binary]
  | w + 1, n, i + 1, h => by
    have ih := binary_getD w (n / 2) i (by omega)
    simp only [binary, List.getD_cons_succ]
    rw [ih, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (2 ^ i) 2]

theorem readTapeBit_frameP_end : ∀ (ws rest : List Bool), readTapeBit (frameP ws ++ false :: rest) (2 * ws.length) = false
  | [], _ => rfl
  | w :: ws, rest => by
    have ih := readTapeBit_frameP_end ws rest
    simp only [frameP_cons, List.cons_append, List.length_cons]
    unfold readTapeBit at ih ⊢
    rw [show 2 * (ws.length + 1) = 2 * ws.length + 1 + 1 by omega]
    simpa using ih

/-- The bit of `b` at position `i` of its frame. -/
theorem frame_bit (W b i : ℕ) (hi : i < W) :
    readTapeBit (frame (binary W b)) (2 * i + 1) = (b / 2 ^ i % 2 == 1) := by
  rw [frame_eq_frameP, readTapeBit_frameP _ _ _ (by simpa using hi), binary_getD W b i hi]

theorem frame_marker (W b i : ℕ) (hi : i < W) : readTapeBit (frame (binary W b)) (2 * i) = true := by
  rw [frame_eq_frameP]; exact readTapeBit_frameP_marker _ _ _ (by simpa using hi)

theorem frame_end (W b : ℕ) : readTapeBit (frame (binary W b)) (2 * W) = false := by
  rw [frame_eq_frameP]
  have := readTapeBit_frameP_end (binary W b) []
  simpa using this

/-! ## The program -/

/-- One bit of the multiplier (head of `B` on its marker): `C += S` if the bit is set, then `S := 2S`. -/
def mulBody (A B C S : Fin (ns + 1)) (F R G : Fin nr) : WM ns nr :=
  .seq (.fwd B) (.seq (.inc G) (.seq (.ifs B (addB C S F R) .skip)
    (.seq (shlB S A F R) (.seq (.fwd B) (.inc G)))))

/-- **`C := a·b`**: clear `C`, load `S := a`, walk the bits of `B`, rewind `B`, clear `S`. -/
def mulB (A B C S : Fin (ns + 1)) (F R G : Fin nr) : WM ns nr :=
  .seq (zeroB C A F R) (.seq (copyB S A F R) (.seq (.whs B (mulBody A B C S F R G))
    (.seq (WM.rewind B G) (zeroB S A F R))))

/-- The state after `i` bits. -/
def mulSt (σ : WState ns nr) (B C S : Fin (ns + 1)) (G : Fin nr) (W a b i : ℕ) : WState ns nr :=
  (((σ.sets C (frame (binary W (a * (b % 2 ^ i))))).sets S (frame (binary W (a * 2 ^ i)))).seth B (2 * i)).setv G
    (2 * i)

section Mul
variable (cap W : ℕ) {A B C S : Fin (ns + 1)} {F R G : Fin nr}
  (hAB : A ≠ B) (hAC : A ≠ C) (hAS : A ≠ S) (hBC : B ≠ C) (hBS : B ≠ S) (hCS : C ≠ S)
  (hFR : F ≠ R) (hFG : F ≠ G) (hRG : R ≠ G)
include hAB hAC hAS hBC hBS hCS hFR hFG hRG

theorem mulSt_facts (σ : WState ns nr) (a b i : ℕ) :
    (mulSt σ B C S G W a b i).st A = σ.st A ∧ (mulSt σ B C S G W a b i).sh A = σ.sh A ∧
    (mulSt σ B C S G W a b i).st B = σ.st B ∧ (mulSt σ B C S G W a b i).sh B = 2 * i ∧
    (mulSt σ B C S G W a b i).st C = frame (binary W (a * (b % 2 ^ i))) ∧
    (mulSt σ B C S G W a b i).sh C = σ.sh C ∧
    (mulSt σ B C S G W a b i).st S = frame (binary W (a * 2 ^ i)) ∧ (mulSt σ B C S G W a b i).sh S = σ.sh S ∧
    (mulSt σ B C S G W a b i).val G = 2 * i ∧ (mulSt σ B C S G W a b i).val F = σ.val F ∧
    (mulSt σ B C S G W a b i).val R = σ.val R := by
  simp [mulSt, Function.update_apply, hAB, hAC, hAS, hBC, hBS, hCS, Ne.symm hAB, Ne.symm hAC, Ne.symm hAS,
    Ne.symm hBC, Ne.symm hBS, Ne.symm hCS, hFG, hRG]

/-- **One bit.** -/
theorem mulBody_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : σ.st B = frame (binary W b))
    (hC0 : σ.sh C = 0) (hS0 : σ.sh S = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hab : a * b < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) (i : ℕ) (hi : i < W) :
    WExec cap (mulBody A B C S F R G) (mulSt σ B C S G W a b i) (mulSt σ B C S G W a b (i + 1)) (82 * W + 30) := by
  obtain ⟨fA, fAh, fB, fBh, fC, fCh, fS, fSh, fG, fF, fR⟩ :=
    mulSt_facts W hAB hAC hAS hBC hBS hCS hFR hFG hRG σ a b i
  set τ0 := mulSt σ B C S G W a b i with hτ0
  have h1 := WExec.fwd (cap := cap) B τ0
  set τ1 := τ0.seth B (τ0.sh B + 1) with hτ1
  have h2 := WExec.inc (cap := cap) G τ1 (by simp [hτ1, fG]; omega)
  set τ2 := τ1.setv G (τ1.val G + 1) with hτ2
  have t2C : NumOn τ2 C W (a * (b % 2 ^ i)) := ⟨by simp [hτ2, hτ1, fC], by simp [hτ2, hτ1, Ne.symm hBC, fCh, hC0]⟩
  have t2S : NumOn τ2 S W (a * 2 ^ i) := ⟨by simp [hτ2, hτ1, fS], by simp [hτ2, hτ1, Ne.symm hBS, fSh, hS0]⟩
  have t2F : τ2.val F = 0 := by simp [hτ2, hτ1, hFG, fF, hF]
  have t2R : τ2.val R = 0 := by simp [hτ2, hτ1, hRG, fR, hR]
  have hbit : wbit τ2 B = (b / 2 ^ i % 2 == 1) := by
    simp only [wbit, hτ2, hτ1, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
      Function.update_self, fB, fBh, hB]
    exact frame_bit W b i hi
  have hmod : b % 2 ^ (i + 1) = b % 2 ^ i + 2 ^ i * (b / 2 ^ i % 2) := Nat.mod_pow_succ
  have hle : a * (b % 2 ^ (i + 1)) ≤ a * b := Nat.mul_le_mul_left a (Nat.mod_le b _)
  have h3 : WExec cap (.ifs B (addB C S F R) .skip) τ2 (τ2.sets C (frame (binary W (a * (b % 2 ^ (i + 1))))))
      (41 * W + 4) := by
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ i) with h0 | h1'
    · have e : a * (b % 2 ^ (i + 1)) = a * (b % 2 ^ i) := by rw [hmod, h0]; simp
      rw [e, show τ2.sets C (frame (binary W (a * (b % 2 ^ i)))) = τ2 by rw [← t2C.1]; exact wsets_same τ2 C]
      exact WExec.mono (WExec.ifsF (by rw [hbit, h0]; rfl) (WExec.skip τ2)) (by omega)
    · have e : a * (b % 2 ^ (i + 1)) = a * (b % 2 ^ i) + a * 2 ^ i := by rw [hmod, h1']; ring
      rw [e]
      have hs := addB_spec cap W hCS hFR τ2 (a * (b % 2 ^ i)) (a * 2 ^ i) t2C t2S t2F t2R (by omega) hcap
      exact WExec.mono (WExec.ifsT (by rw [hbit, h1']; rfl) hs) (by omega)
  set τ3 := τ2.sets C (frame (binary W (a * (b % 2 ^ (i + 1))))) with hτ3
  have t3S : NumOn τ3 S W (a * 2 ^ i) := ⟨by simp [hτ3, Ne.symm hCS, t2S.1], by simp [hτ3, t2S.2]⟩
  have t3A : NumOn τ3 A W a :=
    ⟨by simp [hτ3, hτ2, hτ1, hAC, fA, hA.1], by simp [hτ3, hτ2, hτ1, hAB, fAh, hA.2]⟩
  have h4 := shlB_spec cap W (Ne.symm hAS) hFR τ3 (a * 2 ^ i) a t3S t3A (by simp [hτ3, t2F])
    (by simp [hτ3, t2R]) hcap
  set τ4 := τ3.sets S (frame (binary W (2 * (a * 2 ^ i)))) with hτ4
  have h5 := WExec.fwd (cap := cap) B τ4
  set τ5 := τ4.seth B (τ4.sh B + 1) with hτ5
  have h6 := WExec.inc (cap := cap) G τ5 (by simp [hτ5, hτ4, hτ3, hτ2, hτ1, fG]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 h6))))) ?_
    (by omega)
  have e2 : 2 * (a * 2 ^ i) = a * 2 ^ (i + 1) := by rw [pow_succ]; ring
  simp only [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, mulSt, e2]
  apply WState.eq
  · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> omega
  · funext x; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all
  · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp_all <;> omega
  · rfl

/-- The loop over the multiplier's bits. -/
theorem mulLoop_spec (σ : WState ns nr) (a b : ℕ) (hA : NumOn σ A W a) (hB : σ.st B = frame (binary W b))
    (hC0 : σ.sh C = 0) (hS0 : σ.sh S = 0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hab : a * b < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    ∀ (k i : ℕ), i + k = W → WExec cap (.whs B (mulBody A B C S F R G)) (mulSt σ B C S G W a b i)
      (mulSt σ B C S G W a b W) (k * (82 * W + 32) + 1)
  | 0, i, h => by
    have hi : i = W := by omega
    rw [hi]
    obtain ⟨-, -, fB, fBh, -⟩ := mulSt_facts W hAB hAC hAS hBC hBS hCS hFR hFG hRG σ a b W
    refine WExec.mono (WExec.whsF ?_) (by omega)
    simp only [wbit, fB, fBh, hB]
    exact frame_end W b
  | k + 1, i, h => by
    obtain ⟨-, -, fB, fBh, -⟩ := mulSt_facts W hAB hAC hAS hBC hBS hCS hFR hFG hRG σ a b i
    have hb := mulBody_spec cap W hAB hAC hAS hBC hBS hCS hFR hFG hRG σ a b hA hB hC0 hS0 hF hR hab hcap i
      (by omega)
    have hl := mulLoop_spec σ a b hA hB hC0 hS0 hF hR hab hcap k (i + 1) (by omega)
    have hm : wbit (mulSt σ B C S G W a b i) B = true := by
      simp only [wbit, fB, fBh, hB]
      exact frame_marker W b i (by omega)
    refine WExec.mono (WExec.whsT hm hb hl) ?_
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- The product's cost. -/
def mulCost (W : ℕ) : ℕ := W * (82 * W + 32) + 133 * W + 15

/-- **The product**: `C := a·b`, the scratch word `S` back to `0`, `A` and `B` kept, `F`, `R`, `G` back to `0`. -/
theorem mulB_spec (σ : WState ns nr) (a b c s : ℕ) (hA : NumOn σ A W a) (hB : NumOn σ B W b)
    (hC : NumOn σ C W c) (hS : NumOn σ S W s) (hF : σ.val F = 0) (hR : σ.val R = 0) (hG : σ.val G = 0)
    (hab : a * b < 2 ^ W) (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (mulB A B C S F R G) σ ((σ.sets C (frame (binary W (a * b)))).sets S (frame (binary W 0)))
      (mulCost W) := by
  have z1 := zeroB_spec cap W (Ne.symm hAC) hFR σ c a hC hA hF hR hcap
  set σ1 := σ.sets C (frame (binary W 0)) with hσ1
  have c1 := copyB_spec cap W (Ne.symm hAS) hFR σ1 s a ⟨by simp [hσ1, Ne.symm hCS, hS.1], by simp [hσ1, hS.2]⟩
    ⟨by simp [hσ1, hAC, hA.1], by simp [hσ1, hA.2]⟩ (by simp [hσ1, hF]) (by simp [hσ1, hR]) hcap
  have e0 : σ1.sets S (frame (binary W a)) = mulSt σ B C S G W a b 0 := by
    simp only [hσ1, mulSt, pow_zero, Nat.mod_one, Nat.mul_zero, Nat.mul_one, Nat.mul_zero]
    apply WState.eq
    · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp [hB.2]
    · rfl
    · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp [hG]
    · rfl
  rw [e0] at c1
  have lp := mulLoop_spec cap W hAB hAC hAS hBC hBS hCS hFR hFG hRG σ a b hA hB.1 hC.2 hS.2 hF hR hab hcap W 0
    (by omega)
  obtain ⟨fA, fAh, fB, fBh, fC, fCh, fS, fSh, fG, fF, fR⟩ :=
    mulSt_facts W hAB hAC hAS hBC hBS hCS hFR hFG hRG σ a b W
  have rw1 := wrewind_spec cap B G (2 * W) (mulSt σ B C S G W a b W) fG (by omega)
  set τ := ((mulSt σ B C S G W a b W).setv G 0).seth B ((mulSt σ B C S G W a b W).sh B - 2 * W) with hτ
  have z2 := zeroB_spec cap W (Ne.symm hAS) hFR τ (a * 2 ^ W) a
    ⟨by simp [hτ, fS], by simp [hτ, Ne.symm hBS, fSh, hS.2]⟩ ⟨by simp [hτ, fA, hA.1], by simp [hτ, hAB, fAh, hA.2]⟩
    (by simp [hτ, hFG, fF, hF]) (by simp [hτ, hRG, fR, hR]) hcap
  refine WExec.cast cap (WExec.seq z1 (WExec.seq c1 (WExec.seq lp (WExec.seq rw1 z2)))) ?_ (by unfold mulCost; omega)
  have eb : b % 2 ^ W = b := Nat.mod_eq_of_lt hb
  simp only [hτ, mulSt, eb]
  apply WState.eq
  · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp [hB.2]
  · funext x; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all
  · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp [hG]
  · rfl

end Mul

end NearCubicWires.WireExponent3_5.UnionMachine.RegRat
