import Proof.Gates.CounterMachine.FormulaBinom

/-! # RG machine, part 17: the amplified residue formula

**`ampP_spec`**: the printer emits `ampToks e (tToks d)`, the tokens of `Amp_e(t)` (lem:amp) of the Fermat
product `t` (lem:residue-count): `t` is printed `e + 1` times by `tP`, the binomial constants `C(e−1+j, j)` are
stepped in a unary register (`binStep_spec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ} (cap : ℕ)

section Amp
variable (Y : Fin 8 ↪ Fin (ns + 1)) (X : Fin 24 ↪ Fin nr) (F : Fin 24 ↪ Fin nr)

/-- The registers the amplifier uses beyond the formula state are free (`0`). -/
def AmpFree (σ : WState ns nr) : Prop := ∀ i : Fin 24, i ∈ ([9, 10, 12, 13, 23] : List (Fin 24)) → σ.val (X i) = 0

def ampHead : WM ns nr :=
  .seq (litC (Y 0) F (.const 1)) (.seq (litC (Y 0) F (.const 1)) (.seq (tP Y X F) (.seq (litC (Y 0) F .sub)
    (powC (Y 0) F (X 8)))))

def ampBody : WM ns nr :=
  .seq (constRegC (Y 0) F (X 9)) (.seq (tP Y X F) (.seq (powC (Y 0) F (X 10)) (.seq (litC (Y 0) F .mul)
    (.seq (binStep (X 9) (X 10) (X 8) (X 13) (X 23) (F 8)) (.inc (X 10))))))

def ampLoop : WM ns nr :=
  .seq (.inc (X 9)) (.seq (copyR (X 8) (X 12) (F 8)) (.seq (repLoop (X 12) (ampBody Y X F))
    (.seq (WM.clear (X 10)) (WM.clear (X 9)))))

def ampTail : WM ns nr :=
  .seq (litC (Y 0) F (.const 0)) (.seq (copyR (X 8) (X 12) (F 8)) (.seq (repLoop (X 12) (litC (Y 0) F .add))
    (.seq (litC (Y 0) F .mul) (litC (Y 0) F .sub))))

/-- **The amplified formula printer.** -/
def ampP : WM ns nr := .seq (ampHead Y X F) (.seq (ampLoop Y X F) (ampTail Y X F))

/-- The binomial terms of `Amp_e(t)`. -/
def ampIters (e : ℕ) (t : List Tok) (m : ℕ) : List Tok :=
  ((List.range m).map fun j => [Tok.const (binom e j : ℤ)] ++ t ++ [Tok.pow j, Tok.mul]).flatten

theorem ampToks_eq (e : ℕ) (t : List Tok) :
    ampToks e t = ([Tok.const 1, Tok.const 1] ++ t ++ [Tok.sub, Tok.pow e]) ++ (ampIters e t e ++
      ([Tok.const 0] ++ List.replicate e Tok.add ++ [Tok.mul, Tok.sub])) := by
  simp [ampToks, ampIters, List.append_assoc]

theorem ampIters_succ (e : ℕ) (t : List Tok) (m : ℕ) :
    ampIters e t (m + 1) = ampIters e t m ++ ([Tok.const (binom e m : ℤ)] ++ t ++ [Tok.pow m, Tok.mul]) := by
  simp [ampIters, List.range_succ]

theorem tokWord_powC_le (v : ℕ) : (tokWord (Tok.pow v)).length = 7 + (natWord v).length := by
  simp [tokWord]; decide

theorem ampHead_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (hcap : TCap cap F σ ([Tok.const 1, Tok.const 1] ++ tToks d ++ [Tok.sub, Tok.pow d.e]) Λ) :
    WExec cap (ampHead Y X F) σ (emitT (Y 0) F σ ([Tok.const 1, Tok.const 1] ++ tToks d ++ [Tok.sub, Tok.pow d.e]))
      (110000 * (Λ + 1) ^ 4) := by
  have hFX := hs.disj
  have split : [Tok.const 1, Tok.const 1] ++ tToks d ++ [Tok.sub, Tok.pow d.e] =
      [Tok.const 1] ++ ([Tok.const 1] ++ (tToks d ++ ([Tok.sub] ++ [Tok.pow d.e]))) := by simp
  rw [split] at hcap ⊢
  have c1 := TCap.left cap F hcap
  have r1 := TCap.right cap (Y 0) F hcap
  have c2 := TCap.left cap F r1
  have r2 := TCap.right cap (Y 0) F r1
  have c3 := TCap.left cap F r2
  have r3 := TCap.right cap (Y 0) F r2
  have c4 := TCap.left cap F r3
  have c5 := TCap.right cap (Y 0) F r3
  have e1 := litC_spec cap (Y 0) F (.const 1) σ hs.rest (by unfold TCap at c1; simp at c1; omega)
    (by unfold TCap at c1; simp at c1; omega)
  set σ1 := emitT (Y 0) F σ [Tok.const 1]
  have hs1 := hs.emitT Y X F [Tok.const 1]
  have e2 := litC_spec cap (Y 0) F (.const 1) σ1 hs1.rest (by unfold TCap at c2; simp at c2; omega)
    (by unfold TCap at c2; simp at c2; omega)
  set σ2 := emitT (Y 0) F σ1 [Tok.const 1]
  have hs2 := hs1.emitT Y X F [Tok.const 1]
  have hr2 : FBoundR X σ2 Λ := (hr.emitT X F hFX (Y 0) _).emitT X F hFX (Y 0) _
  have e3 := tP_spec cap Y X F d Λ σ2 hs2 hb hρ hr2 c3
  set σ3 := emitT (Y 0) F σ2 (tToks d)
  have hs3 := hs2.emitT Y X F (tToks d)
  have e4 := litC_spec cap (Y 0) F .sub σ3 hs3.rest (by unfold TCap at c4; simp at c4; omega)
    (by unfold TCap at c4; simp at c4; omega)
  set σ4 := emitT (Y 0) F σ3 [Tok.sub]
  have hs4 := hs3.emitT Y X F [Tok.sub]
  have e5 := powC_spec cap (Y 0) F (X 8) (fun i => hFX i 8) σ4 hs4.rest
    (by rw [hs4.vE, show (natWord 6).length = 7 by decide]; unfold TCap at c5; have := hb.e; omega)
    (by unfold TCap at c5; simp at c5; omega)
  rw [hs4.vE] at e5
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ ?_
  · simp only [σ4, σ3, σ2, σ1, emitT_append, List.append_assoc]
  · have hp := printCost_le d.e Λ hb.e
    have e6 : (natWord 6).length = 7 := by decide
    rw [tokWord_const1_length, tokWord_sub_length, e6]
    have h2 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h0 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega

theorem AmpFree.emitT {σ : WState ns nr} (hFX : ∀ i j, F i ≠ X j) (h : AmpFree X σ) (S : Fin (ns + 1)) (ts : List Tok) :
    AmpFree X (emitT S F σ ts) := fun i hi => by
  rw [emitT_val_ne S F _ (hFX 7 i).symm (hFX 16 i).symm]; exact h i hi

theorem binom_zero (e : ℕ) : binom e 0 = 1 := by simp [binom]

/-- One binomial term `C_j t^j`, the binomial stepped, `j` advanced. -/
theorem ampBody_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (j : ℕ) (hj : j < d.e) (hbin : binom d.e j * (d.e + j) ≤ Λ) (h2e : 2 * d.e ≤ Λ)
    (h9 : σ.val (X 9) = binom d.e j) (h10 : σ.val (X 10) = j) (h13 : σ.val (X 13) = 0) (h23 : σ.val (X 23) = 0)
    (hcap : TCap cap F σ ([Tok.const (binom d.e j : ℤ)] ++ tToks d ++ [Tok.pow j, Tok.mul]) Λ) :
    WExec cap (ampBody Y X F) σ
      ((emitT (Y 0) F σ ([Tok.const (binom d.e j : ℤ)] ++ tToks d ++ [Tok.pow j, Tok.mul])).setv (X 10) (j + 1) |>.setv
        (X 9) (binom d.e (j + 1))) (110000 * (Λ + 1) ^ 4) := by
  have hFX := hs.disj
  have hXX : ∀ {a b : Fin 24}, a ≠ b → X a ≠ X b := fun h => X.injective.ne h
  have split : [Tok.const (binom d.e j : ℤ)] ++ tToks d ++ [Tok.pow j, Tok.mul] =
      [Tok.const (binom d.e j : ℤ)] ++ (tToks d ++ ([Tok.pow j] ++ [Tok.mul])) := by simp
  rw [split] at hcap ⊢
  have c1 := TCap.left cap F hcap
  have r1 := TCap.right cap (Y 0) F hcap
  have c2 := TCap.left cap F r1
  have r2 := TCap.right cap (Y 0) F r1
  have c3 := TCap.left cap F r2
  have c4 := TCap.right cap (Y 0) F r2
  have hbΛ : binom d.e j ≤ Λ := by
    have : binom d.e j ≤ binom d.e j * (d.e + j) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have e1 := constRegC_spec cap (Y 0) F (X 9) (fun i => hFX i 9) σ hs.rest
    (by rw [h9, show (natWord 0).length = 3 by decide]; unfold TCap at c1; omega)
    (by unfold TCap at c1; simp at c1; omega)
  rw [h9] at e1
  set σ1 := emitT (Y 0) F σ [Tok.const (binom d.e j : ℤ)]
  have hs1 := hs.emitT Y X F [Tok.const (binom d.e j : ℤ)]
  have e2 := tP_spec cap Y X F d Λ σ1 hs1 hb hρ (hr.emitT X F hFX (Y 0) _) c2
  set σ2 := emitT (Y 0) F σ1 (tToks d)
  have hs2 := hs1.emitT Y X F (tToks d)
  have v2 : ∀ i, σ2.val (X i) = σ.val (X i) := fun i => by
    simp only [σ2, σ1]; rw [emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm,
      emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm]
  have e3 := powC_spec cap (Y 0) F (X 10) (fun i => hFX i 10) σ2 hs2.rest
    (by rw [v2, h10, show (natWord 6).length = 7 by decide]; unfold TCap at c3; omega)
    (by unfold TCap at c3; simp at c3; omega)
  rw [v2, h10] at e3
  set σ3 := emitT (Y 0) F σ2 [Tok.pow j]
  have hs3 := hs2.emitT Y X F [Tok.pow j]
  have e4 := litC_spec cap (Y 0) F .mul σ3 hs3.rest (by unfold TCap at c4; simp at c4; omega)
    (by unfold TCap at c4; simp at c4; omega)
  set σ4 := emitT (Y 0) F σ3 [Tok.mul]
  have v4 : ∀ i, σ4.val (X i) = σ.val (X i) := fun i => by
    simp only [σ4, σ3]; rw [emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm,
      emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm, v2]
  have h8 : σ4.val (F 8) = 0 := by
    simp only [σ4, σ3, σ2, σ1]
    rw [emitT_val_ne (Y 0) F _ (F.injective.ne (by decide)) (F.injective.ne (by decide)),
      emitT_val_ne (Y 0) F _ (F.injective.ne (by decide)) (F.injective.ne (by decide)),
      emitT_val_ne (Y 0) F _ (F.injective.ne (by decide)) (F.injective.ne (by decide)),
      emitT_val_ne (Y 0) F _ (F.injective.ne (by decide)) (F.injective.ne (by decide))]
    exact hs.rest.zero (Y 0) F 8 (by decide)
  have e5 := binStep_spec cap (X 9) (X 10) (X 8) (X 13) (X 23) (F 8)
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
          not_false_eq_true]
        exact ⟨⟨hXX (by decide), hXX (by decide), hXX (by decide), hXX (by decide), (hFX 8 9).symm⟩,
          ⟨hXX (by decide), hXX (by decide), hXX (by decide), (hFX 8 10).symm⟩,
          ⟨hXX (by decide), hXX (by decide), (hFX 8 8).symm⟩, ⟨hXX (by decide), (hFX 8 13).symm⟩, (hFX 8 23).symm⟩)
    d.e j Λ (by omega) σ4 (by rw [v4, h9]) (by rw [v4, h10]) (by rw [v4, hs.vE]) (by rw [v4, h13]) (by rw [v4, h23])
    h8 hbin (by omega) (by unfold TCap at hcap; omega)
  have e6 := WExec.inc (cap := cap) (X 10) (σ4.setv (X 9) (binom d.e (j + 1)))
    (by simp [Function.update_of_ne (hXX (show (10 : Fin 24) ≠ 9 by decide)), v4, h10]; unfold TCap at hcap; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ ?_
  · have hE : σ4 = emitT (Y 0) F σ ([Tok.const (binom d.e j : ℤ)] ++ (tToks d ++ ([Tok.pow j] ++ [Tok.mul]))) := by
      simp only [σ4, σ3, σ2, σ1, emitT_append, List.append_assoc]
    rw [← hE]
    apply WState.eq <;> try rfl
    funext r; by_cases r10 : r = X 10
    · subst r10; simp [Function.update_of_ne (hXX (show (10 : Fin 24) ≠ 9 by decide)), v4, h10]
    · by_cases r9 : r = X 9
      · subst r9; simp [Function.update_of_ne (hXX (show (9 : Fin 24) ≠ 10 by decide))]
      · simp [Function.update_of_ne r10, Function.update_of_ne r9]
  · have hp1 := printCost_le (binom d.e j) Λ hbΛ
    have hp2 := printCost_le j Λ (by omega)
    rw [show (natWord 0).length = 3 by decide, show (natWord 6).length = 7 by decide, tokWord_mul_length]
    have h2 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega

theorem ampIters_prefix (e : ℕ) (t : List Tok) {k m : ℕ} (h : k ≤ m) :
    ∃ rest, ampIters e t m = ampIters e t k ++ rest := by
  induction m with
  | zero => exact ⟨[], by rw [show k = 0 by omega]; simp⟩
  | succ m ih =>
    by_cases hk : k = m + 1
    · exact ⟨[], by rw [hk]; simp⟩
    · obtain ⟨r, hr⟩ := ih (by omega)
      exact ⟨r ++ ([Tok.const (binom e m : ℤ)] ++ t ++ [Tok.pow m, Tok.mul]), by
        rw [ampIters_succ, hr, List.append_assoc]⟩

theorem binom_e_e_le (e Λ : ℕ) (hbin : ∀ j < e, binom e j * (e + j) ≤ Λ) : binom e e ≤ Λ + 1 := by
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0; simp [binom]
  · have h := binom_succ e (e - 1) hpos
    rw [show e - 1 + 1 = e by omega] at h
    have := hbin (e - 1) (by omega)
    have : binom e e ≤ binom e e * e := Nat.le_mul_of_pos_right _ hpos
    omega

theorem ampLoop_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (hf : AmpFree X σ) (hbin : ∀ j < d.e, binom d.e j * (d.e + j) ≤ Λ) (h2e : 2 * d.e ≤ Λ)
    (hcap : TCap cap F σ (ampIters d.e (tToks d) d.e) Λ) :
    WExec cap (ampLoop Y X F) σ (emitT (Y 0) F σ (ampIters d.e (tToks d) d.e)) (130000 * (Λ + 1) ^ 5) := by
  have hFX := hs.disj
  have hXX : ∀ {a b : Fin 24}, a ≠ b → X a ≠ X b := fun h => X.injective.ne h
  set e := d.e with he
  set t := tToks d
  have hcapc : Λ + 2 ≤ cap := by unfold TCap at hcap; omega
  -- 1. b := 1, K := e
  have s1 := WExec.inc (cap := cap) (X 9) σ (by rw [hf 9 (by decide)]; omega)
  rw [hf 9 (by decide)] at s1
  have s2 := copyR_spec cap (v := X 8) (d := X 12) (t := F 8) (hXX (by decide)) (hFX 8 8).symm (hFX 8 12).symm
    (σ.setv (X 9) (0 + 1)) (by simp [Function.update_of_ne (hFX 8 9)]; exact hs.rest.zero (Y 0) F 8 (by decide))
    (by simp [Function.update_of_ne (hXX (show (12 : Fin 24) ≠ 9 by decide)),
          Function.update_of_ne (hXX (show (8 : Fin 24) ≠ 9 by decide)), hf 12 (by decide), hs.vE]; omega)
  simp only [WState.setv_val, Function.update_of_ne (hXX (show (12 : Fin 24) ≠ 9 by decide)),
    Function.update_of_ne (hXX (show (8 : Fin 24) ≠ 9 by decide)), hf 12 (by decide), hs.vE, Nat.zero_add] at s2
  -- 2. the loop
  let g : ℕ → WState ns nr := fun j =>
    (((emitT (Y 0) F σ (ampIters e t j)).setv (X 10) j).setv (X 9) (binom e j)).setv (X 12) (e - j)
  have hg0 : (σ.setv (X 9) 1).setv (X 12) e = g 0 := by
    simp only [g, Nat.sub_zero, binom_zero]
    rw [show ampIters e t 0 = [] by simp [ampIters], emitT_nil (Y 0) F σ hs.rest.pr.out]
    apply WState.eq <;> try rfl
    funext r; by_cases r12 : r = X 12
    · subst r12; simp
    · by_cases r9 : r = X 9
      · subst r9; simp [Function.update_of_ne r12]
      · by_cases r10 : r = X 10
        · subst r10; simp [Function.update_of_ne r12, Function.update_of_ne r9, hf 10 (by decide)]
        · simp [Function.update_of_ne r12, Function.update_of_ne r9, Function.update_of_ne r10]
  rw [hg0] at s2
  have hbody : ∀ j < e, WExec cap (ampBody Y X F) ((g j).setv (X 12) (e - j - 1)) (g (j + 1))
      (110000 * (Λ + 1) ^ 4) := by
    intro j hj
    simp only [g]
    rw [wsetv_setv]
    set S0 := emitT (Y 0) F σ (ampIters e t j)
    have hS0 := hs.emitT Y X F (ampIters e t j)
    have hS1 := ((hS0.setv_free Y X F 10 (by decide) j).setv_free Y X F 9 (by decide) (binom e j)).setv_free Y X F 12
      (by decide) (e - j - 1)
    have hr1 := (((hr.emitT X F hFX (Y 0) (ampIters e t j)).setv_free X 10 (by decide) j).setv_free X 9 (by decide)
      (binom e j)).setv_free X 12 (by decide) (e - j - 1)
    obtain ⟨rest, hrest⟩ := ampIters_prefix e t (show j + 1 ≤ e by omega)
    rw [hrest, ampIters_succ, List.append_assoc] at hcap
    have cj := TCap.left cap F (TCap.right cap (Y 0) F hcap)
    have cj' := ((cj.setv cap F (X 10) (fun i => hFX i 10) j).setv cap F (X 9) (fun i => hFX i 9) (binom e j)).setv cap F
      (X 12) (fun i => hFX i 12) (e - j - 1)
    have vX : ∀ i : Fin 24, i ∉ ([9, 10, 12] : List (Fin 24)) →
        (((S0.setv (X 10) j).setv (X 9) (binom e j)).setv (X 12) (e - j - 1)).val (X i) = σ.val (X i) := by
      intro i hi
      have h9 : i ≠ 9 := fun h => hi (by simp [h])
      have h10 : i ≠ 10 := fun h => hi (by simp [h])
      have h12 : i ≠ 12 := fun h => hi (by simp [h])
      simp only [WState.setv_val, Function.update_of_ne (hXX h9), Function.update_of_ne (hXX h10),
        Function.update_of_ne (hXX h12)]
      exact emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm σ _
    have e1 := ampBody_spec cap Y X F d Λ _ hS1 hb hρ hr1 j hj (hbin j hj) h2e
      (by simp [Function.update_of_ne (hXX (show (9 : Fin 24) ≠ 12 by decide)), he])
      (by simp [Function.update_of_ne (hXX (show (10 : Fin 24) ≠ 12 by decide)),
            Function.update_of_ne (hXX (show (10 : Fin 24) ≠ 9 by decide))])
      (by rw [vX 13 (by decide)]; exact hf 13 (by decide)) (by rw [vX 23 (by decide)]; exact hf 23 (by decide)) cj'
    refine WExec.cast cap e1 ?_ le_rfl
    rw [emitT_setv (Y 0) F (X 12) (hFX 7 12).symm (hFX 16 12).symm, emitT_setv (Y 0) F (X 9) (hFX 7 9).symm
      (hFX 16 9).symm, emitT_setv (Y 0) F (X 10) (hFX 7 10).symm (hFX 16 10).symm, emitT_append, ← ampIters_succ]
    generalize emitT (Y 0) F σ (ampIters e t (j + 1)) = E
    apply WState.eq <;> try rfl
    funext r; by_cases r12 : r = X 12
    · subst r12; simp [Function.update_of_ne (hXX (show (12 : Fin 24) ≠ 9 by decide)),
        Function.update_of_ne (hXX (show (12 : Fin 24) ≠ 10 by decide))]; omega
    · by_cases r9 : r = X 9
      · subst r9; simp [Function.update_of_ne r12, he]
      · by_cases r10 : r = X 10
        · subst r10; simp [Function.update_of_ne r12, Function.update_of_ne r9]
        · simp [Function.update_of_ne r12, Function.update_of_ne r9, Function.update_of_ne r10]
  have s3 := repLoop_spec cap (X 12) (ampBody Y X F) e (110000 * (Λ + 1) ^ 4) g (fun i _ => by simp [g])
    (by omega) hbody
  -- 3. clear `j` and the binomial
  have hbe := binom_e_e_le e Λ hbin
  have s4 := wclear_spec cap (X 10) e (g e) (by simp [g, Function.update_of_ne (hXX (show (10 : Fin 24) ≠ 12 by decide)),
      Function.update_of_ne (hXX (show (10 : Fin 24) ≠ 9 by decide))]) (by
      simp [g, Function.update_of_ne (hXX (show (10 : Fin 24) ≠ 12 by decide)),
        Function.update_of_ne (hXX (show (10 : Fin 24) ≠ 9 by decide))]; omega)
  have s5 := wclear_spec cap (X 9) (binom e e) ((g e).setv (X 10) 0)
    (by simp [g, Function.update_of_ne (hXX (show (9 : Fin 24) ≠ 12 by decide)),
      Function.update_of_ne (hXX (show (9 : Fin 24) ≠ 10 by decide))]) (by
      simp [g, Function.update_of_ne (hXX (show (9 : Fin 24) ≠ 12 by decide)),
        Function.update_of_ne (hXX (show (9 : Fin 24) ≠ 10 by decide))]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · simp only [g, Nat.sub_self]
    have h9 : (emitT (Y 0) F σ (ampIters e t e)).val (X 9) = 0 := by
      rw [emitT_val_ne (Y 0) F _ (hFX 7 9).symm (hFX 16 9).symm]; exact hf 9 (by decide)
    have h10 : (emitT (Y 0) F σ (ampIters e t e)).val (X 10) = 0 := by
      rw [emitT_val_ne (Y 0) F _ (hFX 7 10).symm (hFX 16 10).symm]; exact hf 10 (by decide)
    have h12 : (emitT (Y 0) F σ (ampIters e t e)).val (X 12) = 0 := by
      rw [emitT_val_ne (Y 0) F _ (hFX 7 12).symm (hFX 16 12).symm]; exact hf 12 (by decide)
    generalize emitT (Y 0) F σ (ampIters e t e) = E at h9 h10 h12 ⊢
    apply WState.eq <;> try rfl
    funext r; by_cases r12 : r = X 12
    · subst r12; simp [Function.update_of_ne (hXX (show (12 : Fin 24) ≠ 9 by decide)),
        Function.update_of_ne (hXX (show (12 : Fin 24) ≠ 10 by decide)), h12]
    · by_cases r9 : r = X 9
      · subst r9; simp [h9]
      · by_cases r10 : r = X 10
        · subst r10; simp [Function.update_of_ne r9, h10]
        · simp [Function.update_of_ne r12, Function.update_of_ne r9, Function.update_of_ne r10]
  · have h4 : (Λ + 1) ^ 4 ≤ (Λ + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 1 ≤ (Λ + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have he' : e * (110000 * (Λ + 1) ^ 4 + 4) ≤ (Λ + 1) * (110000 * (Λ + 1) ^ 4 + 4) :=
      Nat.mul_le_mul_right _ (by omega)
    have : (Λ + 1) ^ 5 = (Λ + 1) * (Λ + 1) ^ 4 := by ring
    nlinarith

theorem TCap.lit {σ : WState ns nr} {t : Tok} {Λ : ℕ} (h : TCap cap F σ [t] Λ) :
    σ.val (F 7) + 2 * (tokWord t).length ≤ cap ∧ σ.val (F 16) < cap := by
  unfold TCap at h; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
    List.length_nil] at h; omega

theorem ampTail_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ)
    (hf : AmpFree X σ) (hcap : TCap cap F σ ([Tok.const 0] ++ List.replicate d.e Tok.add ++ [Tok.mul, Tok.sub]) Λ) :
    WExec cap (ampTail Y X F) σ (emitT (Y 0) F σ ([Tok.const 0] ++ List.replicate d.e Tok.add ++ [Tok.mul, Tok.sub]))
      (1000 * (Λ + 1)) := by
  have hFX := hs.disj
  have hXX : ∀ {a b : Fin 24}, a ≠ b → X a ≠ X b := fun h => X.injective.ne h
  have split : [Tok.const 0] ++ List.replicate d.e Tok.add ++ [Tok.mul, Tok.sub] =
      [Tok.const 0] ++ (List.replicate d.e Tok.add ++ ([Tok.mul] ++ [Tok.sub])) := by simp
  rw [split] at hcap ⊢
  have c1 := TCap.left cap F hcap
  have r1 := TCap.right cap (Y 0) F hcap
  have c2 := TCap.left cap F r1
  have r2 := TCap.right cap (Y 0) F r1
  have c3 := TCap.left cap F r2
  have c4 := TCap.right cap (Y 0) F r2
  have he := hb.e
  have e1 := litC_spec cap (Y 0) F (.const 0) σ hs.rest (by unfold TCap at c1; simp at c1; omega)
    (by unfold TCap at c1; simp at c1; omega)
  set σ1 := emitT (Y 0) F σ [Tok.const 0]
  have hs1 := hs.emitT Y X F [Tok.const 0]
  have v1 : ∀ i, σ1.val (X i) = σ.val (X i) := fun i => emitT_val_ne (Y 0) F _ (hFX 7 i).symm (hFX 16 i).symm σ _
  have e2 := copyR_spec cap (v := X 8) (d := X 12) (t := F 8) (hXX (by decide)) (hFX 8 8).symm (hFX 8 12).symm σ1
    (hs1.rest.zero (Y 0) F 8 (by decide)) (by rw [v1, v1, hf 12 (by decide), hs.vE]; unfold TCap at hcap; omega)
  rw [v1, v1, hf 12 (by decide), hs.vE, Nat.zero_add] at e2
  have e3 := litLoop_spec cap (Y 0) F (X 12) (fun i => hFX i 12) .add d.e (σ1.setv (X 12) d.e)
    (hs1.rest.setv (Y 0) F (X 12) (fun i => hFX i 12) _) (by simp)
    (by simp only [WState.setv_val, Function.update_of_ne (hFX 7 12)]; unfold TCap at c2
        rw [replicate_words, show (tokWord .add).length = 5 by decide] at c2
        rw [show (tokWord .add).length = 5 by decide]; omega)
    (by simp only [WState.setv_val, Function.update_of_ne (hFX 16 12)]; unfold TCap at c2; simp at c2; omega)
  set σ3 := (emitT (Y 0) F (σ1.setv (X 12) d.e) (List.replicate d.e Tok.add)).setv (X 12) 0
  have hσ3 : σ3 = emitT (Y 0) F σ1 (List.replicate d.e Tok.add) := by
    simp only [σ3]; rw [emitT_setv (Y 0) F (X 12) (hFX 7 12).symm (hFX 16 12).symm, wsetv_setv]
    rw [show (0 : ℕ) = (emitT (Y 0) F σ1 (List.replicate d.e Tok.add)).val (X 12) by
      rw [emitT_val_ne (Y 0) F _ (hFX 7 12).symm (hFX 16 12).symm, v1, hf 12 (by decide)], wsetv_same]
  rw [hσ3] at e3
  have hs3 := hs1.emitT Y X F (List.replicate d.e Tok.add)
  have e4 := litC_spec cap (Y 0) F .mul _ hs3.rest (TCap.lit cap F c3).1 (TCap.lit cap F c3).2
  have e5 := litC_spec cap (Y 0) F .sub _ (hs3.rest.emitT (Y 0) F [Tok.mul]) (TCap.lit cap F c4).1
    (TCap.lit cap F c4).2
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ ?_
  · simp only [σ1, emitT_append, List.append_assoc]
  · rw [tokWord_mul_length, tokWord_sub_length, show (tokWord (.const 0)).length = 9 by decide,
      show (tokWord .add).length = 5 by decide]
    omega

/-- **The amplified formula printer** from the formula state. -/
theorem ampP_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (hf : AmpFree X σ) (hbin : ∀ j < d.e, binom d.e j * (d.e + j) ≤ Λ) (h2e : 2 * d.e ≤ Λ)
    (hcap : TCap cap F σ (ampToks d.e (tToks d)) Λ) :
    WExec cap (ampP Y X F) σ (emitT (Y 0) F σ (ampToks d.e (tToks d))) (300000 * (Λ + 1) ^ 5) := by
  have hFX := hs.disj
  rw [ampToks_eq] at hcap ⊢
  have c1 := TCap.left cap F hcap
  have r1 := TCap.right cap (Y 0) F hcap
  have c2 := TCap.left cap F r1
  have r2 := TCap.right cap (Y 0) F r1
  have e1 := ampHead_spec cap Y X F d Λ σ hs hb hρ hr c1
  set H := [Tok.const 1, Tok.const 1] ++ tToks d ++ [Tok.sub, Tok.pow d.e]
  have hs1 := hs.emitT Y X F H
  have e2 := ampLoop_spec cap Y X F d Λ _ hs1 hb hρ (hr.emitT X F hFX (Y 0) H) (hf.emitT X F hFX (Y 0) H) hbin h2e c2
  have hs2 := hs1.emitT Y X F (ampIters d.e (tToks d) d.e)
  have e3 := ampTail_spec cap Y X F d Λ _ hs2 hb ((hf.emitT X F hFX (Y 0) H).emitT X F hFX (Y 0) _) r2
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ ?_
  · rw [emitT_append, emitT_append]
  · have h4 : (Λ + 1) ^ 4 ≤ (Λ + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : Λ + 1 ≤ (Λ + 1) ^ 5 := by
      have := Nat.pow_le_pow_right (show 1 ≤ Λ + 1 by omega) (show 1 ≤ 5 by omega); simpa using this
    omega

end Amp

end NearCubicGates.Close.CounterMachine
