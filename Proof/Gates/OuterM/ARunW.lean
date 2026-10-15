import Proof.Gates.OuterM.Walk
import Proof.Gates.Succinct.Arith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Register arithmetic -/

/-- `r := r + j`. -/
def incG (r : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | j + 1 => .seq (.inc r) (incG r j)

theorem incG_spec (r : Fin nr) : ∀ (j : ℕ) (σ : WState ns nr), σ.val r + j ≤ cap →
    WExec cap (incG r j) σ (σ.setv r (σ.val r + j)) (4 * j)
  | 0, σ, _ => by
    rw [Nat.add_zero, wsetv_same]
    exact WExec.skip σ
  | j + 1, σ, h => by
    have e1 := WExec.inc (cap := cap) r σ (by omega)
    have e2 := incG_spec r j (σ.setv r (σ.val r + 1)) (by simp; omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
    rw [wsetv_setv]; simp; ring_nf

/-- `B += A`, `C += A`, `A := 0`. -/
def spread2 (A B C : Fin nr) : WM ns nr := .whr A (.seq (.dec A) (.seq (.inc B) (.inc C)))

theorem spread2_spec (A B C : Fin nr) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val A = n → σ.val B + n ≤ cap → σ.val C + n ≤ cap → n ≤ cap →
      WExec cap (spread2 A B C) σ (((σ.setv A 0).setv B (σ.val B + n)).setv C (σ.val C + n)) (11 * n + 1)
  | 0, σ, hA, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hA) ?_ (by omega)
    rw [Nat.add_zero, Nat.add_zero, ← hA, wsetv_same, wsetv_same, wsetv_same]
  | n + 1, σ, hA, hB, hC, hn => by
    have e1 := WExec.dec (cap := cap) A σ (by omega)
    set σ1 := σ.setv A (σ.val A - 1) with hσ1
    have e2 := WExec.inc (cap := cap) B σ1 (by simp [σ1, Function.update_apply, Ne.symm hAB]; omega)
    set σ2 := σ1.setv B (σ1.val B + 1) with hσ2
    have e3 := WExec.inc (cap := cap) C σ2 (by simp [σ2, σ1, Function.update_apply, Ne.symm hAC, Ne.symm hBC]; omega)
    set σ3 := σ2.setv C (σ2.val C + 1) with hσ3
    have ih := spread2_spec A B C hAB hAC hBC n σ3 (by simp [σ3, σ2, σ1, Function.update_apply, hAB, hAC, hA])
      (by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hAB, hBC]; omega)
      (by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hAC, Ne.symm hBC]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by omega)
    simp only [σ3, σ2, σ1]
    refine WState.eq rfl rfl ?_ rfl
    funext x
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega

/-- `B += A`, `C += A`, `D += A`, `A := 0`. -/
def spread3 (A B C D : Fin nr) : WM ns nr := .whr A (.seq (.dec A) (.seq (.inc B) (.seq (.inc C) (.inc D))))

theorem spread3_spec (A B C D : Fin nr) (h1 : A ≠ B) (h2 : A ≠ C) (h3 : A ≠ D) (h4 : B ≠ C) (h5 : B ≠ D)
    (h6 : C ≠ D) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val A = n → σ.val B + n ≤ cap → σ.val C + n ≤ cap → σ.val D + n ≤ cap →
      n ≤ cap →
      WExec cap (spread3 A B C D) σ ((((σ.setv A 0).setv B (σ.val B + n)).setv C (σ.val C + n)).setv D (σ.val D + n))
        (15 * n + 1)
  | 0, σ, hA, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hA) ?_ (by omega)
    rw [Nat.add_zero, Nat.add_zero, Nat.add_zero, ← hA, wsetv_same, wsetv_same, wsetv_same, wsetv_same]
  | n + 1, σ, hA, hB, hC, hD, hn => by
    have e1 := WExec.dec (cap := cap) A σ (by omega)
    set σ1 := σ.setv A (σ.val A - 1) with hσ1
    have e2 := WExec.inc (cap := cap) B σ1 (by simp [σ1, Function.update_apply, Ne.symm h1]; omega)
    set σ2 := σ1.setv B (σ1.val B + 1) with hσ2
    have e3 := WExec.inc (cap := cap) C σ2 (by simp [σ2, σ1, Function.update_apply, Ne.symm h2, Ne.symm h4]; omega)
    set σ3 := σ2.setv C (σ2.val C + 1) with hσ3
    have e4 := WExec.inc (cap := cap) D σ3 (by
      simp [σ3, σ2, σ1, Function.update_apply, Ne.symm h3, Ne.symm h5, Ne.symm h6]; omega)
    set σ4 := σ3.setv D (σ3.val D + 1) with hσ4
    have ih := spread3_spec A B C D h1 h2 h3 h4 h5 h6 n σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, h1, h2, h3, hA])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm h1, h4, h5]; omega)
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm h2, Ne.symm h4, h6]; omega)
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm h3, Ne.symm h5, Ne.symm h6]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih) ?_ (by omega)
    simp only [σ4, σ3, σ2, σ1]
    refine WState.eq rfl rfl ?_ rfl
    funext x
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega

/-- `B += c·A`, `A := 0`. -/
def mulC (A B : Fin nr) (c : ℕ) : WM ns nr := .whr A (.seq (.dec A) (incG B c))

theorem mulC_spec (A B : Fin nr) (hAB : A ≠ B) (c : ℕ) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val A = n → σ.val B + n * c ≤ cap → n ≤ cap →
      WExec cap (mulC A B c) σ ((σ.setv A 0).setv B (σ.val B + n * c)) (n * (4 * c + 4) + 1)
  | 0, σ, hA, _, _ => by
    refine WExec.cast cap (WExec.whrF hA) ?_ (by omega)
    rw [Nat.zero_mul, Nat.add_zero, ← hA, wsetv_same, wsetv_same]
  | n + 1, σ, hA, hB, hn => by
    have e1 := WExec.dec (cap := cap) A σ (by omega)
    set σ1 := σ.setv A (σ.val A - 1) with hσ1
    have e2 := incG_spec cap B c σ1 (by simp [σ1, Function.update_apply, Ne.symm hAB]; nlinarith)
    set σ2 := σ1.setv B (σ1.val B + c) with hσ2
    have ih := mulC_spec A B hAB c n σ2 (by simp [σ2, σ1, Function.update_apply, hAB, hA])
      (by simp [σ2, σ1, Function.update_apply, Ne.symm hAB]; nlinarith) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih) ?_ (by nlinarith)
    simp only [σ2, σ1]
    have hm : (n + 1) * c = n * c + c := by ring
    refine WState.eq rfl rfl ?_ rfl
    funext x
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega

/-- `B := B − A` (truncated), `A := 0`. -/
def subL (A B : Fin nr) : WM ns nr := .whr A (.seq (.dec A) (.dec B))

theorem subL_spec (A B : Fin nr) (hAB : A ≠ B) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val A = n → σ.val B ≤ cap → n ≤ cap →
      WExec cap (subL A B) σ ((σ.setv A 0).setv B (σ.val B - n)) (5 * n + 1)
  | 0, σ, hA, _, _ => by
    refine WExec.cast cap (WExec.whrF hA) ?_ (by omega)
    rw [Nat.sub_zero, ← hA, wsetv_same, wsetv_same]
  | n + 1, σ, hA, hB, hn => by
    have e1 := WExec.dec (cap := cap) A σ (by omega)
    set σ1 := σ.setv A (σ.val A - 1) with hσ1
    have e2 := WExec.dec (cap := cap) B σ1 (by simp [σ1, Function.update_apply, Ne.symm hAB]; omega)
    set σ2 := σ1.setv B (σ1.val B - 1) with hσ2
    have ih := subL_spec A B hAB n σ2 (by simp [σ2, σ1, Function.update_apply, hAB, hA])
      (by simp [σ2, σ1, Function.update_apply, Ne.symm hAB]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih) ?_ (by omega)
    simp only [σ2, σ1]
    refine WState.eq rfl rfl ?_ rfl
    funext x
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega

/-! ## Streams -/

theorem writeTapeBit_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [writeTapeBit] using ih

/-- Write the scanned bit of `D` at the head of `S`. -/
theorem wrBit_spec (D S : Fin (ns + 1)) (σ : WState ns nr) :
    WExec cap (.ifs D (.wr S true) (.wr S false)) σ (σ.sets S (writeTapeBit (σ.st S) (σ.sh S) (wbit σ D))) 2 := by
  cases h : wbit σ D
  · exact WExec.ifsF h (WExec.wr S false σ)
  · exact WExec.ifsT h (WExec.wr S true σ)

theorem ofFn_succ_read (d : List Bool) (h n : ℕ) :
    (readTapeBit d h :: List.ofFn fun i : Fin n => readTapeBit d (h + 1 + i.val)) =
      List.ofFn fun i : Fin (n + 1) => readTapeBit d (h + i.val) := by
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
  congr 2
  funext i
  congr 1
  omega

/-- Copy `n` cells of `D` (from its head) onto the end of `S`, counting in `CS`; `K := 0`. -/
def cpyC (D S : Fin (ns + 1)) (K CS : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (.ifs D (.wr S true) (.wr S false)) (.seq (.fwd D) (WM.fwdC S CS))))

theorem cpyC_spec (D S : Fin (ns + 1)) (K CS : Fin nr) (hDS : D ≠ S) (hK : K ≠ CS) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val K = n → σ.sh S = (σ.st S).length → σ.val CS + n ≤ cap → n ≤ cap →
      WExec cap (cpyC D S K CS) σ
        (((((σ.sets S (σ.st S ++ List.ofFn fun i : Fin n => readTapeBit (σ.st D) (σ.sh D + i.val))).seth S
          ((σ.st S).length + n)).seth D (σ.sh D + n)).setv CS (σ.val CS + n)).setv K 0) (14 * n + 1)
  | 0, σ, hK0, hS, _, _ => by
    refine WExec.cast cap (WExec.whrF hK0) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | n + 1, σ, hK0, hS, hC, hn => by
    have e1 := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := wrBit_spec cap D S σ1
    have hb : wbit σ1 D = readTapeBit (σ.st D) (σ.sh D) := rfl
    set σ2 := σ1.sets S (writeTapeBit (σ1.st S) (σ1.sh S) (wbit σ1 D)) with hσ2
    have hw : writeTapeBit (σ1.st S) (σ1.sh S) (wbit σ1 D) = σ.st S ++ [readTapeBit (σ.st D) (σ.sh D)] := by
      simp only [σ1, WState.setv_st, WState.setv_sh, hS]; rw [writeTapeBit_end]; rfl
    have e3 := WExec.fwd (cap := cap) D σ2
    set σ3 := σ2.seth D (σ2.sh D + 1) with hσ3
    have e4 := wfwdC_spec cap S CS σ3 (by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hK]; omega)
    set σ4 := (σ3.seth S (σ3.sh S + 1)).setv CS (σ3.val CS + 1) with hσ4
    have h4st : σ4.st S = σ.st S ++ [readTapeBit (σ.st D) (σ.sh D)] := by simp [σ4, σ3, σ2, hw]
    have h4D : σ4.st D = σ.st D := by simp [σ4, σ3, σ2, σ1, Function.update_apply, hDS]
    have h4hD : σ4.sh D = σ.sh D + 1 := by simp [σ4, σ3, σ2, σ1, Function.update_apply, hDS]
    have ih := cpyC_spec D S K CS hDS hK n σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hK, hK0])
      (by rw [h4st]; simp [σ4, σ3, σ2, σ1, Function.update_apply, hDS, Ne.symm hDS, hS])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hK]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih) ?_ (by omega)
    have hl : σ4.st S ++ (List.ofFn fun i : Fin n => readTapeBit (σ4.st D) (σ4.sh D + i.val)) =
        σ.st S ++ List.ofFn fun i : Fin (n + 1) => readTapeBit (σ.st D) (σ.sh D + i.val) := by
      rw [h4st, h4D, h4hD, List.append_assoc, List.singleton_append, ofFn_succ_read]
    rw [hl]
    have hlen : (σ4.st S).length = (σ.st S).length + 1 := by rw [h4st]; simp
    rw [hlen, h4hD]
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; simp only [σ4, σ3, σ2, σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
    · funext x; simp only [σ4, σ3, σ2, σ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega

/-- `2n` cells `true` appended to `O` (the marked cells of `frame 1^n`); `K := 0`. -/
def emitP2 (O : Fin (ns + 1)) (K OP : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (emitC O OP true) (emitC O OP true)))

theorem emitP2_spec (O : Fin (ns + 1)) (K OP : Fin nr) (hK : K ≠ OP) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val K = n → σ.sh O = (σ.st O).length → σ.val OP + 2 * n ≤ cap → n ≤ cap →
      WExec cap (emitP2 O K OP) σ ((((σ.sets O (σ.st O ++ List.replicate (2 * n) true)).seth O
        ((σ.st O).length + 2 * n)).setv OP (σ.val OP + 2 * n)).setv K 0) (19 * n + 1)
  | 0, σ, hK0, hS, _, _ => by
    refine WExec.cast cap (WExec.whrF hK0) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | n + 1, σ, hK0, hS, hC, hn => by
    have e1 := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := emitC_spec cap O OP true σ1 (by simp [σ1, hS]) (by simp [σ1, Function.update_apply, Ne.symm hK]; omega)
    set σ2 := ((σ1.sets O (σ1.st O ++ [true])).seth O (σ1.sh O + 1)).setv OP (σ1.val OP + 1) with hσ2
    have e3 := emitC_spec cap O OP true σ2 (by simp [σ2, σ1, hS]) (by simp [σ2, σ1, Function.update_apply, Ne.symm hK]; omega)
    set σ3 := ((σ2.sets O (σ2.st O ++ [true])).seth O (σ2.sh O + 1)).setv OP (σ2.val OP + 1) with hσ3
    have h3st : σ3.st O = σ.st O ++ [true, true] := by simp [σ3, σ2, σ1]
    have ih := emitP2_spec O K OP hK n σ3 (by simp [σ3, σ2, σ1, Function.update_apply, hK, hK0])
      (by rw [h3st]; simp [σ3, σ2, σ1, hS]) (by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hK]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by omega)
    have hl : σ3.st O ++ List.replicate (2 * n) true = σ.st O ++ List.replicate (2 * (n + 1)) true := by
      simp [h3st, show 2 * (n + 1) = 2 + 2 * n by ring, List.replicate_add]
    have hlen : (σ3.st O).length = (σ.st O).length + 2 := by rw [h3st]; simp
    rw [hl, hlen]
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; simp only [σ3, σ2, σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
    · funext x; simp only [σ3, σ2, σ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega

/-- Each cell `b` as the four cells `true true true b` (the cells of `frame (frame w ++ …)` for the bits of `w`). -/
def quad (w : List Bool) : List Bool := w.flatMap fun b => [true, true, true, b]

/-- Append the scanned bit of `SRC` to `O`. -/
theorem emitBit_spec (SRC O : Fin (ns + 1)) (OP : Fin nr) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val OP < cap) :
    WExec cap (.ifs SRC (emitC O OP true) (emitC O OP false)) σ
      (((σ.sets O ((σ.st O) ++ [wbit σ SRC])).seth O (σ.sh O + 1)).setv OP (σ.val OP + 1)) 8 := by
  cases h : wbit σ SRC
  · exact WExec.ifsF h (emitC_spec cap O OP false σ hO hc)
  · exact WExec.ifsT h (emitC_spec cap O OP true σ hO hc)

/-- `quad` of `n` cells of `SRC` (from its head) appended to `O`; `K := 0`. -/
def emitFF (SRC O : Fin (ns + 1)) (K OP : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (emitC O OP true) (.seq (emitC O OP true) (.seq (emitC O OP true)
    (.seq (.ifs SRC (emitC O OP true) (emitC O OP false)) (.fwd SRC))))))

theorem emitFF_spec (SRC O : Fin (ns + 1)) (K OP : Fin nr) (hSO : SRC ≠ O) (hK : K ≠ OP) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val K = n → σ.sh O = (σ.st O).length → σ.val OP + 4 * n ≤ cap → n ≤ cap →
      WExec cap (emitFF SRC O K OP) σ
        (((((σ.sets O (σ.st O ++ quad (List.ofFn fun i : Fin n => readTapeBit (σ.st SRC) (σ.sh SRC + i.val)))).seth O
          ((σ.st O).length + 4 * n)).seth SRC (σ.sh SRC + n)).setv OP (σ.val OP + 4 * n)).setv K 0) (40 * n + 1)
  | 0, σ, hK0, hS, _, _ => by
    refine WExec.cast cap (WExec.whrF hK0) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [quad]
    · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | n + 1, σ, hK0, hS, hC, hn => by
    have e1 := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := emitC_spec cap O OP true σ1 (by simp [σ1, hS]) (by simp [σ1, Function.update_apply, Ne.symm hK]; omega)
    set σ2 := ((σ1.sets O (σ1.st O ++ [true])).seth O (σ1.sh O + 1)).setv OP (σ1.val OP + 1) with hσ2
    have e3 := emitC_spec cap O OP true σ2 (by simp [σ2, σ1, hS]) (by simp [σ2, σ1, Function.update_apply, Ne.symm hK]; omega)
    set σ3 := ((σ2.sets O (σ2.st O ++ [true])).seth O (σ2.sh O + 1)).setv OP (σ2.val OP + 1) with hσ3
    have e4 := emitC_spec cap O OP true σ3 (by simp [σ3, σ2, σ1, hS]) (by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hK]; omega)
    set σ4 := ((σ3.sets O (σ3.st O ++ [true])).seth O (σ3.sh O + 1)).setv OP (σ3.val OP + 1) with hσ4
    have e5 := emitBit_spec cap SRC O OP σ4 (by simp [σ4, σ3, σ2, σ1, hS]) (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hK]; omega)
    have hb : wbit σ4 SRC = readTapeBit (σ.st SRC) (σ.sh SRC) := by
      rw [wbit]; simp [σ4, σ3, σ2, σ1, Function.update_apply, hSO]
    set σ5 := ((σ4.sets O ((σ4.st O) ++ [wbit σ4 SRC])).seth O (σ4.sh O + 1)).setv OP (σ4.val OP + 1) with hσ5
    have e6 := WExec.fwd (cap := cap) SRC σ5
    set σ6 := σ5.seth SRC (σ5.sh SRC + 1) with hσ6
    have h6st : σ6.st O = σ.st O ++ [true, true, true, readTapeBit (σ.st SRC) (σ.sh SRC)] := by
      have : σ6.st O = σ4.st O ++ [wbit σ4 SRC] := by simp [σ6, σ5]
      rw [this, hb]; simp [σ4, σ3, σ2, σ1]
    have h6S : σ6.st SRC = σ.st SRC := by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hSO]
    have h6hS : σ6.sh SRC = σ.sh SRC + 1 := by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hSO]
    have ih := emitFF_spec SRC O K OP hSO hK n σ6 (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hK, hK0])
      (by rw [h6st]; simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hSO, hS])
      (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hK]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4
      (WExec.seq e5 e6))))) ih) ?_ (by omega)
    have hl : σ6.st O ++ quad (List.ofFn fun i : Fin n => readTapeBit (σ6.st SRC) (σ6.sh SRC + i.val)) =
        σ.st O ++ quad (List.ofFn fun i : Fin (n + 1) => readTapeBit (σ.st SRC) (σ.sh SRC + i.val)) := by
      rw [h6st, h6S, h6hS, ← ofFn_succ_read]
      simp [quad]
    have hlen : (σ6.st O).length = (σ.st O).length + 4 := by rw [h6st]; simp
    rw [hl, hlen, h6hS]
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh,
        Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
    · funext x; simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_st, WState.seth_st, WState.sets_st,
        Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val,
        Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega

/-- Write the flag `[F ≠ 0]` on the empty stream `FO`. -/
def flagW (F : Fin nr) (FO : Fin (ns + 1)) : WM ns nr := .ifr F (.wr FO true) (.wr FO false)

theorem flagW_spec (F : Fin nr) (FO : Fin (ns + 1)) (σ : WState ns nr) (hst : σ.st FO = []) (hsh : σ.sh FO = 0) :
    WExec cap (flagW F FO) σ (σ.sets FO [decide (σ.val F ≠ 0)]) 2 := by
  show WExec cap (.ifr F (.wr FO true) (.wr FO false)) σ _ 2
  by_cases h : σ.val F = 0
  · have e := WExec.ifrF (P := .wr FO true) h (WExec.wr (cap := cap) FO false σ)
    rw [hst, hsh] at e
    have hw : writeTapeBit [] 0 false = [decide (σ.val F ≠ 0)] := by simp [h, writeTapeBit]
    rw [hw] at e
    exact e
  · have e := WExec.ifrT (Q := .wr FO false) h (WExec.wr (cap := cap) FO true σ)
    rw [hst, hsh] at e
    have hw : writeTapeBit [] 0 true = [decide (σ.val F ≠ 0)] := by simp [h, writeTapeBit]
    rw [hw] at e
    exact e

end NearCubicGates.Close.OuterM
