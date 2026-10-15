import Proof.Wire_3_5.FinalPassListEvalCyc

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Close a (in)equality about one register value of an updated state. -/
macro "gen_eq_val" : tactic =>
  `(tactic| (simp only [RState.setv_val, RState.seth_val, Function.update_apply]
             split_ifs <;> subst_vars <;> (try simp_all) <;> omega))

/-- Close an equality of abstract states whose registers are variables, by cases on the updated registers. -/
syntax "gen_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| gen_eq) => `(tactic| gen_eq [])
  | `(tactic| gen_eq [$ts,*]) => `(tactic| (refine RState.eq ?_ ?_ ?_ <;>
      first
        | (funext x
           simp only [RState.setv_val, RState.seth_val, RState.setv_sh, RState.seth_sh, Function.update_apply]
           split_ifs <;> subst_vars <;> (try simp_all [$ts,*]) <;> omega)
        | rfl
        | simp))

section Generic
variable {ns nr : ℕ} (inp : Fin (ns + 1) → List Bool) (cap : ℕ)

/-- `b += a; t += a; a := 0`. -/
def RM.dup (a b t : Fin nr) : RM ns nr := .whr a (.seq (.dec a) (.seq (.inc b) (.inc t)))

theorem dup_spec (a b t : Fin nr) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    ∀ (n : ℕ) (σ : RState ns nr), σ.val a = n → n ≤ cap → σ.val b + n ≤ cap → σ.val t + n ≤ cap →
      RExec inp cap (RM.dup a b t) σ (((σ.setv a 0).setv b (σ.val b + n)).setv t (σ.val t + n)) (11 * n + 1)
  | 0, σ, h0, _, _, _ => by
    have e : ((σ.setv a 0).setv b (σ.val b + 0)).setv t (σ.val t + 0) = σ := by
      gen_eq
    rw [e]
    exact RExec.whrF h0
  | n + 1, σ, hn, hc, hb, ht => by
    have h1 := RExec.dec (inp := inp) (cap := cap) a σ (by omega)
    have hb1 : (σ.setv a (σ.val a - 1)).val b = σ.val b := setv_val_ne _ _ (Ne.symm hab)
    have h2 := RExec.inc (inp := inp) (cap := cap) b (σ.setv a (σ.val a - 1)) (by rw [hb1]; omega)
    have ht2 : ((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b + 1)).val t = σ.val t := by
      rw [setv_val_ne _ _ (Ne.symm hbt), setv_val_ne _ _ (Ne.symm hat)]
    have h3 := RExec.inc (inp := inp) (cap := cap) t _ (by rw [ht2]; omega)
    have ih := dup_spec a b t hab hat hbt n
      (((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b + 1)).setv t
        (((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b + 1)).val t + 1))
      (by gen_eq_val) (by omega) (by gen_eq_val) (by gen_eq_val)
    refine RExec.cast inp cap (RExec.whrT (by omega) (RExec.seq h1 (RExec.seq h2 h3)) ih) ?_ (by omega)
    gen_eq

/-- `a` times: decrement `b`, or set the flag `f` if `b` is already `0`. -/
def RM.decAgainst (a b f : Fin nr) : RM ns nr := .whr a (.seq (.dec a) (.ifr b (.dec b) (RM.setF f)))

theorem decAgainst_spec (a b f : Fin nr) (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f) (hcap : 1 ≤ cap) :
    ∀ (n : ℕ) (σ : RState ns nr), σ.val a = n → n ≤ cap → σ.val b ≤ cap → σ.val f ≤ 1 →
      RExec inp cap (RM.decAgainst a b f) σ
        (((σ.setv a 0).setv b (σ.val b - n)).setv f (if σ.val b < n then 1 else σ.val f)) (9 * n + 1)
  | 0, σ, h0, _, _, _ => by
    have e : ((σ.setv a 0).setv b (σ.val b - 0)).setv f (if σ.val b < 0 then 1 else σ.val f) = σ := by
      simp only [Nat.sub_zero, Nat.not_lt_zero, if_false]
      gen_eq
    rw [e]
    exact RExec.whrF h0
  | n + 1, σ, hn, hc, hb, hf => by
    have h1 := RExec.dec (inp := inp) (cap := cap) a σ (by omega)
    have hb1 : (σ.setv a (σ.val a - 1)).val b = σ.val b := setv_val_ne _ _ (Ne.symm hab)
    have hf1 : (σ.setv a (σ.val a - 1)).val f = σ.val f := setv_val_ne _ _ (Ne.symm haf)
    by_cases hb0 : σ.val b = 0
    · have h2 := setF_spec inp cap f (σ.setv a (σ.val a - 1)) (by rw [hf1]; exact hf) hcap
      have h2' := RExec.ifrF (P := .dec b) (by rw [hb1]; exact hb0) h2
      have ih := decAgainst_spec a b f hab haf hbf hcap n ((σ.setv a (σ.val a - 1)).setv f 1)
        (by gen_eq_val) (by omega) (by gen_eq_val) (by gen_eq_val)
      refine RExec.cast inp cap (RExec.whrT (by omega) (RExec.seq h1 h2') ih) ?_ (by omega)
      gen_eq [hb0]
    · have h2 := RExec.dec (inp := inp) (cap := cap) b (σ.setv a (σ.val a - 1)) (by rw [hb1]; exact hb)
      have h2' := RExec.ifrT (Q := RM.setF f) (by rw [hb1]; exact hb0) h2
      have ih := decAgainst_spec a b f hab haf hbf hcap n
        ((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b - 1))
        (by gen_eq_val) (by omega) (by gen_eq_val) (by gen_eq_val)
      refine RExec.cast inp cap (RExec.whrT (by omega) (RExec.seq h1 h2') ih) ?_ (by omega)
      gen_eq [hb0]

end Generic

/-! ## One level of arithmetic -/

variable (inp : Fin 3 → List Bool) (cap : ℕ)

/-- `b := a` (from `b = 0`), keeping `a`, through `T2`. -/
def copyTo (a b : Fin 15) : LProg := .seq (RM.dup a b rT2) (RM.move rT2 a)

/-- The empty-state flag if `s_{j+1} > M`: `F := 1` when `MR < S`. -/
def leqFlag : LProg := .seq (copyTo rS rT1) (.seq (copyTo rMR rT) (.seq (RM.decAgainst rT1 rT rF) (RM.clear rT)))

/-- `S := 2S`. -/
def double : LProg := .seq (RM.dup rS rT rT2) (.seq (RM.move rT2 rT) (RM.move rT rS))

/-- `S := 2S + V − W`, with the flag when negative. -/
def arith : LProg := .seq double (.seq (RM.move rV rS) (RM.decAgainst rW rS rF))

/-- Forget the residue and the window. -/
def discard : LProg := .seq (RM.clear rV) (RM.clear rW)

def decidePart : LProg := .ifr rF discard (.seq leqFlag (.ifr rF discard arith))

/-- The scratch registers of the arithmetic are clear. -/
def Clean (σ : LState) : Prop := σ.val rT = 0 ∧ σ.val rT1 = 0 ∧ σ.val rT2 = 0

theorem copyTo_S_spec (σ : LState) (hT1 : σ.val rT1 = 0) (hT2 : σ.val rT2 = 0) (h1 : σ.val rS ≤ cap) :
    RExec inp cap (copyTo rS rT1) σ (σ.setv rT1 (σ.val rS)) (18 * cap + 3) := by
  have s1 := dup_spec inp cap rS rT1 rT2 (by decide) (by decide) (by decide) (σ.val rS) σ rfl h1 (by omega) (by omega)
  have s2 := move_spec inp cap rT2 rS (by decide) (σ.val rS)
    (((σ.setv rS 0).setv rT1 (σ.val rT1 + σ.val rS)).setv rT2 (σ.val rT2 + σ.val rS)) (by simp [hT2])
    (by simp [hT2]; omega) (by simp [hT2]; omega)
  refine RExec.cast inp cap (RExec.seq s1 s2) ?_ (by omega)
  rs_eq [hT1, hT2]

theorem copyTo_M_spec (σ : LState) (hT : σ.val rT = 0) (hT2 : σ.val rT2 = 0) (h1 : σ.val rMR ≤ cap) :
    RExec inp cap (copyTo rMR rT) σ (σ.setv rT (σ.val rMR)) (18 * cap + 3) := by
  have s1 := dup_spec inp cap rMR rT rT2 (by decide) (by decide) (by decide) (σ.val rMR) σ rfl h1 (by omega)
    (by omega)
  have s2 := move_spec inp cap rT2 rMR (by decide) (σ.val rMR)
    (((σ.setv rMR 0).setv rT (σ.val rT + σ.val rMR)).setv rT2 (σ.val rT2 + σ.val rMR)) (by simp [hT2])
    (by simp [hT2]; omega) (by simp [hT2]; omega)
  refine RExec.cast inp cap (RExec.seq s1 s2) ?_ (by omega)
  rs_eq [hT, hT2]

theorem leqFlag_spec (σ : LState) (hc : Clean σ) (hS : σ.val rS ≤ cap) (hM : σ.val rMR ≤ cap) (hF : σ.val rF ≤ 1)
    (hcap : 1 ≤ cap) :
    RExec inp cap leqFlag σ (σ.setv rF (if σ.val rMR < σ.val rS then 1 else σ.val rF)) (60 * cap + 20) := by
  obtain ⟨hT, hT1, hT2⟩ := hc
  have s1 := copyTo_S_spec inp cap σ hT1 hT2 hS
  have s2 := copyTo_M_spec inp cap (σ.setv rT1 (σ.val rS)) (by simp [hT]) (by simp [hT2]) (by simp; omega)
  have s3 := decAgainst_spec inp cap rT1 rT rF (by decide) (by decide) (by decide) hcap (σ.val rS)
    ((σ.setv rT1 (σ.val rS)).setv rT (σ.val rMR)) (by simp) hS (by simp; omega) (by simp; omega)
  have s4 := clear_spec inp cap rT (σ.val rMR - σ.val rS)
    ((((σ.setv rT1 (σ.val rS)).setv rT (σ.val rMR)).setv rT1 0).setv rT (σ.val rMR - σ.val rS) |>.setv rF
      (if σ.val rMR < σ.val rS then 1 else σ.val rF)) (by simp) (by simp; omega)
  have s3' : RExec inp cap (RM.decAgainst rT1 rT rF) ((σ.setv rT1 (σ.val rS)).setv rT (σ.val rMR))
      ((((σ.setv rT1 (σ.val rS)).setv rT (σ.val rMR)).setv rT1 0).setv rT (σ.val rMR - σ.val rS) |>.setv rF
        (if σ.val rMR < σ.val rS then 1 else σ.val rF)) (9 * σ.val rS + 1) := by
    refine RExec.cast inp cap s3 ?_ le_rfl
    rs_eq
  refine RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3' s4))) ?_ (by omega)
  rs_eq [hT, hT1]

theorem double_spec (σ : LState) (hT : σ.val rT = 0) (hT2 : σ.val rT2 = 0) (hS : 2 * σ.val rS ≤ cap) :
    RExec inp cap double σ (σ.setv rS (2 * σ.val rS)) (40 * cap + 5) := by
  have s1 := dup_spec inp cap rS rT rT2 (by decide) (by decide) (by decide) (σ.val rS) σ rfl (by omega) (by omega)
    (by omega)
  have s2 := move_spec inp cap rT2 rT (by decide) (σ.val rS)
    (((σ.setv rS 0).setv rT (σ.val rT + σ.val rS)).setv rT2 (σ.val rT2 + σ.val rS)) (by simp [hT2])
    (by simp [hT2]; omega) (by simp [hT, hT2]; omega)
  have s3 := move_spec inp cap rT rS (by decide) (2 * σ.val rS)
    ((((σ.setv rS 0).setv rT (σ.val rT + σ.val rS)).setv rT2 (σ.val rT2 + σ.val rS)).setv rT2 0 |>.setv rT
      ((σ.val rT + σ.val rS) + (σ.val rT2 + σ.val rS))) (by simp [hT, hT2]; omega) (by simp [hT, hT2]; omega)
    (by simp [hT, hT2]; omega)
  have s2' : RExec inp cap (RM.move rT2 rT) (((σ.setv rS 0).setv rT (σ.val rT + σ.val rS)).setv rT2
      (σ.val rT2 + σ.val rS)) ((((σ.setv rS 0).setv rT (σ.val rT + σ.val rS)).setv rT2 (σ.val rT2 + σ.val rS)).setv
        rT2 0 |>.setv rT ((σ.val rT + σ.val rS) + (σ.val rT2 + σ.val rS))) (7 * σ.val rS + 1) := by
    refine RExec.cast inp cap s2 ?_ le_rfl
    rs_eq
  refine RExec.cast inp cap (RExec.seq s1 (RExec.seq s2' s3)) ?_ (by nlinarith)
  rs_eq [hT, hT2]

theorem arith_spec (σ : LState) (hT : σ.val rT = 0) (hT2 : σ.val rT2 = 0) (hF : σ.val rF = 0)
    (hS : 2 * σ.val rS + σ.val rV ≤ cap) (hW : σ.val rW ≤ cap) (hcap : 1 ≤ cap) :
    RExec inp cap arith σ ((((σ.setv rS (2 * σ.val rS + σ.val rV - σ.val rW)).setv rV 0).setv rW 0).setv rF
      (if 2 * σ.val rS + σ.val rV < σ.val rW then 1 else 0)) (60 * cap + 10) := by
  have s1 := double_spec inp cap σ hT hT2 (by omega)
  have s2 := move_spec inp cap rV rS (by decide) (σ.val rV) (σ.setv rS (2 * σ.val rS)) (by simp) (by simp; omega)
    (by simp; omega)
  have s3 := decAgainst_spec inp cap rW rS rF (by decide) (by decide) (by decide) hcap (σ.val rW)
    (((σ.setv rS (2 * σ.val rS)).setv rV 0).setv rS (2 * σ.val rS + σ.val rV)) (by simp) hW (by simp; omega)
    (by simp [hF])
  have s2' : RExec inp cap (RM.move rV rS) (σ.setv rS (2 * σ.val rS))
      (((σ.setv rS (2 * σ.val rS)).setv rV 0).setv rS (2 * σ.val rS + σ.val rV)) (7 * σ.val rV + 1) := by
    refine RExec.cast inp cap s2 ?_ le_rfl
    rs_eq
  refine RExec.cast inp cap (RExec.seq s1 (RExec.seq s2' s3)) ?_ (by omega)
  rs_eq [hF]

theorem discard_spec (σ : LState) (hV : σ.val rV ≤ cap) (hW : σ.val rW ≤ cap) :
    RExec inp cap discard σ ((σ.setv rV 0).setv rW 0) (6 * cap + 3) := by
  have s1 := clear_spec inp cap rV (σ.val rV) σ rfl hV
  have s2 := clear_spec inp cap rW (σ.val rW) (σ.setv rV 0) (by simp) (by simp; omega)
  have s2' : RExec inp cap (RM.clear rW) (σ.setv rV 0) ((σ.setv rV 0).setv rW 0) (3 * σ.val rW + 1) := by
    refine RExec.cast inp cap s2 ?_ le_rfl
    rs_eq
  exact RExec.mono (RExec.seq s1 s2') (by omega)

/-- The state after a level's decision. -/
def decState (σ : LState) : LState :=
  if σ.val rF ≠ 0 then (σ.setv rV 0).setv rW 0
  else if σ.val rMR < σ.val rS then ((σ.setv rF 1).setv rV 0).setv rW 0
  else ((((σ.setv rS (2 * σ.val rS + σ.val rV - σ.val rW)).setv rV 0).setv rW 0).setv rF
    (if 2 * σ.val rS + σ.val rV < σ.val rW then 1 else 0))

theorem decidePart_spec (σ : LState) (hc : Clean σ) (hF : σ.val rF ≤ 1) (hM : σ.val rMR ≤ cap)
    (hS : σ.val rS ≤ cap) (hMV : 2 * σ.val rMR + σ.val rV ≤ cap) (hW : σ.val rW ≤ cap) (hcap : 1 ≤ cap) :
    RExec inp cap decidePart σ (decState σ) (130 * cap + 40) := by
  have hc0 := hc
  obtain ⟨hT, hT1, hT2⟩ := hc
  by_cases hf : σ.val rF ≠ 0
  · have s := discard_spec inp cap σ (by omega) hW
    have e : decState σ = (σ.setv rV 0).setv rW 0 := by simp [decState, hf]
    rw [e]
    exact RExec.mono (RExec.ifrT hf s) (by omega)
  · have hf0 : σ.val rF = 0 := by omega
    have s1 := leqFlag_spec inp cap σ hc0 hS hM hF hcap
    by_cases hlt : σ.val rMR < σ.val rS
    · have e1 : σ.setv rF (if σ.val rMR < σ.val rS then 1 else σ.val rF) = σ.setv rF 1 := by simp [hlt]
      rw [e1] at s1
      have s2 := discard_spec inp cap (σ.setv rF 1) (by simp; omega) (by simp; omega)
      have s2' := RExec.ifrT (r := rF) (P := discard) (Q := arith) (by simp) s2
      have e : decState σ = ((σ.setv rF 1).setv rV 0).setv rW 0 := by simp [decState, hf0, hlt]
      rw [e]
      exact RExec.mono (RExec.ifrF hf0 (RExec.seq s1 s2')) (by omega)
    · have e1 : σ.setv rF (if σ.val rMR < σ.val rS then 1 else σ.val rF) = σ := by
        simp only [hlt, if_false]; exact setv_same σ rF
      rw [e1] at s1
      have s2 := arith_spec inp cap σ hT hT2 hf0 (by omega) hW hcap
      have s2' := RExec.ifrF (P := discard) (Q := arith) hf0 s2
      have e : decState σ = ((((σ.setv rS (2 * σ.val rS + σ.val rV - σ.val rW)).setv rV 0).setv rW 0).setv rF
          (if 2 * σ.val rS + σ.val rV < σ.val rW then 1 else 0)) := by simp [decState, hf0, hlt]
      rw [e]
      exact RExec.mono (RExec.ifrF hf0 (RExec.seq s1 s2')) (by omega)

end NearCubicWires.WireExponent3_5.FinalPass.ListEval
