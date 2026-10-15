import Proof.Gates.Succinct.Arith
import Proof.Gates.Succinct.Count
import Proof.Gates.OuterM.Spec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct NearCubicGates.Close.WordPrograms

/-! ## Arithmetic -/

theorem log_eq_hc (x : ℕ) : Nat.log 2 x = hc x - 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [hc]
  · have h1 := lt_two_pow_hc x
    have h2 := two_pow_hc_le_two_mul x hx
    generalize hs : hc x = s at h1 h2
    rcases s with _ | s
    · simp at h1; omega
    · rw [Nat.add_sub_cancel, Nat.log_eq_iff (by right; omega)]
      rw [pow_succ] at h1 h2
      exact ⟨by omega, by rw [pow_succ]; exact h1⟩

theorem clog_eq_hc (c : ℕ) : Nat.clog 2 (c + 2) = hc (c + 1) := by
  have h1 := lt_two_pow_hc (c + 1)
  have h2 := two_pow_hc_le_two_mul (c + 1) (by omega)
  generalize hs : hc (c + 1) = s at h1 h2
  apply le_antisymm
  · exact Nat.clog_le_of_le_pow (by omega)
  · by_contra hlt
    push Not at hlt
    have h3 := Nat.le_pow_clog (b := 2) (by norm_num) (c + 2)
    have h4 : 2 ^ Nat.clog 2 (c + 2) ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases s with _ | s
    · omega
    · rw [pow_succ] at h2; simp at h4; omega

/-- `q(2^ν) = c + A·hc(c+1) + A` with `c = ν(k+2)`. -/
theorem widthOf_two_pow (k A ν : ℕ) :
    Outer.widthOf k A (2 ^ ν) = ν * (k + 2) + A * hc (ν * (k + 2) + 1) + A := by
  unfold Outer.widthOf
  rw [Outer.clkLog_two_pow, clog_eq_hc]

theorem bits_cons (v : ℕ) (h : v ≠ 0) : v.bits = decide (v % 2 = 1) :: (v / 2).bits := by
  have := Nat.bit_decide_mod_two_eq_one_shiftRight_one v
  conv_lhs => rw [← this]
  rw [Nat.bits_append_bit, Nat.shiftRight_one]
  intro h0
  have : v = 1 := by omega
  subst this; rfl

theorem bits_length_le (v : ℕ) : v.bits.length ≤ v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp
    · rw [bits_cons v (by omega), List.length_cons]
      have := ih (v / 2) (by omega)
      omega

/-! ## Registers and streams -/

local notation "rX" => (0 : Fin 9)
local notation "rR" => (1 : Fin 9)
local notation "rH" => (2 : Fin 9)
local notation "rC" => (3 : Fin 9)
local notation "rU" => (4 : Fin 9)
local notation "rM" => (5 : Fin 9)
local notation "rP" => (6 : Fin 9)
local notation "rO" => (7 : Fin 9)
local notation "sOut" => (1 : Fin 2)

/-- Close an equality of two states of this program: every head, stream and register by cases. -/
syntax "weq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| weq) => `(tactic| weq [])
  | `(tactic| weq [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | rfl
        | (funext x; fin_cases x <;> simp [Function.update_apply, $ts,*] <;> omega)
        | simp [$ts,*]))

variable (cap : ℕ)

/-! ## `j` increments -/

/-- `r := r + j`. -/
def incN (r : Fin 9) : ℕ → WM 1 9
  | 0 => .skip
  | j + 1 => .seq (.inc r) (incN r j)

theorem incN_spec (r : Fin 9) : ∀ (j : ℕ) (σ : WState 1 9), σ.val r + j ≤ cap →
    WExec cap (incN r j) σ (σ.setv r (σ.val r + j)) (4 * j)
  | 0, σ, _ => by
    rw [Nat.add_zero, wsetv_same]
    exact WExec.skip σ
  | j + 1, σ, h => by
    have e1 := WExec.inc (cap := cap) r σ (by omega)
    have e2 := incN_spec r j (σ.setv r (σ.val r + 1)) (by simp; omega)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
    rw [wsetv_setv]; simp; ring_nf

/-! ## Phase 1: the input length -/

/-- `X := |x|` from `frame x` on stream `0` (the head stays at the end). -/
def cntL : WM 1 9 := .whs 0 (.seq (.fwd 0) (.seq (.fwd 0) (.inc rX)))

theorem cntL_spec (u : List Bool) : ∀ (m j : ℕ) (σ : WState 1 9), j + m = u.length →
    σ.st 0 = RepairOrdinary.frame u → σ.sh 0 = 2 * j → σ.val rX = j → u.length < cap →
    WExec cap cntL σ ((σ.seth 0 (2 * u.length)).setv rX u.length) (9 * m + 1)
  | 0, j, σ, hj, hst, hsh, hX, _ => by
    have hb : wbit σ 0 = false := by
      unfold wbit; rw [hst, hsh, frame_even]; simp; omega
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    rw [show u.length = j by omega, ← hsh, ← hX, wseth_same, wsetv_same]
  | m + 1, j, σ, hj, hst, hsh, hX, hcap => by
    have hb : wbit σ 0 = true := by
      unfold wbit; rw [hst, hsh, frame_even]; simp; omega
    have e1 := WExec.fwd (cap := cap) 0 σ
    have e2 := WExec.fwd (cap := cap) 0 (σ.seth 0 (σ.sh 0 + 1))
    have e3 := WExec.inc (cap := cap) rX ((σ.seth 0 (σ.sh 0 + 1)).seth 0 ((σ.seth 0 (σ.sh 0 + 1)).sh 0 + 1))
      (by simp; omega)
    set τ := ((σ.seth 0 (σ.sh 0 + 1)).seth 0 ((σ.seth 0 (σ.sh 0 + 1)).sh 0 + 1)).setv rX
      (((σ.seth 0 (σ.sh 0 + 1)).seth 0 ((σ.seth 0 (σ.sh 0 + 1)).sh 0 + 1)).val rX + 1) with hτ
    have ih := cntL_spec u m (j + 1) τ (by omega) (by simp [τ, hst]) (by simp [τ, hsh]; omega)
      (by simp [τ, hX]) hcap
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by omega)
    simp only [τ]
    weq [hsh, hX]

/-! ## Phases 3 and 5: multiplication by a constant -/

/-- `C += R·a`, `U += R·a`, `R := 0`. -/
def mulL (a : ℕ) : WM 1 9 := .whr rR (.seq (.dec rR) (.seq (incN rC a) (incN rU a)))

theorem mulL_spec (a : ℕ) : ∀ (n : ℕ) (σ : WState 1 9), σ.val rR = n → σ.val rC + n * a ≤ cap →
    σ.val rU + n * a ≤ cap → n ≤ cap →
    WExec cap (mulL a) σ (((σ.setv rR 0).setv rC (σ.val rC + n * a)).setv rU (σ.val rU + n * a)) (n * (8 * a + 5) + 1)
  | 0, σ, hR, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hR) ?_ (by omega)
    simp only [Nat.zero_mul, Nat.add_zero]
    rw [← hR, wsetv_same, wsetv_same, wsetv_same]
  | n + 1, σ, hR, hC, hU, hn => by
    have e1 := WExec.dec (cap := cap) rR σ (by omega)
    set σ1 := σ.setv rR (σ.val rR - 1) with hσ1
    have e2 := incN_spec cap rC a σ1 (by simp [Function.update_apply, σ1]; nlinarith)
    set σ2 := σ1.setv rC (σ1.val rC + a) with hσ2
    have e3 := incN_spec cap rU a σ2 (by simp [Function.update_apply, σ2, σ1]; nlinarith)
    set σ3 := σ2.setv rU (σ2.val rU + a) with hσ3
    have ih := mulL_spec a n σ3 (by simp [Function.update_apply, σ3, σ2, σ1, hR]) (by simp [Function.update_apply, σ3, σ2, σ1]; nlinarith)
      (by simp [Function.update_apply, σ3, σ2, σ1]; nlinarith) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by nlinarith)
    simp only [σ3, σ2, σ1]
    have hm : (n + 1) * a = n * a + a := by ring
    weq [hm, hR]

/-- `C += M·A`, `M := 0`. -/
def addL (A : ℕ) : WM 1 9 := .whr rM (.seq (.dec rM) (incN rC A))

theorem addL_spec (A : ℕ) : ∀ (n : ℕ) (σ : WState 1 9), σ.val rM = n → σ.val rC + n * A ≤ cap → n ≤ cap →
    WExec cap (addL A) σ ((σ.setv rM 0).setv rC (σ.val rC + n * A)) (n * (4 * A + 4) + 1)
  | 0, σ, hM, _, _ => by
    refine WExec.cast cap (WExec.whrF hM) ?_ (by omega)
    simp only [Nat.zero_mul, Nat.add_zero]
    rw [← hM, wsetv_same, wsetv_same]
  | n + 1, σ, hM, hC, hn => by
    have e1 := WExec.dec (cap := cap) rM σ (by omega)
    set σ1 := σ.setv rM (σ.val rM - 1) with hσ1
    have e2 := incN_spec cap rC A σ1 (by simp [Function.update_apply, σ1]; nlinarith)
    set σ2 := σ1.setv rC (σ1.val rC + A) with hσ2
    have ih := addL_spec A n σ2 (by simp [Function.update_apply, σ2, σ1, hM]) (by simp [Function.update_apply, σ2, σ1]; nlinarith) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih) ?_ (by nlinarith)
    simp only [σ2, σ1]
    have hm : (n + 1) * A = n * A + A := by ring
    weq [hm, hM]

/-! ## Phase 6: the output -/

/-- `H += C/2`, `P += C mod 2`, `C := 0`. -/
def halvP : WM 1 9 := .whr rC (.seq (.dec rC) (.ifr rC (.seq (.dec rC) (.inc rH)) (.inc rP)))

theorem halvP_spec : ∀ (v : ℕ) (σ : WState 1 9), σ.val rC = v → σ.val rH + v / 2 ≤ cap →
    σ.val rP + v % 2 ≤ cap → v ≤ cap →
    WExec cap halvP σ (((σ.setv rC 0).setv rH (σ.val rH + v / 2)).setv rP (σ.val rP + v % 2)) (5 * v + 4)
  | 0, σ, hC, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hC) ?_ (by omega)
    simp only [Nat.zero_div, Nat.zero_mod, Nat.add_zero]
    rw [← hC, wsetv_same, wsetv_same, wsetv_same]
  | 1, σ, hC, hH, hP, _ => by
    have e1 := WExec.dec (cap := cap) rC σ (by omega)
    set σ1 := σ.setv rC (σ.val rC - 1) with hσ1
    have h0 : σ1.val rC = 0 := by simp [Function.update_apply, σ1, hC]
    have e2 := WExec.inc (cap := cap) rP σ1 (by simp [Function.update_apply, σ1]; omega)
    have e3 := WExec.whrF (cap := cap) (r := rC) (P := .seq (.dec rC) (.ifr rC (.seq (.dec rC) (.inc rH)) (.inc rP)))
      (σ := σ1.setv rP (σ1.val rP + 1)) (by simp [Function.update_apply, σ1, hC])
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.ifrF h0 e2)) e3) ?_ (by omega)
    simp only [σ1]
    weq [hC]
  | v + 2, σ, hC, hH, hP, hv => by
    have e1 := WExec.dec (cap := cap) rC σ (by omega)
    set σ1 := σ.setv rC (σ.val rC - 1) with hσ1
    have h1 : σ1.val rC ≠ 0 := by simp [Function.update_apply, σ1, hC]
    have e2 := WExec.dec (cap := cap) rC σ1 (by simp [Function.update_apply, σ1]; omega)
    set σ2 := σ1.setv rC (σ1.val rC - 1) with hσ2
    have e3 := WExec.inc (cap := cap) rH σ2 (by
      simp [Function.update_apply, σ2, σ1]; have : (v + 2) / 2 = v / 2 + 1 := by omega
      omega)
    set σ3 := σ2.setv rH (σ2.val rH + 1) with hσ3
    have ih := halvP_spec v σ3 (by simp [Function.update_apply, σ3, σ2, σ1, hC])
      (by simp [Function.update_apply, σ3, σ2, σ1]; have : (v + 2) / 2 = v / 2 + 1 := by omega
          omega)
      (by simp [Function.update_apply, σ3, σ2, σ1]; have : (v + 2) % 2 = v % 2 := by omega
          omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.ifrT h1 (WExec.seq e2 e3))) ih) ?_
      (by omega)
    simp only [σ3, σ2, σ1]
    have h2 : (v + 2) / 2 = v / 2 + 1 := by omega
    have h3 : (v + 2) % 2 = v % 2 := by omega
    weq [h2, h3, hC]

/-- One bit of `frame q.bits`: the marker, then `C mod 2`; `C := C / 2`. -/
def bitBody : WM 1 9 :=
  .seq (emitC sOut rO true) (.seq halvP (.seq (.ifr rP (.seq (emitC sOut rO true) (.dec rP)) (emitC sOut rO false))
    (WM.move rH rC)))

theorem bitBody_spec (v : ℕ) (σ : WState 1 9) (pre : List Bool) (hC : σ.val rC = v) (hH : σ.val rH = 0)
    (hP : σ.val rP = 0) (hst : σ.st sOut = pre) (hsh : σ.sh sOut = pre.length) (hO : σ.val rO = pre.length)
    (hcap : pre.length + 2 < cap) (hv : v + 1 ≤ cap) :
    WExec cap bitBody σ ((((σ.sets sOut (pre ++ [true, decide (v % 2 = 1)])).seth sOut (pre.length + 2)).setv rO
      (pre.length + 2)).setv rC (v / 2)) (9 * v + 25) := by
  have e1 := emitC_spec cap sOut rO true σ (by rw [hst, hsh]) (by omega)
  set σ1 := ((σ.sets sOut (σ.st sOut ++ [true])).seth sOut (σ.sh sOut + 1)).setv rO (σ.val rO + 1) with hσ1
  have e2 := halvP_spec cap v σ1 (by simp [Function.update_apply, σ1, hC]) (by simp [Function.update_apply, σ1, hH]; omega) (by simp [Function.update_apply, σ1, hP]; omega) (by omega)
  set σ2 := ((σ1.setv rC 0).setv rH (σ1.val rH + v / 2)).setv rP (σ1.val rP + v % 2) with hσ2
  have hσ2H : σ2.val rH = v / 2 := by simp [Function.update_apply, σ2, σ1, hH]
  have hσ2O : σ2.sh sOut = (σ2.st sOut).length := by simp [Function.update_apply, σ2, σ1, hst, hsh]
  have hσ2o : σ2.val rO = pre.length + 1 := by simp [Function.update_apply, σ2, σ1, hO]
  rcases Nat.mod_two_eq_zero_or_one v with hpar | hpar
  · have hP2 : σ2.val rP = 0 := by simp [Function.update_apply, σ2, σ1, hP, hpar]
    have e3 := emitC_spec cap sOut rO false σ2 hσ2O (by omega)
    set σ3 := ((σ2.sets sOut (σ2.st sOut ++ [false])).seth sOut (σ2.sh sOut + 1)).setv rO (σ2.val rO + 1) with hσ3
    have e4 := wmove_spec cap rH rC (by decide) (v / 2) σ3 (by simp [Function.update_apply, σ3, hσ2H])
      (by simp [Function.update_apply, σ3, hσ2H]; omega)
      (by simp [Function.update_apply, σ3, σ2, σ1, hH]; omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq (WExec.ifrF hP2 e3) e4))) ?_ (by omega)
    simp only [σ3, σ2, σ1]
    weq [hpar, hst, hsh, hO, hC, hH, hP]
  · have hP2 : σ2.val rP = 1 := by simp [Function.update_apply, σ2, σ1, hP, hpar]
    have e3 := emitC_spec cap sOut rO true σ2 hσ2O (by omega)
    set σ3 := ((σ2.sets sOut (σ2.st sOut ++ [true])).seth sOut (σ2.sh sOut + 1)).setv rO (σ2.val rO + 1) with hσ3
    have e3' := WExec.dec (cap := cap) rP σ3 (by simp [Function.update_apply, σ3, hP2]; omega)
    set σ4 := σ3.setv rP (σ3.val rP - 1) with hσ4
    have e4 := wmove_spec cap rH rC (by decide) (v / 2) σ4 (by simp [Function.update_apply, σ4, σ3, hσ2H])
      (by simp [Function.update_apply, σ4, σ3, hσ2H]; omega)
      (by simp [Function.update_apply, σ4, σ3, σ2, σ1, hH]; omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq (WExec.ifrT (by omega) (WExec.seq e3 e3')) e4)))
      ?_ (by omega)
    simp only [σ4, σ3, σ2, σ1]
    weq [hpar, hst, hsh, hO, hC, hH, hP]

/-- `frame`-without-terminator of `C.bits` appended to the output; `C := 0`. -/
def bitsL : WM 1 9 := .whr rC bitBody

theorem bitsL_spec : ∀ (v : ℕ) (σ : WState 1 9) (pre : List Bool), σ.val rC = v → σ.val rH = 0 →
    σ.val rP = 0 → σ.st sOut = pre → σ.sh sOut = pre.length → σ.val rO = pre.length →
    pre.length + 2 * v + 2 < cap → v + 1 ≤ cap →
    WExec cap bitsL σ ((((σ.sets sOut (pre ++ frameP v.bits)).seth sOut (pre.length + 2 * v.bits.length)).setv rO
      (pre.length + 2 * v.bits.length)).setv rC 0) (30 * v + 30 * v.bits.length + 1) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro σ pre hC hH hP hst hsh hO hcap hv
    rcases Nat.eq_zero_or_pos v with rfl | hpos
    · refine WExec.cast cap (WExec.whrF hC) ?_ (by omega)
      simp only [Nat.zero_bits, frameP_nil, List.append_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
      weq [hst, hsh, hO, hC]
    · have e1 := bitBody_spec cap v σ pre hC hH hP hst hsh hO (by omega) hv
      set σ1 := (((σ.sets sOut (pre ++ [true, decide (v % 2 = 1)])).seth sOut (pre.length + 2)).setv rO
        (pre.length + 2)).setv rC (v / 2) with hσ1
      have hb := bits_cons v (by omega)
      have hlen : v.bits.length = (v / 2).bits.length + 1 := by rw [hb]; rfl
      have hl2 := bits_length_le (v / 2)
      have ih' := ih (v / 2) (by omega) σ1 (pre ++ [true, decide (v % 2 = 1)]) (by simp [Function.update_apply, σ1]) (by simp [Function.update_apply, σ1, hH])
        (by simp [Function.update_apply, σ1, hP]) (by simp [Function.update_apply, σ1]) (by simp [Function.update_apply, σ1]) (by simp [Function.update_apply, σ1]) (by simp; omega) (by omega)
      refine WExec.cast cap (WExec.whrT (by omega) e1 ih') ?_ (by rw [hlen]; omega)
      simp only [σ1]
      have hfp : pre ++ [true, decide (v % 2 = 1)] ++ frameP (v / 2).bits = pre ++ frameP v.bits := by
        rw [hb]; simp
      weq [hfp, hlen, hst, hsh, hO]

/-- `1^C` appended to the output; `C := 0`. -/
def unaL : WM 1 9 := .whr rC (.seq (.dec rC) (emitC sOut rO true))

theorem unaL_spec : ∀ (v : ℕ) (σ : WState 1 9) (pre : List Bool), σ.val rC = v → σ.st sOut = pre →
    σ.sh sOut = pre.length → σ.val rO = pre.length → pre.length + v < cap → v ≤ cap →
    WExec cap unaL σ ((((σ.sets sOut (pre ++ List.replicate v true)).seth sOut (pre.length + v)).setv rO
      (pre.length + v)).setv rC 0) (11 * v + 1)
  | 0, σ, pre, hC, hst, hsh, hO, _, _ => by
    refine WExec.cast cap (WExec.whrF hC) ?_ (by omega)
    simp only [List.replicate_zero, List.append_nil, Nat.add_zero]
    weq [hst, hsh, hO, hC]
  | v + 1, σ, pre, hC, hst, hsh, hO, hcap, hv => by
    have e1 := WExec.dec (cap := cap) rC σ (by omega)
    set σ1 := σ.setv rC (σ.val rC - 1) with hσ1
    have e2 := emitC_spec cap sOut rO true σ1 (by simp [Function.update_apply, σ1, hst, hsh]) (by simp [Function.update_apply, σ1, hO]; omega)
    set σ2 := ((σ1.sets sOut (σ1.st sOut ++ [true])).seth sOut (σ1.sh sOut + 1)).setv rO (σ1.val rO + 1) with hσ2
    have ih := unaL_spec v σ2 (pre ++ [true]) (by simp [Function.update_apply, σ2, σ1, hC]) (by simp [Function.update_apply, σ2, σ1, hst]) (by simp [Function.update_apply, σ2, σ1, hsh])
      (by simp [Function.update_apply, σ2, σ1, hO]) (by simp; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih) ?_ (by omega)
    simp only [σ2, σ1]
    have hr : pre ++ [true] ++ List.replicate v true = pre ++ List.replicate (v + 1) true := by
      rw [List.replicate_succ, List.append_assoc]; rfl
    weq [hr, hst, hsh, hO, hC]

/-! ## Phases 1–5: the front -/

/-- Phases 1–5: `C := q(2^{⌊log₂ N⌋})` from `frame x` on stream `0`. -/
def front (k A : ℕ) : WM 1 9 :=
  .seq cntL (.seq (hcW rX rR rH) (.seq (.dec rR) (.seq (mulL (k + 2)) (.seq (.inc rU) (.seq (hcW rU rM rH)
    (.seq (addL A) (incN rC A)))))))

/-- `c = ν(k+2)` at input length `N` (`ν = hc N − 1 = ⌊log₂ N⌋`). -/
def cOf (k N : ℕ) : ℕ := (hc N - 1) * (k + 2)

/-- The front's cost at input length `N`. -/
def frontCost (k A N : ℕ) : ℕ :=
  (9 * N + 1) + (30 * N + 20 * hc N + 1) + 1 + ((hc N - 1) * (8 * (k + 2) + 5) + 1) + 3 +
    (30 * (cOf k N + 1) + 20 * hc (cOf k N + 1) + 1) + (hc (cOf k N + 1) * (4 * A + 4) + 1) + 4 * A + 7

theorem q_eq (k A N : ℕ) :
    Outer.widthOf k A (2 ^ Nat.log 2 N) = cOf k N + hc (cOf k N + 1) * A + A := by
  rw [widthOf_two_pow, log_eq_hc, cOf, Nat.mul_comm A]

theorem front_spec (k A : ℕ) (σ : WState 1 9) (u : List Bool) (hst : σ.st 0 = RepairOrdinary.frame u)
    (hsh : σ.sh 0 = 0) (hval : ∀ r, σ.val r = 0)
    (hcap : u.length + Outer.widthOf k A (2 ^ Nat.log 2 u.length) + 2 ≤ cap) :
    WExec cap (front k A) σ ((σ.seth 0 (2 * u.length)).setv rC (Outer.widthOf k A (2 ^ Nat.log 2 u.length)))
      (frontCost k A u.length) := by
  set N := u.length with hN
  have hq := q_eq k A N
  set c := cOf k N with hc'
  set m := hc (c + 1) with hm
  have hcN : hc N ≤ N := hc_le N
  have hm1 : m ≤ c + 1 := hc_le _
  rw [hq] at hcap ⊢
  have e1 := cntL_spec cap u N 0 σ (by omega) hst (by rw [hsh]) (hval _) (by omega)
  set σ1 := (σ.seth 0 (2 * N)).setv rX N with hσ1
  have e2 := hcW_spec cap rX rR rH (by decide) (by decide) (by decide) N σ1 (by simp [σ1])
    (by simp [σ1, Function.update_apply, hval]) (by simp [σ1, Function.update_apply, hval]; omega) (by omega)
  set σ2 := (σ1.setv rX 0).setv rR (σ1.val rR + hc N) with hσ2
  have e3 := WExec.dec (cap := cap) rR σ2 (by simp [σ2, σ1, Function.update_apply, hval]; omega)
  set σ3 := σ2.setv rR (σ2.val rR - 1) with hσ3
  have hR3 : σ3.val rR = hc N - 1 := by simp [σ3, σ2, σ1, Function.update_apply, hval]
  have e4 := mulL_spec cap (k + 2) (hc N - 1) σ3 hR3
    (by simp [σ3, σ2, σ1, Function.update_apply, hval]; simp only [cOf] at hc'; nlinarith)
    (by simp [σ3, σ2, σ1, Function.update_apply, hval]; simp only [cOf] at hc'; nlinarith) (by omega)
  set σ4 := ((σ3.setv rR 0).setv rC (σ3.val rC + (hc N - 1) * (k + 2))).setv rU (σ3.val rU + (hc N - 1) * (k + 2))
    with hσ4
  have e5 := WExec.inc (cap := cap) rU σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hval]; simp only [cOf] at hc'; omega)
  set σ5 := σ4.setv rU (σ4.val rU + 1) with hσ5
  have hU5 : σ5.val rU = c + 1 := by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hval, c, cOf]
  have e6 := hcW_spec cap rU rM rH (by decide) (by decide) (by decide) (c + 1) σ5 hU5
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hval])
    (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hval]; omega) (by omega)
  set σ6 := (σ5.setv rU 0).setv rM (σ5.val rM + hc (c + 1)) with hσ6
  have hM6 : σ6.val rM = m := by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hval, m]
  have hC6 : σ6.val rC = c := by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hval, c, cOf]
  have e7 := addL_spec cap A m σ6 hM6 (by rw [hC6]; nlinarith) (by omega)
  set σ7 := (σ6.setv rM 0).setv rC (σ6.val rC + m * A) with hσ7
  have e8 := incN_spec cap rC A σ7 (by simp [σ7, Function.update_apply, hC6]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ (by simp only [frontCost, c, m]; omega)
  simp only [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  weq [hval, hC6, c, cOf]

/-! ## The two programs -/

/-- `frame q.bits` on stream `1`. -/
def widthBitsP (k A : ℕ) : WMX 1 9 := .wm (.seq (front k A) (.seq bitsL (emitC sOut rO false)))

/-- `1^q` on stream `1`. -/
def widthUnaryP (k A : ℕ) : WMX 1 9 := .wm (.seq (front k A) unaL)

/-- The cost of `widthBitsP` at input length `N`. -/
def bitsCost (k A N : ℕ) : ℕ :=
  frontCost k A N + 1 + ((30 * Outer.widthOf k A (2 ^ Nat.log 2 N) +
    30 * (Outer.widthOf k A (2 ^ Nat.log 2 N)).bits.length + 1) + 1 + 7)

/-- The cost of `widthUnaryP` at input length `N`. -/
def unaryCost (k A N : ℕ) : ℕ := frontCost k A N + 1 + (11 * Outer.widthOf k A (2 ^ Nat.log 2 N) + 1)

theorem widthBitsP_spec (k A : ℕ) (σ : WState 1 9) (u : List Bool) (hst : σ.st 0 = RepairOrdinary.frame u)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) (hout : σ.st sOut = [])
    (hcap : u.length + 2 * Outer.widthOf k A (2 ^ Nat.log 2 u.length) + 4 ≤ cap) :
    ∃ τ, WXExec cap (widthBitsP k A) σ τ (bitsCost k A u.length) ∧
      τ.st sOut = RepairOrdinary.frame (Outer.widthOf k A (2 ^ Nat.log 2 u.length)).bits := by
  set q := Outer.widthOf k A (2 ^ Nat.log 2 u.length) with hq
  have e1 := front_spec cap k A σ u hst (hsh 0) hval (by omega)
  set σ1 := (σ.seth 0 (2 * u.length)).setv rC q with hσ1
  have hbl := bits_length_le q
  have e2 := bitsL_spec cap q σ1 [] (by simp [σ1]) (by simp [σ1, Function.update_apply, hval])
    (by simp [σ1, Function.update_apply, hval]) (by simp [σ1, hout]) (by simp [σ1, Function.update_apply, hsh])
    (by simp [σ1, Function.update_apply, hval]) (by simp; omega) (by omega)
  set σ2 := (((σ1.sets sOut ([] ++ frameP q.bits)).seth sOut ([].length + 2 * q.bits.length)).setv rO
    ([].length + 2 * q.bits.length)).setv rC 0 with hσ2
  have e3 := emitC_spec cap sOut rO false σ2 (by simp [σ2]) (by simp [σ2, Function.update_apply]; omega)
  refine ⟨_, WXExec.wm (WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by simp only [bitsCost, q]; omega)), ?_⟩
  simp [σ2, frame_eq_frameP]

theorem widthUnaryP_spec (k A : ℕ) (σ : WState 1 9) (u : List Bool) (hst : σ.st 0 = RepairOrdinary.frame u)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) (hout : σ.st sOut = [])
    (hcap : u.length + 2 * Outer.widthOf k A (2 ^ Nat.log 2 u.length) + 4 ≤ cap) :
    ∃ τ, WXExec cap (widthUnaryP k A) σ τ (unaryCost k A u.length) ∧
      τ.st sOut = List.replicate (Outer.widthOf k A (2 ^ Nat.log 2 u.length)) true := by
  set q := Outer.widthOf k A (2 ^ Nat.log 2 u.length) with hq
  have e1 := front_spec cap k A σ u hst (hsh 0) hval (by omega)
  set σ1 := (σ.seth 0 (2 * u.length)).setv rC q with hσ1
  have e2 := unaL_spec cap q σ1 [] (by simp [σ1]) (by simp [σ1, hout]) (by simp [σ1, Function.update_apply, hsh])
    (by simp [σ1, Function.update_apply, hval]) (by simp; omega) (by omega)
  refine ⟨_, WXExec.wm (WExec.mono (WExec.seq e1 e2) (by simp only [unaryCost, q]; omega)), ?_⟩
  simp

end NearCubicGates.Close.OuterM
