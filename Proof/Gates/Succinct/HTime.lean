import Proof.Gates.Succinct.PointLoop

/-!
# 𝒱_G, part 7: the hierarchy clock and the witness prefix

Paper: lem:succinct-verifier (app:multitape), stage (4): "It runs `𝒟` on `tt_N(B)`, using that work tape as the
input tape of `𝒟`, its own witness tape as the witness tape of `𝒟`". The hierarchy verifier `H.verifier` halts within
`H.time N = c_H (N^{k+2} + 1)` steps on witnesses of exactly that length, so the verifier hands it the first
`H.time N` witness bits (blanks past the end), framed:
* `htW`: `HT := c·(N^{k+2} + 1)` (**`htW_spec`**);
* `wpW`: `WP := frame (prefixBits y HT)` from `frame y` on the witness stream (**`wpW_spec`**).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-! ## The hierarchy clock -/

/-- `R += c` (`c` increments). -/
def incsW (R : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | c + 1 => .seq (incsW R c) (WMX.inc R)

theorem incsW_spec (cap : ℕ) (R : Fin nr) : ∀ (c : ℕ) (σ : WState ns nr), σ.val R + c ≤ cap →
    WXExec cap (incsW R c) σ (σ.setv R (σ.val R + c)) (4 * c)
  | 0, σ, _ => by simp [incsW, wsetv_same]; exact WXExec.skip cap σ
  | c + 1, σ, h => by
    have e1 := incsW_spec cap R c σ (by omega)
    have e2 := WXExec.inc cap R (σ.setv R (σ.val R + c)) (by simp; omega)
    refine WXExec.cast cap (WXExec.seq e1 e2) ?_ (by omega)
    simp [wsetv_setv]; ring_nf

/-- `HT := c·(N^{k+2} + 1)`, `N` in `NN`. -/
def htW (c k : ℕ) (E : VReg → Fin nr) : WMX ns nr :=
  .seq (powW (E .x) (E .x2) (E .nN) (E .y) (E .t) (k + 2)) (.seq (WMX.inc (E .x)) (.seq (incsW (E .p) c)
    (.seq (mulR (E .p) (E .x2) (E .x) (E .ht) (E .t)) (.seq (.wm (WM.clear (E .x))) (.wm (WM.clear (E .p)))))))

/-- The hierarchy clock value (paper lem:succinct-verifier, stage (4); `OrdinaryHierarchy.time` at `N`). -/
def htVal (c k N : ℕ) : ℕ := c * (N ^ (k + 2) + 1)

theorem htW_spec (cap c k : ℕ) (E : VReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr) (N : ℕ)
    (hN : σ.val (E .nN) = N) (hz : ∀ q ∈ [VReg.x, .x2, .y, .t, .p, .ht], σ.val (E q) = 0)
    (hcap : 3 * (c + 1) * (N + 2) ^ (k + 3) + 10 ≤ cap) :
    WXExec cap (htW c k E) σ (σ.setv (E .ht) (htVal c k N)) (100 * (c + 1) * (k + 3) * (N + 2) ^ (k + 2) + 10) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  have zx := hz .x (by simp); have zx2 := hz .x2 (by simp); have zy := hz .y (by simp)
  have zt := hz .t (by simp); have zp := hz .p (by simp); have zht := hz .ht (by simp)
  have hpow1 : (N + 1) ^ (k + 3) ≤ (N + 2) ^ (k + 3) := Nat.pow_le_pow_left (by omega) _
  have hpow2 : N ^ (k + 2) + 1 ≤ (N + 2) ^ (k + 3) := by
    have h1 : N ^ (k + 2) < (N + 1) ^ (k + 2) := Nat.pow_lt_pow_left (by omega) (by omega)
    have h2 : (N + 1) ^ (k + 2) ≤ (N + 1) ^ (k + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hQ : 1 ≤ (N + 2) ^ (k + 3) := Nat.one_le_pow _ _ (by omega)
  have hQc : (N + 2) ^ (k + 3) ≤ 3 * (c + 1) * (N + 2) ^ (k + 3) := by nlinarith
  have hcQ : c * (N ^ (k + 2) + 1) ≤ 3 * (c + 1) * (N + 2) ^ (k + 3) := by nlinarith
  have e1 := powW_spec cap (E .x) (E .x2) (E .nN) (E .y) (E .t) (by simp [List.nodup_cons, hE.eq_iff]) N (k + 2) σ
    zx hN zx2 zy zt (by have : (N + 1) ^ (k + 2) ≤ (N + 2) ^ (k + 3) :=
                          (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
                        nlinarith)
  have e2 := WXExec.inc cap (E .x) (σ.setv (E .x) (N ^ (k + 2))) (by simp; nlinarith)
  rw [show (σ.setv (E .x) (N ^ (k + 2))).setv (E .x) ((σ.setv (E .x) (N ^ (k + 2))).val (E .x) + 1) =
    σ.setv (E .x) (N ^ (k + 2) + 1) by simp [wsetv_setv]] at e2
  have e3 := incsW_spec cap (E .p) c (σ.setv (E .x) (N ^ (k + 2) + 1))
    (by simp [Function.update_apply, hE.eq_iff, zp]; nlinarith)
  rw [show (σ.setv (E .x) (N ^ (k + 2) + 1)).val (E .p) = 0 by simp [Function.update_apply, hE.eq_iff, zp],
    Nat.zero_add] at e3
  set σ3 := (σ.setv (E .x) (N ^ (k + 2) + 1)).setv (E .p) c with hσ3
  have e4 := mulR_spec cap (A := E .p) (A2 := E .x2) (B := E .x) (C := E .ht) (T := E .t)
    (by simp [List.nodup_cons, hE.eq_iff]) σ3 (by simp [σ3, Function.update_apply, hE.eq_iff, zx2])
    (by simp [σ3, Function.update_apply, hE.eq_iff, zt])
    (by simp [σ3, Function.update_apply, hE.eq_iff, zht]; nlinarith) (by simp [σ3]; nlinarith)
  have hv : σ3.val (E .ht) + σ3.val (E .p) * σ3.val (E .x) = htVal c k N := by
    simp [σ3, Function.update_apply, hE.eq_iff, zht, htVal]
  rw [hv] at e4
  have e5 := wclear_spec cap (E .x) (N ^ (k + 2) + 1) (σ3.setv (E .ht) (htVal c k N))
    (by simp [σ3, Function.update_apply, hE.eq_iff]) (by simp [σ3, Function.update_apply, hE.eq_iff]; omega)
  have e6 := wclear_spec cap (E .p) c ((σ3.setv (E .ht) (htVal c k N)).setv (E .x) 0)
    (by simp [σ3, Function.update_apply, hE.eq_iff]) (by simp [σ3, Function.update_apply, hE.eq_iff]; nlinarith)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq (WXExec.wm e5)
    (WXExec.wm e6)))))) ?_ ?_
  · refine WState.eq rfl rfl ?_ rfl
    funext q; simp only [σ3, WState.setv_val, Function.update_apply]
    by_cases hqp : q = E .p
    · subst hqp; simp [hE.eq_iff, zp]
    · by_cases hqx : q = E .x
      · subst hqx; simp [hE.eq_iff, zx]
      · simp [hqp, hqx]
  · simp only [σ3, WState.setv_val, Function.update_apply, hE.eq_iff, reduceCtorEq, if_true, if_false]
    have hq1 : (N + 1) ^ (k + 2) ≤ (N + 2) ^ (k + 2) := Nat.pow_le_pow_left (by omega) _
    have hq2 : N ^ (k + 2) + 1 ≤ (N + 2) ^ (k + 2) := by
      have : N ^ (k + 2) < (N + 2) ^ (k + 2) := Nat.pow_lt_pow_left (by omega) (by omega)
      omega
    have hq3 : 1 ≤ (N + 2) ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
    have hA : (k + 2) * (61 * (N + 1) ^ (k + 2)) ≤ 61 * ((k + 3) * (N + 2) ^ (k + 2)) :=
      calc (k + 2) * (61 * (N + 1) ^ (k + 2)) ≤ (k + 3) * (61 * (N + 2) ^ (k + 2)) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hq1)
        _ = 61 * ((k + 3) * (N + 2) ^ (k + 2)) := by ring
    have hB : c * (18 * (N ^ (k + 2) + 1) + 3 + 8) ≤ 29 * (c * (N + 2) ^ (k + 2)) := by
      have : c * (N ^ (k + 2) + 1) ≤ c * (N + 2) ^ (k + 2) := Nat.mul_le_mul_left _ hq2
      have : c ≤ c * (N + 2) ^ (k + 2) := Nat.le_mul_of_pos_right _ hq3
      nlinarith
    have hC : (N + 2) ^ (k + 2) ≤ (k + 3) * (N + 2) ^ (k + 2) := Nat.le_mul_of_pos_left _ (by omega)
    have hD : c * (N + 2) ^ (k + 2) ≤ c * ((k + 3) * (N + 2) ^ (k + 2)) := Nat.mul_le_mul_left _ hC
    have hE' : c ≤ c * (N + 2) ^ (k + 2) := Nat.le_mul_of_pos_right _ hq3
    have hR : 100 * (c + 1) * (k + 3) * (N + 2) ^ (k + 2) =
        100 * ((k + 3) * (N + 2) ^ (k + 2)) + 100 * (c * ((k + 3) * (N + 2) ^ (k + 2))) := by ring
    rw [hR]
    generalize (k + 2) * (61 * (N + 1) ^ (k + 2)) = a1 at hA ⊢
    generalize c * (18 * (N ^ (k + 2) + 1) + 3 + 8) = a2 at hB ⊢
    generalize c * ((k + 3) * (N + 2) ^ (k + 2)) = a3 at hD ⊢
    generalize c * (N + 2) ^ (k + 2) = a4 at hB hD hE' ⊢
    generalize (k + 3) * (N + 2) ^ (k + 2) = a5 at hA hC ⊢
    omega

/-! ## The witness prefix -/

/-- The first `m` witness bits, blanks past the end (paper lem:succinct-verifier, stage (4): the witness bits that
`𝒟` can read). -/
def prefixBits (y : List Bool) (m : ℕ) : List Bool := List.ofFn fun i : Fin m => y.getD i.val false

theorem prefixBits_succ (y : List Bool) (m : ℕ) : prefixBits y (m + 1) = prefixBits y m ++ [y.getD m false] := by
  unfold prefixBits; rw [List.ofFn_succ_last]; simp

theorem prefixBits_length (y : List Bool) (m : ℕ) : (prefixBits y m).length = m := by simp [prefixBits]

/-- One witness cell: on a marker, copy the data bit framed and step past the pair; at the end, append a framed
blank. -/
def wcell (WIT WP : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .ifs WIT (.seq (.fwd WIT) (.seq (emitC WP OP true) (.seq (.ifs WIT (emitC WP OP true) (emitC WP OP false))
    (.fwd WIT)))) (.seq (emitC WP OP true) (emitC WP OP false))

theorem wcell_spec (cap : ℕ) (WIT WP : Fin (ns + 1)) (hWW : WIT ≠ WP) (OP : Fin nr) (y : List Bool) (j : ℕ)
    (σ : WState ns nr) (hst : σ.st WIT = RepairOrdinary.frame y) (hsh : σ.sh WIT = 2 * min j y.length)
    (hd : σ.sh WP = (σ.st WP).length) (hc : σ.val OP + 2 ≤ cap) :
    WExec cap (wcell WIT WP OP) σ
      ((((σ.sets WP (σ.st WP ++ [true, y.getD j false])).seth WP (σ.sh WP + 2)).setv OP (σ.val OP + 2)).seth WIT
        (2 * min (j + 1) y.length)) 22 := by
  have hWW' := Ne.symm hWW
  by_cases hj : j < y.length
  · have hm : min j y.length = j := by omega
    have hm1 : min (j + 1) y.length = j + 1 := by omega
    rw [hm] at hsh; rw [hm1]
    have hb0 : wbit σ WIT = true := by simp [wbit, hst, hsh, frame_even, hj]
    have e1 := WExec.fwd (cap := cap) WIT σ
    set σ1 := σ.seth WIT (σ.sh WIT + 1) with hσ1
    have e2 := emitC_spec cap WP OP true σ1 (by simp [σ1, Function.update_apply, hWW', hd]) (by simp [σ1]; omega)
    set σ2 := ((σ1.sets WP (σ1.st WP ++ [true])).seth WP (σ1.sh WP + 1)).setv OP (σ1.val OP + 1) with hσ2
    have hb1 : wbit σ2 WIT = y.getD j false := by
      simp [wbit, σ2, σ1, Function.update_apply, hWW, hst, hsh]; exact frame_odd y j hj
    have hd2 : σ2.sh WP = (σ2.st WP).length := by simp [σ2, σ1, Function.update_apply, hWW', hd]
    have hc2 : σ2.val OP < cap := by simp [σ2, σ1]; omega
    have e3 : WExec cap (.ifs WIT (emitC WP OP true) (emitC WP OP false)) σ2
        (((σ2.sets WP (σ2.st WP ++ [y.getD j false])).seth WP (σ2.sh WP + 1)).setv OP (σ2.val OP + 1)) 8 := by
      cases hb : y.getD j false
      · exact WExec.mono (WExec.ifsF (by rw [hb1, hb]) (emitC_spec cap WP OP false σ2 hd2 hc2)) (by omega)
      · exact WExec.mono (WExec.ifsT (by rw [hb1, hb]) (emitC_spec cap WP OP true σ2 hd2 hc2)) (by omega)
    set σ3 := ((σ2.sets WP (σ2.st WP ++ [y.getD j false])).seth WP (σ2.sh WP + 1)).setv OP (σ2.val OP + 1) with hσ3
    have e4 := WExec.fwd (cap := cap) WIT σ3
    refine WExec.mono (WExec.cast cap (WExec.ifsT hb0 (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)))) ?_ le_rfl)
      (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = WIT
      · subst hx; simp [σ3, σ2, σ1, Function.update_apply, hWW, hsh]; ring
      · by_cases hx2 : x = WP
        · subst hx2; simp [σ3, σ2, σ1, Function.update_apply, hWW, hWW']; try ring
        · simp [σ3, σ2, σ1, Function.update_apply, hx, hx2]
    · funext x; by_cases hx2 : x = WP
      · subst hx2; simp [σ3, σ2, σ1, Function.update_apply, hWW']
      · simp [σ3, σ2, σ1, Function.update_apply, hx2]
    · funext q; by_cases hq : q = OP
      · subst hq; simp [σ3, σ2, σ1]; try ring
      · simp [σ3, σ2, σ1, Function.update_apply, hq]
  · have hm : min j y.length = y.length := by omega
    have hm1 : min (j + 1) y.length = y.length := by omega
    rw [hm] at hsh; rw [hm1]
    have hb0 : wbit σ WIT = false := by simp [wbit, hst, hsh, frame_even]
    have hgd : y.getD j false = false := List.getD_eq_default _ _ (by omega)
    rw [hgd]
    have e1 := emitC_spec cap WP OP true σ hd (by omega)
    set σ1 := ((σ.sets WP (σ.st WP ++ [true])).seth WP (σ.sh WP + 1)).setv OP (σ.val OP + 1) with hσ1
    have e2 := emitC_spec cap WP OP false σ1 (by simp [σ1, hd]) (by simp [σ1]; omega)
    refine WExec.mono (WExec.cast cap (WExec.ifsF hb0 (WExec.seq e1 e2)) ?_ le_rfl) (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = WIT
      · subst hx; simp [σ1, Function.update_apply, hWW, hsh]
      · by_cases hx2 : x = WP
        · subst hx2; simp [σ1, Function.update_apply, hWW']; try ring
        · simp [σ1, Function.update_apply, hx, hx2]
    · funext x; by_cases hx2 : x = WP
      · subst hx2; simp [σ1]
      · simp [σ1, Function.update_apply, hx2]
    · funext q; by_cases hq : q = OP
      · subst hq; simp [σ1]; try ring
      · simp [σ1, Function.update_apply, hq]

/-- **The witness prefix** (paper lem:succinct-verifier, stage (4)): `WP := frame (prefixBits y HT)`, head `0`. -/
def wpW (WIT WP : Fin (ns + 1)) (E : VReg → Fin nr) : WM ns nr :=
  .seq (addTo (E .ht) (E .k2) (E .t)) (.seq (.whr (E .k2) (.seq (.dec (E .k2)) (wcell WIT WP (E .wop))))
    (.seq (emitC WP (E .wop) false) (WM.rewind WP (E .wop))))

theorem wpW_spec (cap : ℕ) (WIT WP : Fin (ns + 1)) (hWW : WIT ≠ WP) (E : VReg → Fin nr) (hE : Function.Injective E)
    (σ : WState ns nr) (y : List Bool) (m : ℕ) (hst : σ.st WIT = RepairOrdinary.frame y) (hsh : σ.sh WIT = 0)
    (hWP : σ.st WP = []) (hWPh : σ.sh WP = 0) (hht : σ.val (E .ht) = m)
    (hz : ∀ q ∈ [VReg.k2, .t, .wop], σ.val (E q) = 0) (hcap : 2 * m + 4 ≤ cap) :
    ∃ τ, WExec cap (wpW WIT WP E) σ τ (60 * m + 30) ∧ τ.st WP = RepairOrdinary.frame (prefixBits y m) ∧
      τ.sh WP = 0 ∧ SameExcept σ τ [WIT, WP] [] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  have zk := hz .k2 (by simp); have zt := hz .t (by simp); have zw := hz .wop (by simp)
  have e1 := addTo_spec cap (E .ht) (E .k2) (E .t) (hE.ne (by decide)) (hE.ne (by decide)) (hE.ne (by decide)) σ zt
    (by omega) (by omega)
  rw [zk, hht, Nat.zero_add] at e1
  set σ1 := σ.setv (E .k2) m with hσ1
  let S : ℕ → WState ns nr := fun j =>
    (((σ1.sets WP (marks (prefixBits y j))).seth WP (2 * j)).setv (E .wop) (2 * j)).seth WIT (2 * min j y.length) |>.setv
      (E .k2) (m - j)
  have hS0 : S 0 = σ1 := by
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = WIT
      · subst hx; simp [S, σ1, hsh]
      · by_cases hx2 : x = WP
        · subst hx2; simp [S, σ1, Function.update_apply, hx, hWPh]
        · simp [S, σ1, Function.update_apply, hx, hx2]
    · funext x; by_cases hx2 : x = WP
      · subst hx2; simp [S, σ1, hWP, prefixBits, marks]
      · simp [S, σ1, Function.update_apply, hx2]
    · funext q; simp only [S, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases hq : q = E .k2
      · subst hq; simp
      · by_cases hq2 : q = E .wop
        · subst hq2; simp [hq, zw]
        · simp [hq, hq2]
  have e2 := UnionMachine.Round.wloop cap (E .k2) (wcell WIT WP (E .wop)) 22 m S
    (fun j _ => by simp [S]) (by omega)
    (fun j hj => by
      have := wcell_spec cap WIT WP hWW (E .wop) y j ((S j).setv (E .k2) (m - j - 1)) (by simp [S, Function.update_apply, hWW, Ne.symm hWW, hst, σ1])
        (by simp [S]) (by simp [S, Function.update_apply, hWW, Ne.symm hWW, prefixBits_length])
        (by simp [S, Function.update_apply, hE.eq_iff]; omega)
      refine WExec.cast cap this ?_ le_rfl
      refine WState.eq ?_ ?_ ?_ rfl
      · funext x; by_cases hx : x = WIT
        · subst hx; simp [S]
        · by_cases hx2 : x = WP
          · subst hx2; simp [S, Function.update_apply, hx]; ring
          · simp [S, Function.update_apply, hx, hx2]
      · funext x; by_cases hx2 : x = WP
        · subst hx2; simp [S, prefixBits_succ, marks_append, marks]
        · simp [S, Function.update_apply, hx2]
      · funext q; simp only [S, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
        by_cases hq : q = E .k2
        · subst hq; simp [hE.eq_iff]; omega
        · by_cases hq2 : q = E .wop
          · subst hq2; simp [hq]; ring
          · simp [hq, hq2])
  rw [hS0] at e2
  have e3 := emitC_spec cap WP (E .wop) false (S m) (by simp [S, Function.update_apply, Ne.symm hWW, prefixBits_length])
    (by simp [S, Function.update_apply, hE.eq_iff]; omega)
  set σ3 := (((S m).sets WP ((S m).st WP ++ [false])).seth WP ((S m).sh WP + 1)).setv (E .wop)
    ((S m).val (E .wop) + 1) with hσ3
  have e4 := wrewind_spec cap WP (E .wop) (2 * m + 1) σ3 (by simp [σ3, S, Function.update_apply, hE.eq_iff])
    (by simp [σ3, S, Function.update_apply, hE.eq_iff]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (by omega), ?_, ?_, ?_⟩
  · simp [σ3, S, Function.update_apply, Ne.symm hWW, frame_eq_marks']
  · simp [σ3, S, Function.update_apply, Ne.symm hWW]
  · refine ⟨fun x hx => ?_, fun q _ => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [σ3, S, σ1, Function.update_apply, hx.1, hx.2]
    · simp only [σ3, S, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases hq : q = E .wop
      · subst hq; simp [zw]
      · by_cases hq2 : q = E .k2
        · subst hq2; simp [hq, zk]
        · simp [hq, hq2]
    · simp [σ3, S, σ1]

end NearCubicGates.Close.Succinct
