import SourceAdapters.Refuter.RLoadParse
import SourceAdapters.Refuter.ClockPrep

/-!
# R's loader, part 2: the unary constants (input 7, R: INIT)

Paper anchor: proof of `lem:multitape-refuter`, Step 1 ("First `𝒟` computes `T(N)` and prepares its clock in `O(T(N)+1)` steps"),
proof of `cor:framed-refuter` (the records `x_i = 1^M 0 1^{N−M−2−g} 0 w_i`, `g = ⌊N/16⌋`, `M` the enumeration index of the
machine), (the request words carry `1^g` and `1^{T(N)}`).

Generic word programs (any layout), each returning every head and counter to `0`:

* `tuP`: `TU := 1^n` from the binary output `n.bits` of the time constructor and its unary step count `1^s`
  (`n < 2^s`): most significant bit first from cell `s`, one unary Horner step `dbl` per cell; the costs form a
  geometric sum, `≤ 40n + 30s + 30` (`tu_spec`; `Clock.sum_div_pow`, `Clock.div_pow_step` reused);
* `guP`: `GU := 1^⌊N/16⌋` by a countdown of period 16 over `NU = 1^N`;
* `muP`: `MU := 1^{M}`, `M = foldl (2a+b) 1 code`, by one Horner step per bit of `CODE = fr(code)`;
* `xuP`: `XU := 1^{N−g−M−2}` by skipping `g + M + 2` cells of `NU`.
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {ns nr : ℕ} (cap : ℕ)

theorem rdr (n : ℕ) (b : Bool) {p : ℕ} (h : p < n) : readTapeBit (List.replicate n b) p = b := by
  unfold readTapeBit
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem rdr_end (n : ℕ) (b : Bool) {p : ℕ} (h : n ≤ p) : readTapeBit (List.replicate n b) p = false := by
  unfold readTapeBit
  rw [List.getD_eq_default _ _ (by simpa using h)]

theorem wtb_rep (n : ℕ) (b : Bool) : writeTapeBit (List.replicate n b) n b = List.replicate (n + 1) b := by
  have := wtb_append (List.replicate n b) b
  rw [List.length_replicate] at this
  rw [this, ← List.replicate_succ']

/-! ## `TU := 1^n`, most significant bit first -/

/-- Walk `KO` to cell `s` along `TL = 1^s`, then one Horner step `TU := 1^(2u+b)` per cell going back. -/
def tuP (TL KO TU : Fin (ns + 1)) (R1 R2 Ra Rb : Fin nr) : WMX ns nr :=
  .seq (.whs TL (.seq (WMX.fwd TL) (.seq (WMX.fwd KO) (.seq (WMX.inc R1) (WMX.inc R2)))))
  (.seq (rew TL R2)
  (.whr R1 (.seq (WMX.dec R1) (.seq (WMX.bwd KO) (.ifs KO (dbl TU Ra Rb true) (dbl TU Ra Rb false))))))

theorem sum_geo (n s : ℕ) : (Finset.range s).sum (fun k => 40 * (n / 2 ^ (s - k)) + 25 + 2) ≤ 40 * n + 27 * s := by
  have h1 : (Finset.range s).sum (fun k => n / 2 ^ (s - k)) ≤ n := by
    have e := Finset.sum_range_reflect (fun j => n / 2 ^ (j + 1)) s
    have e2 : (Finset.range s).sum (fun k => n / 2 ^ (s - 1 - k + 1)) =
        (Finset.range s).sum (fun k => n / 2 ^ (s - k)) := by
      apply Finset.sum_congr rfl; intro k hk; simp at hk; congr 2; omega
    rw [← e2, e]; exact Clock.sum_div_pow n s
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

set_option maxHeartbeats 400000 in
theorem tu_spec (TL KO TU : Fin (ns + 1)) (R1 R2 Ra Rb : Fin nr) (d1 : TL ≠ KO) (d2 : TL ≠ TU) (d3 : KO ≠ TU)
    (q1 : R1 ≠ R2) (q2 : R1 ≠ Ra) (q3 : R1 ≠ Rb) (q4 : R2 ≠ Ra) (q5 : R2 ≠ Rb) (q6 : Ra ≠ Rb)
    (σ : WState ns nr) (B : List Bool) (n s : ℕ) (hB : ∀ j, readTapeBit B j = n.testBit j) (hn : n < 2 ^ s)
    (hTL : σ.st TL = List.replicate s true) (sTL : σ.sh TL = 0) (hKO : σ.st KO = B) (sKO : σ.sh KO = 0)
    (hTU : σ.st TU = []) (sTU : σ.sh TU = 0) (v1 : σ.val R1 = 0) (v2 : σ.val R2 = 0) (va : σ.val Ra = 0)
    (vb : σ.val Rb = 0) (hcap : 2 * n + 2 * s + 2 ≤ cap) :
    WXExec cap (tuP TL KO TU R1 R2 Ra Rb) σ (σ.sets TU (List.replicate n true)) (40 * n + 50 * (s + 1)) := by
  -- walk to cell `s`
  let st1 : ℕ → WState ns nr := fun k => (((σ.seth TL k).seth KO k).setv R1 k).setv R2 k
  have l1 := loopS cap (i := TL) (body := .seq (WMX.fwd TL) (.seq (WMX.fwd KO) (.seq (WMX.inc R1) (WMX.inc R2))))
    st1 s 11
    (fun k hk => by simp only [wbit, st1, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
      Function.update_of_ne d1, Function.update_self, hTL]; exact rdr s true hk)
    (by simp only [wbit, st1, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
      Function.update_of_ne d1, Function.update_self, hTL]; exact rdr_end s true le_rfl)
    (fun k hk => by
      have e1 := WXExec.fwd cap TL (st1 k)
      have e2 := WXExec.fwd cap KO ((st1 k).seth TL ((st1 k).sh TL + 1))
      have e3 := WXExec.inc cap R1 (((st1 k).seth TL ((st1 k).sh TL + 1)).seth KO
        (((st1 k).seth TL ((st1 k).sh TL + 1)).sh KO + 1)) (by simp [st1, Function.update_apply, q1, q1.symm]; omega)
      have e4 := WXExec.inc cap R2 ((((st1 k).seth TL ((st1 k).sh TL + 1)).seth KO
        (((st1 k).seth TL ((st1 k).sh TL + 1)).sh KO + 1)).setv R1 ((((st1 k).seth TL ((st1 k).sh TL + 1)).seth KO
        (((st1 k).seth TL ((st1 k).sh TL + 1)).sh KO + 1)).val R1 + 1)) (by simp [st1, Function.update_apply, q1, q1.symm]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
      simp only [st1]; wst)
  have s10 : st1 0 = σ := by simp only [st1]; wst
  rw [s10] at l1
  have l2 := rew_spec cap TL R2 (st1 s) s (by simp [st1]) (by omega)
  -- the Horner steps
  let st2 : ℕ → WState ns nr := fun k =>
    (((σ.seth KO (s - k)).setv R1 (s - k)).setv R2 0).sets TU (List.replicate (n / 2 ^ (s - k)) true)
  have hz : n / 2 ^ s = 0 := Nat.div_eq_of_lt hn
  have s20 : ((st1 s).setv R2 0).seth TL ((st1 s).sh TL - s) = st2 0 := by
    simp only [st1, st2, Nat.sub_zero, hz, List.replicate_zero]; wst
  rw [s20] at l2
  have l3 := Clock.whrV cap (r := R1)
    (body := .seq (WMX.dec R1) (.seq (WMX.bwd KO) (.ifs KO (dbl TU Ra Rb true) (dbl TU Ra Rb false)))) s st2
    (fun k => 40 * (n / 2 ^ (s - k)) + 25)
    (fun k hk => by simp [st2, Function.update_apply, q1, q1.symm]; omega)
    (by simp [st2, Function.update_apply, q1, q1.symm])
    (fun k hk => by
      set u := n / 2 ^ (s - k) with hu
      have hun : u ≤ n := Nat.div_le_self _ _
      have hstep := Clock.div_pow_step n (s - k - 1)
      rw [show s - k - 1 + 1 = s - k by omega, ← hu] at hstep
      have e1 := WXExec.dec cap R1 (st2 k) (by simp [st2, Function.update_apply, q1, q1.symm]; omega)
      have e2 := WXExec.bwd cap KO ((st2 k).setv R1 ((st2 k).val R1 - 1))
      set τ := ((st2 k).setv R1 ((st2 k).val R1 - 1)).seth KO (((st2 k).setv R1 ((st2 k).val R1 - 1)).sh KO - 1)
        with hτ
      have hb : wbit τ KO = n.testBit (s - k - 1) := by
        simp only [wbit, hτ, st2, WState.seth_st, WState.setv_st, WState.sets_st, WState.seth_sh, WState.setv_sh,
          WState.sets_sh, Function.update_of_ne d3, Function.update_self, hKO, hB]
      have hdbl : ∀ b : Bool, WXExec cap (dbl TU Ra Rb b) τ (τ.sets TU (List.replicate (2 * u + b.toNat) true))
          (40 * u + 20) := fun b =>
        dbl_spec cap TU Ra Rb q6 b τ u (by simp [hτ, st2, hu]) (by simp [hτ, st2, Function.update_of_ne d3.symm, sTU])
          (by simp [hτ, st2, Function.update_apply, q2, q4, q2.symm, q4.symm, va])
          (by simp [hτ, st2, Function.update_apply, q3, q5, q3.symm, q5.symm, vb]) (by omega)
      have e3 : WXExec cap (.ifs KO (dbl TU Ra Rb true) (dbl TU Ra Rb false)) τ
          (τ.sets TU (List.replicate (n / 2 ^ (s - k - 1)) true)) (40 * u + 21) := by
        cases hc : n.testBit (s - k - 1)
        · rw [hc] at hb hstep
          refine (WXExec.ifsF hb (hdbl false)).cast cap ?_ le_rfl
          rw [hstep]; rfl
        · rw [hc] at hb hstep
          refine (WXExec.ifsT hb (hdbl true)).cast cap ?_ le_rfl
          rw [hstep]; rfl
      refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
      rw [hτ]; simp only [st2, show s - (k + 1) = s - k - 1 by omega]; wst)
  have s2s : st2 s = σ.sets TU (List.replicate n true) := by
    simp only [st2, Nat.sub_self, pow_zero, Nat.div_one]; wst
  rw [s2s] at l3
  refine (WXExec.seq l1 (WXExec.seq l2 l3)).mono ?_
  have := sum_geo n s
  nlinarith

/-! ## Repeated increments -/

/-- `k` increments of `R`. -/
def incK (R : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | k + 1 => .seq (WMX.inc R) (incK R k)

theorem incK_spec (R : Fin nr) : ∀ (k : ℕ) (σ : WState ns nr), σ.val R + k ≤ cap →
    WXExec cap (incK R k) σ (σ.setv R (σ.val R + k)) (4 * k)
  | 0, σ, _ => (WXExec.skip cap σ).cast cap (by wst) (by omega)
  | k + 1, σ, h => by
    have e1 := WXExec.inc cap R σ (by omega)
    have e2 := incK_spec R k (σ.setv R (σ.val R + 1)) (by simp; omega)
    refine (WXExec.seq e1 e2).cast cap ?_ (by omega)
    wst

/-! ## `GU := 1^⌊N/16⌋` -/

/-- One cell of `NU`: count down `D`; every 16th cell append `1` to `GU` and reload `D`. -/
def g16 (GU : Fin (ns + 1)) (D RG : Fin nr) : WMX ns nr :=
  .seq (WMX.dec D) (.ifr D WMX.skip (.seq (WMX.wr GU true) (.seq (WMX.fwd GU) (.seq (WMX.inc RG) (incK D 16)))))

def guP (NU GU : Fin (ns + 1)) (R D RG : Fin nr) : WMX ns nr :=
  .seq (incK D 16) (.seq (forU NU R (g16 GU D RG)) (.seq (.whr D (WMX.dec D)) (rew GU RG)))

set_option maxHeartbeats 400000 in
theorem gu_spec (NU GU : Fin (ns + 1)) (R D RG : Fin nr) (d1 : NU ≠ GU) (q1 : R ≠ D) (q2 : R ≠ RG)
    (q4 : D ≠ RG) (σ : WState ns nr) (N : ℕ)
    (hNU : σ.st NU = List.replicate N true) (sNU : σ.sh NU = 0) (hGU : σ.st GU = []) (sGU : σ.sh GU = 0)
    (vR : σ.val R = 0) (vD : σ.val D = 0) (vG : σ.val RG = 0) (hcap : 2 * N + 40 ≤ cap) :
    WXExec cap (guP NU GU R D RG) σ (σ.sets GU (List.replicate (N / 16) true)) (200 * (N + 1)) := by
  have e1 := incK_spec cap D 16 σ (by omega)
  rw [vD, Nat.zero_add] at e1
  let st : ℕ → WState ns nr := fun k =>
    ((((σ.sets GU (List.replicate (k / 16) true)).seth GU (k / 16)).setv D (16 - k % 16)).setv RG (k / 16))
  have s0 : σ.setv D 16 = st 0 := by simp only [st]; wst
  rw [s0] at e1
  have e2 := forU_spec cap NU R (g16 GU D RG) N 80 st (fun k _ => by simp [st, Function.update_of_ne d1, hNU])
    (fun k _ => by simp [st, Function.update_of_ne d1, sNU])
    (fun k _ => by simp [st, Function.update_apply, q1, q2, vR])
    (fun k hk => by
      have e1 := WXExec.dec cap D (mv (st k) NU R k) (by simp [st, mv, Function.update_apply, q1.symm, q4]; omega)
      set τ := (mv (st k) NU R k).setv D ((mv (st k) NU R k).val D - 1) with hτ
      have hτD : τ.val D = 15 - k % 16 := by simp [hτ, st, mv, Function.update_apply, q1.symm, q4]; omega
      rcases Nat.lt_or_ge (k % 16) 15 with hlt | hge
      · have e2 : WXExec cap (.ifr D WMX.skip (.seq (WMX.wr GU true) (.seq (WMX.fwd GU) (.seq (WMX.inc RG)
            (incK D 16))))) τ τ 1 := WXExec.ifrT (by omega) (WXExec.skip cap τ)
        refine (WXExec.seq e1 e2).cast cap ?_ (by omega)
        have h1 : (k + 1) / 16 = k / 16 := by omega
        have h2 : 16 - (k + 1) % 16 = 15 - k % 16 := by omega
        simp only [hτ, st, mv, h1, h2]
        wst
      · have hk15 : k % 16 = 15 := by omega
        have h1 : (k + 1) / 16 = k / 16 + 1 := by omega
        have h2 : (k + 1) % 16 = 0 := by omega
        have w1 := WXExec.wr cap GU true τ
        have hw : writeTapeBit (τ.st GU) (τ.sh GU) true = List.replicate (k / 16 + 1) true := by
          simp only [hτ, st, mv, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
            WState.sets_sh, Function.update_self, Function.update_of_ne d1.symm]
          exact wtb_rep _ _
        rw [hw] at w1
        have w2 := WXExec.fwd cap GU (τ.sets GU (List.replicate (k / 16 + 1) true))
        set τ2 := (τ.sets GU (List.replicate (k / 16 + 1) true)).seth GU
          ((τ.sets GU (List.replicate (k / 16 + 1) true)).sh GU + 1) with hτ2
        have w3 := WXExec.inc cap RG τ2 (by simp [hτ2, hτ, st, mv, Function.update_apply, q2.symm, q4.symm]; omega)
        have w5 := incK_spec cap D 16 (τ2.setv RG (τ2.val RG + 1))
          (by simp [hτ2, Function.update_apply, q4, hτD]; omega)
        have e2 : WXExec cap (.ifr D WMX.skip (.seq (WMX.wr GU true) (.seq (WMX.fwd GU) (.seq (WMX.inc RG)
            (incK D 16))))) τ _ _ :=
          WXExec.ifrF (by omega) (WXExec.seq w1 (WXExec.seq w2 (WXExec.seq w3 w5)))
        refine (WXExec.seq e1 e2).cast cap ?_ (by omega)
        simp only [hτ2, hτ, st, mv, h1, h2]
        wst)
    (by omega)
  -- empty `D`, rewind `GU`
  set ρ := st N with hρ
  have l3 := loopR cap (r := D) (body := WMX.dec D) (fun j => ρ.setv D (16 - N % 16 - j)) (16 - N % 16) 1
    (fun j hj => by simp; omega) (by simp)
    (fun j hj => (WXExec.dec cap D (ρ.setv D (16 - N % 16 - j)) (by simp; omega)).cast cap (by wst) le_rfl)
  have r0 : ρ.setv D (16 - N % 16 - 0) = ρ := by simp only [hρ, st]; wst
  rw [r0] at l3
  have l4 := rew_spec cap GU RG (ρ.setv D (16 - N % 16 - (16 - N % 16))) (N / 16)
    (by simp [hρ, st, Function.update_apply, q4.symm]) (by omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq l3 l4))).cast cap ?_ (by omega)
  simp only [hρ, st]
  wst

/-! ## `MU := 1^M`, `M = foldl (2a+b) 1 code` -/

/-- The enumeration step of `machineIndex`. -/
def idx (acc : ℕ) (b : Bool) : ℕ := 2 * acc + if b then 1 else 0

theorem idx_le_foldl : ∀ (l : List Bool) (acc : ℕ), acc ≤ l.foldl idx acc
  | [], _ => le_rfl
  | b :: l, acc => le_trans (by unfold idx; omega) (idx_le_foldl l (idx acc b))

theorem foldl_take_le (l : List Bool) (k : ℕ) (acc : ℕ) : (l.take k).foldl idx acc ≤ l.foldl idx acc := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [List.foldl_append]
  exact idx_le_foldl _ _

def muP (CODE MU : Fin (ns + 1)) (R Ra Rb : Fin nr) : WMX ns nr :=
  .seq (WMX.wr MU true) (forP CODE R (.ifs CODE (dbl MU Ra Rb true) (dbl MU Ra Rb false)))

set_option maxHeartbeats 400000 in
theorem mu_spec (CODE MU : Fin (ns + 1)) (R Ra Rb : Fin nr) (d1 : CODE ≠ MU) (q1 : R ≠ Ra) (q2 : R ≠ Rb)
    (q3 : Ra ≠ Rb) (σ : WState ns nr) (code : List Bool) (hC : σ.st CODE = RepairOrdinary.frame code)
    (sC : σ.sh CODE = 0) (hMU : σ.st MU = []) (sMU : σ.sh MU = 0) (vR : σ.val R = 0) (va : σ.val Ra = 0)
    (vb : σ.val Rb = 0) (hcap : 2 * code.length + 2 * code.foldl idx 1 + 2 ≤ cap) :
    WXExec cap (muP CODE MU R Ra Rb) σ (σ.sets MU (List.replicate (code.foldl idx 1) true))
      (code.length * (40 * code.foldl idx 1 + 50) + 10) := by
  set m := code.foldl idx 1 with hm
  have e1 := WXExec.wr cap MU true σ
  rw [sMU, hMU] at e1
  have hw : writeTapeBit [] 0 true = List.replicate 1 true := rfl
  rw [hw] at e1
  let st : ℕ → WState ns nr := fun k => σ.sets MU (List.replicate ((code.take k).foldl idx 1) true)
  have s0 : σ.sets MU (List.replicate 1 true) = st 0 := by simp [st]
  rw [s0] at e1
  have e2 := forP_spec cap CODE R (.ifs CODE (dbl MU Ra Rb true) (dbl MU Ra Rb false)) code [false] (40 * m + 21) st
    (fun k _ => by simp [st, Function.update_of_ne d1, hC, frame_eq_fpre])
    (fun k _ => by simp [st, sC]) (fun k _ => by simp [st, vR]) (by simp [readTapeBit])
    (fun k hk => by
      set u := (code.take k).foldl idx 1 with hu
      have hum : u ≤ m := foldl_take_le code k 1
      have hb : wbit (mv2 (st k) CODE R (2 * k + 1) (2 * k)) CODE = code[k] := by
        simp only [wbit, mv2, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          WState.sets_sh, Function.update_self, Function.update_of_ne d1, hC, frame_eq_fpre]
        exact (rd_fpre code [false] k hk).2
      have hnext : (code.take (k + 1)).foldl idx 1 = 2 * u + code[k].toNat := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, idx, ← hu]
        cases code[k] <;> simp
      have hdbl : ∀ b : Bool, WXExec cap (dbl MU Ra Rb b) (mv2 (st k) CODE R (2 * k + 1) (2 * k))
          ((mv2 (st k) CODE R (2 * k + 1) (2 * k)).sets MU (List.replicate (2 * u + b.toNat) true)) (40 * u + 20) :=
        fun b => dbl_spec cap MU Ra Rb q3 b _ u (by simp [mv2, st, hu])
          (by simp [mv2, st, Function.update_of_ne d1.symm, sMU]) (by simp [mv2, st, Function.update_apply, q1, q1.symm, va])
          (by simp [mv2, st, Function.update_apply, q2, q2.symm, vb]) (by omega)
      have e : WXExec cap (.ifs CODE (dbl MU Ra Rb true) (dbl MU Ra Rb false))
          (mv2 (st k) CODE R (2 * k + 1) (2 * k))
          ((mv2 (st k) CODE R (2 * k + 1) (2 * k)).sets MU (List.replicate (2 * u + code[k].toNat) true))
          (40 * u + 21) := by
        cases hc : code[k]
        · rw [hc] at hb; exact WXExec.ifsF hb (hdbl false)
        · rw [hc] at hb; exact WXExec.ifsT hb (hdbl true)
      refine e.cast cap ?_ (by omega)
      simp only [st, mv2, hnext]
      wst)
    (by omega)
  refine (WXExec.seq e1 e2).cast cap ?_ (by nlinarith)
  simp only [st, List.take_length]
  wst

/-! ## Walking two streams in lockstep -/

/-- Walk `A = 1^a` to its end, moving `B` along; counters `RA`, `RB`. -/
def lock (A B : Fin (ns + 1)) (RA RB : Fin nr) : WMX ns nr :=
  .whs A (.seq (WMX.fwd A) (.seq (WMX.fwd B) (.seq (WMX.inc RA) (WMX.inc RB))))

theorem lock_spec (A B : Fin (ns + 1)) (RA RB : Fin nr) (d : A ≠ B) (q : RA ≠ RB) (σ : WState ns nr) (a h0 : ℕ)
    (hA : σ.st A = List.replicate a true) (sA : σ.sh A = 0) (vA : σ.val RA = 0) (sB : σ.sh B = h0)
    (vB : σ.val RB = h0) (hcap : h0 + a ≤ cap) :
    WXExec cap (lock A B RA RB) σ ((((σ.seth A a).seth B (h0 + a)).setv RA a).setv RB (h0 + a)) (13 * a + 1) := by
  let st : ℕ → WState ns nr := fun k => (((σ.seth A k).seth B (h0 + k)).setv RA k).setv RB (h0 + k)
  have l := loopS cap (i := A) (body := .seq (WMX.fwd A) (.seq (WMX.fwd B) (.seq (WMX.inc RA) (WMX.inc RB)))) st a 11
    (fun k hk => by simp only [wbit, st, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
      Function.update_of_ne d, Function.update_self, hA]; exact rdr a true hk)
    (by simp only [wbit, st, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
      Function.update_of_ne d, Function.update_self, hA]; exact rdr_end a true le_rfl)
    (fun k hk => by
      have e1 := WXExec.fwd cap A (st k)
      have e2 := WXExec.fwd cap B ((st k).seth A ((st k).sh A + 1))
      have e3 := WXExec.inc cap RA (((st k).seth A ((st k).sh A + 1)).seth B (((st k).seth A ((st k).sh A + 1)).sh B + 1))
        (by simp [st, Function.update_apply, q, q.symm]; omega)
      have e4 := WXExec.inc cap RB ((((st k).seth A ((st k).sh A + 1)).seth B (((st k).seth A ((st k).sh A + 1)).sh B + 1)).setv
        RA ((((st k).seth A ((st k).sh A + 1)).seth B (((st k).seth A ((st k).sh A + 1)).sh B + 1)).val RA + 1))
        (by simp [st, Function.update_apply, q, q.symm]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
      simp only [st]; wst)
  have s0 : st 0 = σ := by simp only [st]; wst
  rw [s0] at l
  exact l.mono (by omega)

/-! ## `XU := 1^{N−g−M−2}` -/

/-- Skip `g + M + 2` cells of `NU` (walking `GU = 1^g` and `MU = 1^M`). -/
def xuSkip (GU MU NU : Fin (ns + 1)) (RA RB RN : Fin nr) : WMX ns nr :=
  .seq (lock GU NU RA RN) (.seq (lock MU NU RB RN) (.seq (WMX.fwd NU) (.seq (WMX.inc RN) (.seq (WMX.fwd NU)
    (WMX.inc RN)))))

/-- Copy the rest of `NU` onto `XU`. -/
def xuLoop (NU XU : Fin (ns + 1)) (RN RX : Fin nr) : WMX ns nr :=
  .whs NU (.seq (WMX.fwd NU) (.seq (WMX.inc RN) (wb XU RX true)))

def xuRew (GU MU NU XU : Fin (ns + 1)) (RA RB RN RX : Fin nr) : WMX ns nr :=
  .seq (rew GU RA) (.seq (rew MU RB) (.seq (rew NU RN) (rew XU RX)))

def xuP (GU MU NU XU : Fin (ns + 1)) (RA RB RN RX : Fin nr) : WMX ns nr :=
  .seq (xuSkip GU MU NU RA RB RN) (.seq (xuLoop NU XU RN RX) (xuRew GU MU NU XU RA RB RN RX))

theorem fwdinc2 (X : Fin (ns + 1)) (R : Fin nr) (σ : WState ns nr) (hv : σ.val R + 2 ≤ cap) :
    WXExec cap (.seq (WMX.fwd X) (.seq (WMX.inc R) (.seq (WMX.fwd X) (WMX.inc R)))) σ
      ((σ.seth X (σ.sh X + 2)).setv R (σ.val R + 2)) 11 := by
  have e1 := WXExec.fwd cap X σ
  have e2 := WXExec.inc cap R (σ.seth X (σ.sh X + 1)) (by simp; omega)
  have e3 := WXExec.fwd cap X ((σ.seth X (σ.sh X + 1)).setv R ((σ.seth X (σ.sh X + 1)).val R + 1))
  have e4 := WXExec.inc cap R (((σ.seth X (σ.sh X + 1)).setv R ((σ.seth X (σ.sh X + 1)).val R + 1)).seth X
    (((σ.seth X (σ.sh X + 1)).setv R ((σ.seth X (σ.sh X + 1)).val R + 1)).sh X + 1)) (by simp; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
  clear e1 e2 e3 e4
  wst

theorem xuSkip_spec (GU MU NU : Fin (ns + 1)) (RA RB RN : Fin nr) (d1 : GU ≠ MU) (d2 : GU ≠ NU) (d4 : MU ≠ NU)
    (q1 : RA ≠ RB) (q2 : RA ≠ RN) (q4 : RB ≠ RN) (σ : WState ns nr) (g m : ℕ)
    (hGU : σ.st GU = List.replicate g true) (hMU : σ.st MU = List.replicate m true) (sGU : σ.sh GU = 0)
    (sMU : σ.sh MU = 0) (sNU : σ.sh NU = 0) (vA : σ.val RA = 0) (vB : σ.val RB = 0) (vN : σ.val RN = 0)
    (hcap : g + m + 2 ≤ cap) :
    WXExec cap (xuSkip GU MU NU RA RB RN) σ
      ((((((σ.seth GU g).seth MU m).seth NU (g + m + 2)).setv RA g).setv RB m).setv RN (g + m + 2))
      (13 * (g + m) + 20) := by
  have e1 := lock_spec cap GU NU RA RN d2 q2 σ g 0 hGU sGU vA sNU vN (by omega)
  have e2 := lock_spec cap MU NU RB RN d4 q4 ((((σ.seth GU g).seth NU (0 + g)).setv RA g).setv RN (0 + g)) m (0 + g)
    (by simp [hMU]) (by simp [Function.update_apply, d1, d1.symm, d4, d4.symm, sMU])
    (by simp [Function.update_apply, q1, q1.symm, q4, q4.symm, vB]) (by simp) (by simp) (by omega)
  have e3 := fwdinc2 cap NU RN ((((((((σ.seth GU g).seth NU (0 + g)).setv RA g).setv RN (0 + g)).seth MU m).seth NU
    (0 + g + m)).setv RB m).setv RN (0 + g + m)) (by simp; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
  clear e1 e2 e3
  wst

theorem xuLoop_spec (NU XU : Fin (ns + 1)) (RN RX : Fin nr) (d6 : NU ≠ XU) (q6 : RN ≠ RX) (σ : WState ns nr)
    (N h0 : ℕ) (hh : h0 ≤ N) (hNU : σ.st NU = List.replicate N true) (sNU : σ.sh NU = h0) (vN : σ.val RN = h0)
    (hXU : σ.st XU = []) (sXU : σ.sh XU = 0) (vX : σ.val RX = 0) (hcap : N + 1 ≤ cap) :
    WXExec cap (xuLoop NU XU RN RX) σ
      (((((σ.seth NU N).setv RN N).sets XU (List.replicate (N - h0) true)).seth XU (N - h0)).setv RX (N - h0))
      (15 * (N - h0) + 1) := by
  let st : ℕ → WState ns nr := fun k =>
    ((((σ.seth NU (h0 + k)).setv RN (h0 + k)).sets XU (List.replicate k true)).seth XU k).setv RX k
  have e := loopS cap (i := NU) (body := .seq (WMX.fwd NU) (.seq (WMX.inc RN) (wb XU RX true))) st (N - h0) 13
    (fun k hk => by
      simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        WState.sets_sh, Function.update_of_ne d6.symm, Function.update_of_ne d6, Function.update_self, hNU]
      exact rdr N true (by omega))
    (by
      simp only [wbit, st, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        WState.sets_sh, Function.update_of_ne d6.symm, Function.update_of_ne d6, Function.update_self, hNU]
      exact rdr_end N true (by omega))
    (fun k hk => by
      have f1 := WXExec.fwd cap NU (st k)
      have f2 := WXExec.inc cap RN ((st k).seth NU ((st k).sh NU + 1))
        (by simp [st, Function.update_apply, q6, q6.symm]; omega)
      have f3 := wb_act cap XU RX true (((st k).seth NU ((st k).sh NU + 1)).setv RN
        (((st k).seth NU ((st k).sh NU + 1)).val RN + 1))
        (by simp [st, Function.update_of_ne d6.symm])
        (by simp [st, Function.update_apply, q6, q6.symm]; omega)
      refine (WXExec.seq f1 (WXExec.seq f2 f3)).cast cap ?_ (by omega)
      simp only [st]; unfold app
      have hl : List.replicate k true ++ [true] = List.replicate (k + 1) true := by rw [← List.replicate_succ']
      simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, hl]
      wst)
  have s0 : st 0 = σ := by simp only [st]; wst
  rw [s0] at e
  refine e.cast cap ?_ (by omega)
  simp only [st, show h0 + (N - h0) = N by omega]

set_option maxHeartbeats 400000 in
theorem xu_spec (GU MU NU XU : Fin (ns + 1)) (RA RB RN RX : Fin nr) (d1 : GU ≠ MU) (d2 : GU ≠ NU) (d3 : GU ≠ XU)
    (d4 : MU ≠ NU) (d5 : MU ≠ XU) (d6 : NU ≠ XU) (q1 : RA ≠ RB) (q2 : RA ≠ RN) (q3 : RA ≠ RX) (q4 : RB ≠ RN)
    (q5 : RB ≠ RX) (q6 : RN ≠ RX) (σ : WState ns nr) (g m N : ℕ) (hgm : g + m + 2 ≤ N)
    (hGU : σ.st GU = List.replicate g true) (hMU : σ.st MU = List.replicate m true)
    (hNU : σ.st NU = List.replicate N true) (hXU : σ.st XU = []) (sGU : σ.sh GU = 0) (sMU : σ.sh MU = 0)
    (sNU : σ.sh NU = 0) (sXU : σ.sh XU = 0) (vA : σ.val RA = 0) (vB : σ.val RB = 0) (vN : σ.val RN = 0)
    (vX : σ.val RX = 0) (hcap : 2 * N + 2 ≤ cap) :
    WXExec cap (xuP GU MU NU XU RA RB RN RX) σ (σ.sets XU (List.replicate (N - g - m - 2) true)) (60 * (N + 1)) := by
  have e1 := xuSkip_spec cap GU MU NU RA RB RN d1 d2 d4 q1 q2 q4 σ g m hGU hMU sGU sMU sNU vA vB vN (by omega)
  have e2 := xuLoop_spec cap NU XU RN RX d6 q6
    ((((((σ.seth GU g).seth MU m).seth NU (g + m + 2)).setv RA g).setv RB m).setv RN (g + m + 2)) N (g + m + 2) hgm
    (by simp [hNU]) (by simp) (by simp) (by simp [Function.update_apply, d3, d5, d6, d3.symm, d5.symm, d6.symm, hXU])
    (by simp [Function.update_apply, d3, d5, d6, d3.symm, d5.symm, d6.symm, sXU])
    (by simp [Function.update_apply, q3, q5, q6, q3.symm, q5.symm, q6.symm, vX]) (by omega)
  set ρ := ((((((((((σ.seth GU g).seth MU m).seth NU (g + m + 2)).setv RA g).setv RB m).setv RN (g + m + 2)).seth NU
    N).setv RN N).sets XU (List.replicate (N - (g + m + 2)) true)).seth XU (N - (g + m + 2))).setv RX
    (N - (g + m + 2)) with hρ
  have r1 := rew_spec cap GU RA ρ g (by simp [hρ, Function.update_apply, q1, q2, q3, q1.symm, q2.symm, q3.symm])
    (by omega)
  have r2 := rew_spec cap MU RB ((ρ.setv RA 0).seth GU (ρ.sh GU - g)) m
    (by simp [hρ, Function.update_apply, q1, q4, q5, q1.symm, q4.symm, q5.symm]) (by omega)
  have r3 := rew_spec cap NU RN ((((ρ.setv RA 0).seth GU (ρ.sh GU - g)).setv RB 0).seth MU
    (((ρ.setv RA 0).seth GU (ρ.sh GU - g)).sh MU - m)) N
    (by simp [hρ, Function.update_apply, q2, q4, q6, q2.symm, q4.symm, q6.symm]) (by omega)
  have r4 := rew_spec cap XU RX ((((((ρ.setv RA 0).seth GU (ρ.sh GU - g)).setv RB 0).seth MU
    (((ρ.setv RA 0).seth GU (ρ.sh GU - g)).sh MU - m)).setv RN 0).seth NU ((((((ρ.setv RA 0).seth GU
    (ρ.sh GU - g)).setv RB 0).seth MU (((ρ.setv RA 0).seth GU (ρ.sh GU - g)).sh MU - m))).sh NU - N)) (N - (g + m + 2))
    (by simp [hρ, Function.update_apply, q3, q5, q6, q3.symm, q5.symm, q6.symm]) (by omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq r1 (WXExec.seq r2 (WXExec.seq r3 r4))))).cast cap ?_ (by omega)
  clear e1 e2 r1 r2 r3 r4
  rw [hρ, show N - (g + m + 2) = N - g - m - 2 by omega]
  clear hρ
  wst

end NearCubicGates.Adapters.Refuter.RM
