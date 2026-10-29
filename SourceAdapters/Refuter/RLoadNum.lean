import SourceAdapters.Refuter.RLoadUnary
import SourceAdapters.Refuter.RMachArith

/-!
# R's loader, part 3: the stored numbers and the flags (input 7, R: INIT)

Paper anchor: (`lem:multitape-refuter` Step 4: R's binary searches over `[0, 2^g)` and the
least-hit search start from the empty interval, phase "nothing asked"); (the endpoints are written
in binary). R keeps `g+2`-bit numbers (`num (g+2) v = fr(binary (g+2) v)`, least significant bit first): the
constants `0`, `1`, `2^g`, `g+1` and the search state `lo = hi = fuel = 0`.

* `zeroNum`: `X := num (g+2) 0` from `GU = 1^g` (`zeroNum_spec`);
* `setBit`: write the data cell of bit `j` of a stored number (`num (g+2) 1`, `num (g+2) (2^g)`);
* `ffP`: `FF := num (g+2) (g+1)` by `g+1` binary additions of `ONE` (L's `BinW.add`, one per cell of `GU`);
* the phase flags `P0 = 1` (fresh), all other flags `0`.
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Refuter
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section Generic
variable {ns nr : ℕ} (cap : ℕ)

/-! ## Numbers as lists -/

theorem fpre_replicate_add (g : ℕ) :
    fpre (List.replicate (g + 2) false) = fpre (List.replicate g false) ++ [true, false] ++ [true, false] := by
  rw [List.replicate_succ', List.replicate_succ', fpre_append, fpre_append]
  rfl

theorem wtb_fpre : ∀ (l rest : List Bool) (j : ℕ), j < l.length → ∀ b : Bool,
    writeTapeBit (fpre l ++ rest) (2 * j + 1) b = fpre (l.set j b) ++ rest
  | [], _, _, h, _ => by simp at h
  | a :: l, rest, 0, _, b => by simp [fpre, writeTapeBit]
  | a :: l, rest, j + 1, h, b => by
    have ih := wtb_fpre l rest j (by simp at h; omega) b
    simp only [fpre, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring]
    simp only [writeTapeBit, List.set_cons_succ, List.flatMap_cons, List.cons_append, List.nil_append, ih]

theorem num_zero (W : ℕ) : num W 0 = RepairOrdinary.frame (List.replicate W false) := by
  simp [num, binary_zero]

theorem binary_one (k : ℕ) : binary (k + 1) 1 = (List.replicate (k + 1) false).set 0 true := by
  simp [binary, binary_zero, List.replicate_succ]

theorem binary_two_pow (g : ℕ) : binary (g + 2) (2 ^ g) = (List.replicate (g + 2) false).set g true := by
  induction g with
  | zero => simp [binary, binary_zero, List.replicate_succ]
  | succ g ih =>
    have h1 : (2 ^ (g + 1)) % 2 = 0 := by simp [pow_succ]
    have h2 : 2 ^ (g + 1) / 2 = 2 ^ g := by rw [pow_succ]; simp
    have h : binary (g + 1 + 2) (2 ^ (g + 1)) = false :: binary (g + 2) (2 ^ g) := by
      show (2 ^ (g + 1) % 2 == 1) :: binary (g + 2) (2 ^ (g + 1) / 2) = _
      rw [h1, h2]; rfl
    rw [h, ih, show g + 1 + 2 = (g + 2) + 1 by ring]
    conv_rhs => rw [List.replicate_succ]
    rw [List.set_cons_succ]

/-! ## `X := num (g+2) 0` -/

/-- `X := fr(0^{g+2})` from `GU = 1^g`. -/
def zeroNum (GU X : Fin (ns + 1)) (R RX : Fin nr) : WMX ns nr :=
  .seq (forU GU R (em1 X RX false)) (.seq (em1 X RX false) (.seq (em1 X RX false) (.seq (WMX.wr X false) (rew X RX))))

theorem zeroNum_spec (GU X : Fin (ns + 1)) (R RX : Fin nr) (d : GU ≠ X) (q : R ≠ RX) (σ : WState ns nr) (g : ℕ)
    (hGU : σ.st GU = List.replicate g true) (sGU : σ.sh GU = 0) (hX : σ.st X = []) (sX : σ.sh X = 0)
    (vR : σ.val R = 0) (vX : σ.val RX = 0) (hcap : 2 * g + 8 ≤ cap) :
    WXExec cap (zeroNum GU X R RX) σ (σ.sets X (num (g + 2) 0)) (50 * (g + 2)) := by
  have e1 := forU_act cap (em1_act cap X RX) false GU R d q σ g hGU sGU vR (by rw [sX, hX]; rfl)
    (by simp [vX]; omega) (by omega)
  have hfp : ((List.replicate g false).flatMap fun b => [true, b]) = fpre (List.replicate g false) := rfl
  rw [hfp] at e1
  have e2 := em1_act cap X RX false (app σ X RX (fpre (List.replicate g false))) (by simp [sX, hX])
    (by simp [vX]; omega)
  rw [app_app] at e2
  have e3 := em1_act cap X RX false (app σ X RX (fpre (List.replicate g false) ++ [true, false]))
    (by simp [sX, hX]) (by simp [vX]; omega)
  rw [app_app] at e3
  set A := fpre (List.replicate g false) ++ [true, false] ++ [true, false] with hA
  have hAl : A.length = 2 * (g + 2) := by rw [hA, ← fpre_replicate_add, fpre_length]; simp
  have e4 := WXExec.wr cap X false (app σ X RX A)
  have w : writeTapeBit ((app σ X RX A).st X) ((app σ X RX A).sh X) false = num (g + 2) 0 := by
    simp only [app_st_D, app_sh_D, hX, sX, List.nil_append, Nat.zero_add]
    rw [wtb_append, num_zero, frame_eq_fpre, hA, fpre_replicate_add]
  rw [w] at e4
  have e5 := rew_spec cap X RX ((app σ X RX A).sets X (num (g + 2) 0)) A.length (by simp [vX]) (by omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ (by omega)
  clear e1 e2 e3 e4 e5 w
  unfold app
  wst

/-! ## Setting one bit of a stored number -/

/-- Set bit `0` (the data cell `1`). -/
def bit0P (X : Fin (ns + 1)) : WMX ns nr := .seq (WMX.fwd X) (.seq (WMX.wr X true) (WMX.bwd X))

theorem bit0_spec (X : Fin (ns + 1)) (σ : WState ns nr) (g : ℕ) (hX : σ.st X = num (g + 2) 0) (sX : σ.sh X = 0) :
    WXExec cap (bit0P X) σ (σ.sets X (num (g + 2) 1)) 5 := by
  have e1 := WXExec.fwd cap X σ
  have e2 := WXExec.wr cap X true (σ.seth X (σ.sh X + 1))
  have w : writeTapeBit ((σ.seth X (σ.sh X + 1)).st X) ((σ.seth X (σ.sh X + 1)).sh X) true = num (g + 2) 1 := by
    have h1 : num (g + 2) 1 = fpre ((List.replicate (g + 2) false).set 0 true) ++ [false] := by
      show RepairOrdinary.frame (binary (g + 1 + 1) 1) = _
      rw [binary_one, frame_eq_fpre]
    rw [h1]
    simp only [WState.seth_st, WState.seth_sh, Function.update_self, hX, sX, num, binary_zero, frame_eq_fpre]
    exact wtb_fpre (List.replicate (g + 2) false) [false] 0 (by simp) true
  rw [w] at e2
  have e3 := WXExec.bwd cap X ((σ.seth X (σ.sh X + 1)).sets X (num (g + 2) 1))
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
  clear e1 e2 e3 w
  wst

/-- Set bit `g` (the data cell `2g+1`): walk `GU = 1^g` twice along `X`. -/
def bitGP (GU X : Fin (ns + 1)) (RA RS : Fin nr) : WMX ns nr :=
  .seq (lock GU X RA RS) (.seq (rew GU RA) (.seq (lock GU X RA RS) (.seq (rew GU RA)
    (.seq (WMX.fwd X) (.seq (WMX.inc RS) (.seq (WMX.wr X true) (rew X RS)))))))

set_option maxHeartbeats 400000 in
theorem bitG_spec (GU X : Fin (ns + 1)) (RA RS : Fin nr) (d : GU ≠ X) (q : RA ≠ RS) (σ : WState ns nr) (g : ℕ)
    (hGU : σ.st GU = List.replicate g true) (sGU : σ.sh GU = 0) (hX : σ.st X = num (g + 2) 0) (sX : σ.sh X = 0)
    (vA : σ.val RA = 0) (vS : σ.val RS = 0) (hcap : 2 * g + 4 ≤ cap) :
    WXExec cap (bitGP GU X RA RS) σ (σ.sets X (num (g + 2) (2 ^ g))) (60 * (g + 1)) := by
  have e1 := lock_spec cap GU X RA RS d q σ g 0 hGU sGU vA sX vS (by omega)
  have e2 := rew_spec cap GU RA ((((σ.seth GU g).seth X (0 + g)).setv RA g).setv RS (0 + g)) g
    (by simp [Function.update_apply, q, q.symm]) (by omega)
  have e3 := lock_spec cap GU X RA RS d q (((((((σ.seth GU g).seth X (0 + g)).setv RA g).setv RS (0 + g)).setv RA 0).seth
    GU (((((σ.seth GU g).seth X (0 + g)).setv RA g).setv RS (0 + g)).sh GU - g))) g (0 + g) (by simp [hGU])
    (by simp [Function.update_apply, d, d.symm]) (by simp) (by simp [Function.update_apply, d, d.symm]) (by simp [Function.update_apply, q, q.symm])
    (by omega)
  set τ := (((((((((((σ.seth GU g).seth X (0 + g)).setv RA g).setv RS (0 + g)).setv RA 0).seth
    GU (((((σ.seth GU g).seth X (0 + g)).setv RA g).setv RS (0 + g)).sh GU - g))).seth GU g).seth X (0 + g + g)).setv
    RA g).setv RS (0 + g + g)) with hτ
  have e4 := rew_spec cap GU RA τ g (by simp [hτ, Function.update_apply, q, q.symm]) (by omega)
  set τ4 := (τ.setv RA 0).seth GU (τ.sh GU - g) with hτ4
  have e5 := WXExec.fwd cap X τ4
  have e6 := WXExec.inc cap RS (τ4.seth X (τ4.sh X + 1)) (by simp [hτ4, hτ, Function.update_apply, q, q.symm]; omega)
  set τ6 := (τ4.seth X (τ4.sh X + 1)).setv RS ((τ4.seth X (τ4.sh X + 1)).val RS + 1) with hτ6
  have e7 := WXExec.wr cap X true τ6
  have w : writeTapeBit (τ6.st X) (τ6.sh X) true = num (g + 2) (2 ^ g) := by
    have h1 : τ6.st X = num (g + 2) 0 := by simp [hτ6, hτ4, hτ, hX]
    have h2 : τ6.sh X = 2 * g + 1 := by simp [hτ6, hτ4, hτ, Function.update_apply, d, d.symm]; omega
    have h3 : num (g + 2) (2 ^ g) = fpre ((List.replicate (g + 2) false).set g true) ++ [false] := by
      show RepairOrdinary.frame (binary (g + 2) (2 ^ g)) = _
      rw [binary_two_pow, frame_eq_fpre]
    rw [h1, h2, num_zero, frame_eq_fpre, wtb_fpre (List.replicate (g + 2) false) [false] g (by simp) true, h3]
  rw [w] at e7
  have e8 := rew_spec cap X RS (τ6.sets X (num (g + 2) (2 ^ g))) (2 * g + 1)
    (by simp [hτ6, hτ4, hτ, Function.update_apply, q, q.symm]; omega) (by omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq e7
    e8))))))).cast cap ?_ (by omega)
  clear e1 e2 e3 e4 e5 e6 e7 e8 w
  have h2 : τ6.sh X = 2 * g + 1 := by simp [hτ6, hτ4, hτ, Function.update_apply, d, d.symm]; omega
  rw [hτ6] at h2 ⊢
  rw [hτ4] at h2 ⊢
  rw [hτ] at h2 ⊢
  wst

/-! ## `FF := num (g+2) (g+1)` -/

/-- `g + 1` binary additions of `ONE` (one per cell of `GU`, then one more). -/
def ffP (GU FF ONE : Fin (ns + 1)) (R F Rr : Fin nr) : WMX ns nr :=
  .seq (forU GU R (BinW.add FF ONE F Rr)) (BinW.add FF ONE F Rr)

theorem ff_spec (GU FF ONE : Fin (ns + 1)) (R F Rr : Fin nr) (d1 : GU ≠ FF) (d2 : GU ≠ ONE) (d3 : FF ≠ ONE)
    (q1 : R ≠ F) (q2 : R ≠ Rr) (q3 : F ≠ Rr) (σ : WState ns nr) (g : ℕ) (hGU : σ.st GU = List.replicate g true)
    (sGU : σ.sh GU = 0) (hFF : σ.st FF = num (g + 2) 0) (sFF : σ.sh FF = 0) (hONE : σ.st ONE = num (g + 2) 1)
    (sONE : σ.sh ONE = 0) (vR : σ.val R = 0) (vF : σ.val F = 0) (vRr : σ.val Rr = 0) (hcap : 2 * g + 5 ≤ cap) :
    WXExec cap (ffP GU FF ONE R F Rr) σ (σ.sets FF (num (g + 2) (g + 1))) ((g + 1) * (41 * (g + 2) + 20)) := by
  have hpow : g + 1 < 2 ^ (g + 2) := (pow_facts g).1
  let st : ℕ → WState ns nr := fun k => σ.sets FF (num (g + 2) k)
  have e1 := forU_spec cap GU R (BinW.add FF ONE F Rr) g (41 * (g + 2) + 3) st
    (fun k _ => by simp [st, Function.update_of_ne d1, hGU]) (fun k _ => by simp [st, sGU])
    (fun k _ => by simp [st, vR])
    (fun k hk => by
      have e := BinW.add_spec cap (g + 2) d3 q3 (mv (st k) GU R k) k 1
        ⟨by simp [st, mv], by simp [st, mv, Function.update_of_ne d1.symm, sFF]⟩
        ⟨by simp [st, mv, Function.update_of_ne d3.symm, hONE], by simp [st, mv, Function.update_of_ne d2.symm, sONE]⟩
        (by simp [st, mv, Function.update_of_ne q1.symm, vF]) (by simp [st, mv, Function.update_of_ne q2.symm, vRr])
        (by omega) (by omega)
      refine e.cast cap ?_ le_rfl
      clear e
      simp only [st, mv]; wst)
    (by omega)
  have s0 : st 0 = σ := by simp only [st, ← hFF]; wst
  rw [s0] at e1
  have e2 := BinW.add_spec cap (g + 2) d3 q3 (st g) g 1 ⟨by simp [st], by simp [st, sFF]⟩
    ⟨by simp [st, Function.update_of_ne d3.symm, hONE], by simp [st, sONE]⟩ (by simp [st, vF]) (by simp [st, vRr])
    (by omega) (by omega)
  refine (WXExec.seq e1 e2).cast cap ?_ (by nlinarith)
  clear e1 e2
  simp only [st]; wst

/-! ## Several streams at once -/

/-- Set several streams. -/
def setsL (σ : WState ns nr) : List (Fin (ns + 1) × List Bool) → WState ns nr
  | [] => σ
  | p :: L => setsL (σ.sets p.1 p.2) L

@[simp] theorem setsL_nil (σ : WState ns nr) : setsL σ [] = σ := rfl
@[simp] theorem setsL_cons (σ : WState ns nr) (p : Fin (ns + 1) × List Bool) (L : List (Fin (ns + 1) × List Bool)) :
    setsL σ (p :: L) = setsL (σ.sets p.1 p.2) L := rfl

theorem setsL_sh (σ : WState ns nr) : ∀ L, (setsL σ L).sh = σ.sh
  | [] => rfl
  | p :: L => (setsL_sh (σ.sets p.1 p.2) L).trans rfl

theorem setsL_val (σ : WState ns nr) : ∀ L, (setsL σ L).val = σ.val
  | [] => rfl
  | p :: L => (setsL_val (σ.sets p.1 p.2) L).trans rfl

theorem setsL_cell (σ : WState ns nr) : ∀ L, (setsL σ L).cell = σ.cell
  | [] => rfl
  | p :: L => (setsL_cell (σ.sets p.1 p.2) L).trans rfl

theorem setsL_other (σ : WState ns nr) : ∀ (L : List (Fin (ns + 1) × List Bool)) (Y : Fin (ns + 1)),
    Y ∉ L.map Prod.fst → (setsL σ L).st Y = σ.st Y
  | [], _, _ => rfl
  | p :: L, Y, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [setsL_cons, setsL_other _ L Y h.2]
    simp [Function.update_of_ne h.1]

/-- Write one bit on each listed (empty) stream. -/
def wrs : List (Fin (ns + 1) × Bool) → WMX ns nr
  | [] => WMX.skip
  | p :: L => .seq (WMX.wr p.1 p.2) (wrs L)

theorem wrs_spec : ∀ (L : List (Fin (ns + 1) × Bool)) (σ : WState ns nr), (L.map Prod.fst).Nodup →
    (∀ p ∈ L, σ.st p.1 = [] ∧ σ.sh p.1 = 0) →
    WXExec cap (wrs L) σ (setsL σ (L.map fun p => (p.1, [p.2]))) (2 * L.length)
  | [], σ, _, _ => (WXExec.skip cap σ).mono (by simp)
  | p :: L, σ, hnd, hpre => by
    have e1 := WXExec.wr cap p.1 p.2 σ
    rw [(hpre p (by simp)).1, (hpre p (by simp)).2] at e1
    simp only [List.map_cons, List.nodup_cons] at hnd
    have e2 := wrs_spec L (σ.sets p.1 [p.2]) hnd.2 (fun q hq => by
      have hne : q.1 ≠ p.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hq)
      simp [Function.update_of_ne hne, hpre q (by simp [hq])])
    exact (WXExec.seq e1 e2).mono (by simp; omega)

/-- `num (g+2) 0` on each listed (empty) stream. -/
def zerosP (GU : Fin (ns + 1)) (R RX : Fin nr) : List (Fin (ns + 1)) → WMX ns nr
  | [] => WMX.skip
  | X :: L => .seq (zeroNum GU X R RX) (zerosP GU R RX L)

theorem zeros_spec (GU : Fin (ns + 1)) (R RX : Fin nr) (q : R ≠ RX) (g : ℕ) (hcap : 2 * g + 8 ≤ cap) :
    ∀ (L : List (Fin (ns + 1))) (σ : WState ns nr), L.Nodup → GU ∉ L →
    σ.st GU = List.replicate g true → σ.sh GU = 0 → σ.val R = 0 → σ.val RX = 0 →
    (∀ X ∈ L, σ.st X = [] ∧ σ.sh X = 0) →
    WXExec cap (zerosP GU R RX L) σ (setsL σ (L.map fun X => (X, num (g + 2) 0))) (L.length * (50 * (g + 2) + 1))
  | [], σ, _, _, _, _, _, _, _ => (WXExec.skip cap σ).mono (by simp)
  | X :: L, σ, hnd, hG, hGU, sGU, vR, vX, hpre => by
    simp only [List.nodup_cons] at hnd
    have hGX : GU ≠ X := fun h => hG (by simp [h])
    have e1 := zeroNum_spec cap GU X R RX hGX q σ g hGU sGU (hpre X (by simp)).1 (hpre X (by simp)).2 vR vX hcap
    have e2 := zeros_spec GU R RX q g hcap L (σ.sets X (num (g + 2) 0)) hnd.2 (fun h => hG (by simp [h]))
      (by simp [Function.update_of_ne hGX, hGU]) (by simp [sGU]) (by simp [vR]) (by simp [vX])
      (fun Y hY => by
        have hne : Y ≠ X := fun h => hnd.1 (h ▸ hY)
        simp [Function.update_of_ne hne, hpre Y (by simp [hY])])
    exact (WXExec.seq e1 e2).mono (by simp; nlinarith)

end Generic

/-! ## The flags (R's layout) -/

section Layout
variable {tc tT : ℕ} (cap : ℕ)

local notation "WS" => WState (NS tc tT) NR

/-- The flags of the fresh state: `P0 = 1`, `P1 = P3 = ELO = 0`, `DONE = ANS = FIN = 0`. -/
def flagList : List (Fin (NS tc tT + 1) × Bool) :=
  [(sP0, true), (sP1, false), (sP3, false), (sELO, false), (sDONE, false), (sANS, false), (sFIN, false)]

def flagsP : WMX (NS tc tT) NR := wrs (flagList (tc := tc) (tT := tT))

theorem flagList_nodup : ((flagList (tc := tc) (tT := tT)).map Prod.fst).Nodup := by
  simp [flagList, sP0, sP1, sP3, sELO, sDONE, sANS, sFIN, Fin.ext_iff]

end Layout

end NearCubicGates.Adapters.Refuter.RM
