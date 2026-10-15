import Proof.Gates.CounterMachine.TabCallCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.Codec

variable {ns nr : ℕ} (cap : ℕ)

section Log
variable (G : Fin 6 ↪ Fin nr)

/-- `A := 2A` (`G 0` the accumulator, `G 1`, `G 2` scratch). -/
def dblP : WM ns nr := .seq (copyR (G 0) (G 1) (G 2)) (WM.move (G 1) (G 0))

/-- `A := A·(n+1)` (`G 4` holds `n + 1`). -/
def mulP : WM ns nr := .seq (mulR (G 4) (G 0) (G 1) (G 2)) (WM.move (G 1) (G 0))

def powP : ℕ → WM ns nr
  | 0 => .skip
  | e + 1 => .seq (powP e) (mulP G)

theorem hG {a b : Fin 6} (h : a ≠ b) : G a ≠ G b := G.injective.ne h

theorem dbl_spec (σ : WState ns nr) (a : ℕ) (hA : σ.val (G 0) = a) (h1 : σ.val (G 1) = 0) (h2 : σ.val (G 2) = 0)
    (hc : 2 * a ≤ cap) : WExec cap (dblP G) σ (σ.setv (G 0) (2 * a)) (26 * a + 5) := by
  have e1 := copyR_spec cap (v := G 0) (d := G 1) (t := G 2) (hG G (by decide)) (hG G (by decide))
    (hG G (by decide)) σ h2 (by omega)
  rw [h1, hA, Nat.zero_add] at e1
  have e2 := wmove_spec (cap := cap) (G 1) (G 0) (hG G (by decide)) a (σ.setv (G 1) a) (by simp) (by simp; omega)
    (by simp [Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 1 by decide)), hA]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq <;> simp
  funext r
  by_cases r0 : r = G 0
  · subst r0; simp [Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 1 by decide)), hA]; ring
  · by_cases r1 : r = G 1
    · subst r1; simp [Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide)), h1]
    · simp [Function.update_of_ne r0, Function.update_of_ne r1]

theorem mul_spec (σ : WState ns nr) (a b : ℕ) (hA : σ.val (G 0) = a) (hB : σ.val (G 4) = b) (h1 : σ.val (G 1) = 0)
    (h2 : σ.val (G 2) = 0) (hc : a * b + a ≤ cap) :
    WExec cap (mulP G) σ (σ.setv (G 0) (a * b)) (a * (18 * b + 7) + 1 + 1 + (7 * (a * b) + 1)) := by
  have e1 := mulR_spec cap (B := G 4) (M := G 0) (T := G 1) (t := G 2) (hG G (by decide)) (hG G (by decide))
    (hG G (by decide)) (hG G (by decide)) (hG G (by decide)) (hG G (by decide)) σ b a hB hA h2
    (by rw [h1]; nlinarith) (by nlinarith)
  rw [h1, Nat.zero_add] at e1
  have e2 := wmove_spec (cap := cap) (G 1) (G 0) (hG G (by decide)) (a * b) ((σ.setv (G 1) (a * b)).setv (G 0) 0)
    (by simp [Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide))])
    (by simp [Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide))]; nlinarith)
    (by simp [Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide))]; nlinarith)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by ring_nf; omega)
  apply WState.eq <;> simp
  funext r
  by_cases r0 : r = G 0
  · subst r0; simp [Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 1 by decide))]
  · by_cases r1 : r = G 1
    · subst r1; simp [Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide)), h1]
    · simp [Function.update_of_ne r0, Function.update_of_ne r1]

theorem pow_spec (b : ℕ) (hb : 1 ≤ b) : ∀ (E a : ℕ) (σ : WState ns nr), σ.val (G 0) = a → σ.val (G 4) = b →
    σ.val (G 1) = 0 → σ.val (G 2) = 0 → a * b ^ E * b + a * b ^ E ≤ cap →
    WExec cap (powP G E) σ (σ.setv (G 0) (a * b ^ E)) (E * (40 * (a * b ^ E * b) + 10))
  | 0, a, σ, hA, _, _, _, _ => by
    simp only [powP, pow_zero, Nat.mul_one, Nat.zero_mul]
    rw [← hA, wsetv_same]; exact WExec.skip σ
  | E + 1, a, σ, hA, hB, h1, h2, hc => by
    have hpE : a * b ^ E ≤ a * b ^ (E + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (by omega))
    have hpE' : a * b ^ (E + 1) * b ≥ a * b ^ E * b := Nat.mul_le_mul_right _ hpE
    have e1 := pow_spec b hb E a σ hA hB h1 h2 (by
      have : a * b ^ (E + 1) = a * b ^ E * b := by ring
      nlinarith)
    have e2 := mul_spec cap G (σ.setv (G 0) (a * b ^ E)) (a * b ^ E) b (by simp)
      (by simp [Function.update_of_ne (hG G (show (4 : Fin 6) ≠ 0 by decide)), hB])
      (by simp [Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide)), h1])
      (by simp [Function.update_of_ne (hG G (show (2 : Fin 6) ≠ 0 by decide)), h2])
      (by have : a * b ^ (E + 1) = a * b ^ E * b := by ring
          nlinarith)
    refine WExec.cast cap (WExec.seq e1 e2) (by rw [wsetv_setv]; ring_nf) ?_
    set X := a * b ^ E with hX
    have eq : a * b ^ (E + 1) * b = X * b * b := by rw [hX]; ring
    have hX1 : X ≤ X * b := Nat.le_mul_of_pos_right _ hb
    have hX2 : X * b ≤ X * b * b := Nat.le_mul_of_pos_right _ hb
    have h3 : E * (40 * (X * b) + 10) ≤ E * (40 * (X * b * b) + 10) := Nat.mul_le_mul_left _ (by omega)
    have h5 : X * (18 * b + 7) = 18 * (X * b) + 7 * X := by ring
    rw [eq, h5, Nat.add_mul, Nat.one_mul]
    omega

theorem dblLoop_spec (σ : WState ns nr) (a s : ℕ) (hA : σ.val (G 0) = a) (hS : σ.val (G 3) = s)
    (h1 : σ.val (G 1) = 0) (h2 : σ.val (G 2) = 0) (hc : 2 * (a * 2 ^ s) + s ≤ cap) :
    WExec cap (repLoop (G 3) (dblP G)) σ ((σ.setv (G 0) (a * 2 ^ s)).setv (G 3) 0)
      (s * (26 * (a * 2 ^ s) + 9) + 1) := by
  let g : ℕ → WState ns nr := fun i => (σ.setv (G 0) (a * 2 ^ i)).setv (G 3) (s - i)
  have hg0 : g 0 = σ := by
    simp only [g, pow_zero, Nat.mul_one, Nat.sub_zero]; rw [← hA, wsetv_same, ← hS, wsetv_same]
  have e := repLoop_spec cap (G 3) (dblP G) s (26 * (a * 2 ^ s) + 5) g (fun i _ => by simp [g]) (by omega)
    (fun i hi => by
      have hai : a * 2 ^ i ≤ a * 2 ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hi.le)
      have hai1 : a * 2 ^ (i + 1) ≤ a * 2 ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hi)
      simp only [g]; rw [wsetv_setv]
      have e1 := dbl_spec cap G ((σ.setv (G 0) (a * 2 ^ i)).setv (G 3) (s - i - 1)) (a * 2 ^ i)
        (by simp [Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 3 by decide))])
        (by simp [Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 3 by decide)),
          Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide)), h1])
        (by simp [Function.update_of_ne (hG G (show (2 : Fin 6) ≠ 3 by decide)),
          Function.update_of_ne (hG G (show (2 : Fin 6) ≠ 0 by decide)), h2])
        (by rw [pow_succ] at hai1; nlinarith)
      refine WExec.mono (WExec.cast cap e1 ?_ le_rfl) (by omega)
      apply WState.eq <;> simp
      funext r
      by_cases r0 : r = G 0
      · subst r0; simp [Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 3 by decide)), pow_succ]; ring
      · by_cases r3 : r = G 3
        · subst r3; simp [Function.update_of_ne (hG G (show (3 : Fin 6) ≠ 0 by decide))]; omega
        · simp [Function.update_of_ne r0, Function.update_of_ne r3])
  rw [hg0] at e
  simpa [g] using e

theorem blankLoop_spec (LOG : Fin (ns + 1)) (σ : WState ns nr) (m : ℕ) (hA : σ.val (G 0) = m)
    (hO : σ.val (G 5) = 0) (hL : σ.st LOG = []) (hLh : σ.sh LOG = 0) (hc : m + 1 ≤ cap) :
    WExec cap (repLoop (G 0) (emitC LOG (G 5) false)) σ
      ((((σ.sets LOG (List.replicate m false)).seth LOG m).setv (G 5) m).setv (G 0) 0) (m * 11 + 1) := by
  let g : ℕ → WState ns nr := fun i =>
    (((σ.sets LOG (List.replicate i false)).seth LOG i).setv (G 5) i).setv (G 0) (m - i)
  have hg0 : g 0 = σ := by
    apply WState.eq
    · funext j; by_cases hj : j = LOG
      · subst hj; simp [g, hLh]
      · simp [g, Function.update_of_ne hj]
    · funext j; by_cases hj : j = LOG
      · subst hj; simp [g, hL]
      · simp [g, Function.update_of_ne hj]
    · funext r; by_cases r0 : r = G 0
      · subst r0; simp [g, hA]
      · by_cases r5 : r = G 5
        · subst r5; simp [g, Function.update_of_ne (hG G (show (5 : Fin 6) ≠ 0 by decide)), hO]
        · simp [g, Function.update_of_ne r0, Function.update_of_ne r5]
    · simp [g]
  have e := repLoop_spec cap (G 0) (emitC LOG (G 5) false) m 7 g (fun i _ => by simp [g]) (by omega)
    (fun i hi => by
      simp only [g]; rw [wsetv_setv]
      have e1 := emitC_spec (cap := cap) LOG (G 5) false
        ((((σ.sets LOG (List.replicate i false)).seth LOG i).setv (G 5) i).setv (G 0) (m - i - 1)) (by simp)
        (by simp [Function.update_of_ne (hG G (show (5 : Fin 6) ≠ 0 by decide))]; omega)
      refine WExec.cast cap e1 ?_ le_rfl
      apply WState.eq
      · funext j; by_cases hj : j = LOG
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      · funext j; by_cases hj : j = LOG
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      · funext r; by_cases r0 : r = G 0
        · subst r0; simp [Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 5 by decide))]; omega
        · by_cases r5 : r = G 5
          · subst r5; simp [Function.update_of_ne (hG G (show (5 : Fin 6) ≠ 0 by decide))]
          · simp [Function.update_of_ne r0, Function.update_of_ne r5]
      · simp)
  rw [hg0] at e
  refine WExec.cast cap e ?_ (by omega)
  simp [g]

/-- **The log.** `Cl·2^s·b^El` blanks (`G 3 = s`, `G 4 = b = n + 1`). -/
def logP (LOG : Fin (ns + 1)) (Cl El : ℕ) : WM ns nr :=
  .seq (incN (G 0) Cl) (.seq (repLoop (G 3) (dblP G)) (.seq (powP G El)
    (.seq (repLoop (G 0) (emitC LOG (G 5) false)) (WM.rewind LOG (G 5)))))

theorem logP_spec (LOG : Fin (ns + 1)) (Cl El : ℕ) (σ : WState ns nr) (s b : ℕ) (hb : 1 ≤ b)
    (h0 : σ.val (G 0) = 0) (h1 : σ.val (G 1) = 0) (h2 : σ.val (G 2) = 0) (hS : σ.val (G 3) = s)
    (hB : σ.val (G 4) = b) (h5 : σ.val (G 5) = 0) (hL : σ.st LOG = []) (hLh : σ.sh LOG = 0)
    (hc : 4 * (Cl * 2 ^ s * b ^ El * b) + s + 4 ≤ cap) :
    WExec cap (logP G LOG Cl El) σ ((σ.sets LOG (List.replicate (Cl * 2 ^ s * b ^ El) false)).setv (G 3) 0)
      (100 * (El + s + 1) * (Cl * 2 ^ s * b ^ El * b + 1)) := by
  have hb0 : Cl * 2 ^ s ≤ Cl * 2 ^ s * b ^ El := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  have hb1 : Cl * 2 ^ s * b ^ El ≤ Cl * 2 ^ s * b ^ El * b := Nat.le_mul_of_pos_right _ hb
  have hCl : Cl ≤ Cl * 2 ^ s := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos s)
  have e1 := incN_spec cap (G 0) Cl σ (by rw [h0]; omega)
  rw [h0, Nat.zero_add] at e1
  set σ1 := σ.setv (G 0) Cl with hσ1
  have e2 := dblLoop_spec cap G σ1 Cl s (by simp [hσ1])
    (by simp [hσ1, Function.update_of_ne (hG G (show (3 : Fin 6) ≠ 0 by decide)), hS])
    (by simp [hσ1, Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide)), h1])
    (by simp [hσ1, Function.update_of_ne (hG G (show (2 : Fin 6) ≠ 0 by decide)), h2]) (by omega)
  set σ2 := (σ1.setv (G 0) (Cl * 2 ^ s)).setv (G 3) 0 with hσ2
  have e3 := pow_spec cap G b hb El (Cl * 2 ^ s) σ2
    (by simp [hσ2, Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 3 by decide))])
    (by simp [hσ2, hσ1, Function.update_of_ne (hG G (show (4 : Fin 6) ≠ 3 by decide)),
      Function.update_of_ne (hG G (show (4 : Fin 6) ≠ 0 by decide)), hB])
    (by simp [hσ2, hσ1, Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 3 by decide)),
      Function.update_of_ne (hG G (show (1 : Fin 6) ≠ 0 by decide)), h1])
    (by simp [hσ2, hσ1, Function.update_of_ne (hG G (show (2 : Fin 6) ≠ 3 by decide)),
      Function.update_of_ne (hG G (show (2 : Fin 6) ≠ 0 by decide)), h2]) (by omega)
  set m := Cl * 2 ^ s * b ^ El with hm
  set σ3 := σ2.setv (G 0) m with hσ3
  have e4 := blankLoop_spec cap G LOG σ3 m (by simp [hσ3])
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (hG G (show (5 : Fin 6) ≠ 3 by decide)),
      Function.update_of_ne (hG G (show (5 : Fin 6) ≠ 0 by decide)), h5])
    (by simp [hσ3, hσ2, hσ1, hL]) (by simp [hσ3, hσ2, hσ1, hLh]) (by omega)
  set σ4 := (((σ3.sets LOG (List.replicate m false)).seth LOG m).setv (G 5) m).setv (G 0) 0 with hσ4
  have e5 := wrewind_spec (cap := cap) LOG (G 5) m σ4
    (by simp [hσ4, Function.update_of_ne (hG G (show (5 : Fin 6) ≠ 0 by decide))]) (by
      simp [hσ4, Function.update_of_ne (hG G (show (5 : Fin 6) ≠ 0 by decide))]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ ?_
  · apply WState.eq
    · funext j; by_cases hj : j = LOG
      · subst hj; simp [hσ4, hσ3, hσ2, hσ1, hLh]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hj]
    · funext j; by_cases hj : j = LOG
      · subst hj; simp [hσ4, hσ3, hσ2, hσ1]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hj]
    · funext r
      by_cases r5 : r = G 5
      · subst r5; simp [h5]
      · by_cases r0 : r = G 0
        · subst r0; simp [hσ4, Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 5 by decide)),
            Function.update_of_ne (hG G (show (0 : Fin 6) ≠ 3 by decide)), h0]
        · by_cases r3 : r = G 3
          · subst r3; simp [hσ4, hσ3, hσ2, Function.update_of_ne r5, Function.update_of_ne r0]
          · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne r5, Function.update_of_ne r0, Function.update_of_ne r3]
    · simp [hσ4, hσ3, hσ2, hσ1]
  · have hs2 : s * (26 * (Cl * 2 ^ s) + 9) + 1 ≤ (s + 1) * (26 * (m * b) + 10) := by
      have : Cl * 2 ^ s ≤ m * b := hb0.trans hb1
      nlinarith
    have hp : El * (40 * (Cl * 2 ^ s * b ^ El * b) + 10) ≤ El * (40 * (m * b) + 10) := le_rfl
    have hfin : 4 * Cl + 1 + (s + 1) * (26 * (m * b) + 10) + 1 + (El * (40 * (m * b) + 10) + 1 +
        (m * 11 + 1 + 1 + (5 * m + 1))) ≤ 100 * (El + s + 1) * (m * b + 1) := by
      have hCm : Cl ≤ m * b := hCl.trans (hb0.trans hb1)
      have hmb : m ≤ m * b := hb1
      nlinarith
    omega

end Log

end NearCubicGates.Close.CounterMachine
