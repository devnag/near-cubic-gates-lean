import Proof.Gates.CounterMachine.FormulaProd

/-! # RG machine, part 16: the binomial constants of `Amp_e`

`Amp_e(t) = 1 − (1−t)^e Σ_{j<e} C(e−1+j, j) t^j` (lem:amp). The printer keeps `b_j = C(e−1+j, j)` in a
unary register and steps `b_{j+1} = b_j·(e+j)/(j+1)` (`Nat.succ_mul_choose_eq`): **`binStep_spec`**, a unary
multiplication (`mulR`) and an exact unary division (`divR`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Codec

variable {ns nr : ℕ} (cap : ℕ)

theorem binom_succ (e j : ℕ) (he : 1 ≤ e) : binom e j * (e + j) = binom e (j + 1) * (j + 1) := by
  unfold binom
  have h := Nat.add_one_mul_choose_eq (e - 1 + j) j
  rw [show e - 1 + j + 1 = e + j by omega] at h
  rw [show e - 1 + (j + 1) = e + j by omega, ← h]; ring

section Arith
variable (B M T Z t : Fin nr)

/-- `T := T + b·m` for `m` in `M` (cleared), `b` in `B`. -/
def mulR : WM ns nr := repLoop M (copyR B T t)

theorem mulR_spec (hBM : B ≠ M) (hBT : B ≠ T) (hBt : B ≠ t) (hMT : M ≠ T) (hMt : M ≠ t) (hTt : T ≠ t)
    (σ : WState ns nr) (b m : ℕ) (hb : σ.val B = b) (hm : σ.val M = m) (ht : σ.val t = 0)
    (hcap : σ.val T + m * b ≤ cap) (hcm : m ≤ cap) :
    WExec cap (mulR B M T t) σ ((σ.setv T (σ.val T + m * b)).setv M 0) (m * (18 * b + 3 + 4) + 1) := by
  unfold mulR
  let g : ℕ → WState ns nr := fun i => (σ.setv T (σ.val T + i * b)).setv M (m - i)
  have hg0 : g 0 = σ := by
    simp only [g, Nat.zero_mul, Nat.add_zero, Nat.sub_zero]; rw [← hm, wsetv_same, wsetv_same]
  have e := repLoop_spec cap M (copyR B T t) m (18 * b + 3) g (fun i _ => by simp [g])
    hcm (fun i hi => by
      simp only [g]
      rw [wsetv_setv]
      have e1 := copyR_spec cap (v := B) (d := T) (t := t) hBT hBt hTt ((σ.setv T (σ.val T + i * b)).setv M (m - i - 1))
        (by simp [Function.update_of_ne hMt.symm, Function.update_of_ne hTt.symm, ht])
        (by simp [Function.update_of_ne hMT.symm, Function.update_of_ne hBM, Function.update_of_ne hBT, hb]
            have : i * b + b ≤ m * b := by nlinarith
            omega)
      have vB : ((σ.setv T (σ.val T + i * b)).setv M (m - i - 1)).val B = b := by
        simp [Function.update_of_ne hBM, Function.update_of_ne hBT, hb]
      have vT : ((σ.setv T (σ.val T + i * b)).setv M (m - i - 1)).val T = σ.val T + i * b := by
        simp [Function.update_of_ne hMT.symm]
      rw [vB, vT] at e1
      refine WExec.cast cap e1 ?_ le_rfl
      apply WState.eq <;> try rfl
      funext r; by_cases rT : r = T
      · subst rT; simp [Function.update_of_ne hMT.symm]; ring
      · by_cases rM : r = M
        · subst rM; simp [Function.update_of_ne rT]; omega
        · simp [Function.update_of_ne rT, Function.update_of_ne rM])
  rw [hg0] at e
  simpa [g] using e

/-- `Z := Z + T/d` for `d − 1` in `M` and `T` a multiple of `d` (`T` cleared; scratch `t`). -/
def divR : WM ns nr := .whr T (.seq (copyR M t B) (.seq (.inc t) (.seq (repLoop t (.dec T)) (.inc Z))))

theorem decLoop_spec (σ : WState ns nr) (k : ℕ) (hk : σ.val t = k) (hT : k ≤ σ.val T) (hTt : T ≠ t) (hc : k ≤ cap)
    (hTc : σ.val T ≤ cap) :
    WExec cap (repLoop t (.dec T)) σ ((σ.setv T (σ.val T - k)).setv t 0) (k * (1 + 4) + 1) := by
  let g : ℕ → WState ns nr := fun i => (σ.setv T (σ.val T - i)).setv t (k - i)
  have hg0 : g 0 = σ := by simp only [g, Nat.sub_zero]; rw [wsetv_same, ← hk, wsetv_same]
  have e := repLoop_spec cap t (.dec T) k 1 g (fun i _ => by simp [g]) hc (fun i hi => by
    simp only [g]; rw [wsetv_setv]
    have e1 := WExec.dec (cap := cap) T ((σ.setv T (σ.val T - i)).setv t (k - i - 1))
      (by simp [Function.update_of_ne hTt]; omega)
    refine WExec.cast cap e1 ?_ le_rfl
    apply WState.eq <;> try rfl
    funext r; by_cases rT : r = T
    · subst rT; simp [Function.update_of_ne hTt]; omega
    · by_cases rt : r = t
      · subst rt; simp [Function.update_of_ne (Ne.symm hTt)] <;> omega
      · simp [Function.update_of_ne rT, Function.update_of_ne rt])
  rw [hg0] at e
  simpa [g] using e

theorem divR_spec (hBM : B ≠ M) (hBT : B ≠ T) (hBt : B ≠ t) (hBZ : B ≠ Z) (hMT : M ≠ T) (hMt : M ≠ t)
    (hMZ : M ≠ Z) (hTt : T ≠ t) (hTZ : T ≠ Z) (htZ : t ≠ Z) (d1 : ℕ) :
    ∀ (q : ℕ) (σ : WState ns nr), σ.val M = d1 → σ.val T = q * (d1 + 1) → σ.val t = 0 → σ.val B = 0 →
      σ.val T ≤ cap → d1 + 1 ≤ cap → σ.val Z + q ≤ cap →
      WExec cap (divR B M T Z t) σ ((σ.setv T 0).setv Z (σ.val Z + q)) (q * (30 * (d1 + 1) + 30) + 1)
  | 0, σ, _, hT, _, _, _, _, _ => by
    have h0 : σ.val T = 0 := by simp [hT]
    have e0 : σ.setv T 0 = σ := by rw [← h0, wsetv_same]
    have e : (σ.setv T 0).setv Z (σ.val Z + 0) = σ := by rw [Nat.add_zero, e0, wsetv_same]
    rw [e]; exact WExec.mono (WExec.whrF (by simp [hT])) (by omega)
  | q + 1, σ, hM, hT, ht, hB, hTc, hdc, hZc => by
    have e1 := copyR_spec cap (v := M) (d := t) (t := B) hMt (Ne.symm hBM) (Ne.symm hBt) σ hB (by rw [ht, hM]; omega)
    rw [ht, hM, Nat.zero_add] at e1
    have e2 := WExec.inc (cap := cap) t (σ.setv t d1) (by simp; omega)
    simp only [WState.setv_val, Function.update_self, wsetv_setv] at e2
    have e3 := decLoop_spec cap T t (σ.setv t (d1 + 1)) (d1 + 1) (by simp)
      (by simp [Function.update_of_ne hTt, hT] <;> nlinarith) hTt hdc (by simp [Function.update_of_ne hTt]; omega)
    have e4 := WExec.inc (cap := cap) Z (((σ.setv t (d1 + 1)).setv T ((σ.setv t (d1 + 1)).val T - (d1 + 1))).setv t 0)
      (by simp [Function.update_of_ne (Ne.symm htZ), Function.update_of_ne (Ne.symm hTZ)]; omega)
    set τ := (((σ.setv t (d1 + 1)).setv T ((σ.setv t (d1 + 1)).val T - (d1 + 1))).setv t 0).setv Z
      ((((σ.setv t (d1 + 1)).setv T ((σ.setv t (d1 + 1)).val T - (d1 + 1))).setv t 0).val Z + 1) with hτ
    have vT : τ.val T = q * (d1 + 1) := by
      simp [hτ, Function.update_of_ne hTZ, Function.update_of_ne hTt, hT]; ring_nf; omega
    have vZ : τ.val Z = σ.val Z + 1 := by
      simp [hτ, Function.update_of_ne (Ne.symm htZ), Function.update_of_ne (Ne.symm hTZ)]
    have ih := divR_spec hBM hBT hBt hBZ hMT hMt hMZ hTt hTZ htZ d1 q τ
      (by simp [hτ, Function.update_of_ne hMZ, Function.update_of_ne hMt, Function.update_of_ne hMT, hM])
      vT (by simp [hτ, Function.update_of_ne htZ]) (by
        simp [hτ, Function.update_of_ne hBZ, Function.update_of_ne hBt, Function.update_of_ne hBT, hB])
      (by rw [vT]; nlinarith) hdc (by rw [vZ]; omega)
    refine WExec.mono (WExec.whrT (by rw [hT]; positivity) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)))
      (WExec.cast cap ih ?_ le_rfl)) ?_
    · apply WState.eq <;> try rfl
      funext r; by_cases rT : r = T
      · subst rT; simp [Function.update_of_ne hTZ]
      · by_cases rZ : r = Z
        · subst rZ; simp [Function.update_of_ne (Ne.symm hTZ), vZ]; ring
        · by_cases rt : r = t
          · subst rt; simp [hτ, Function.update_of_ne rT, Function.update_of_ne rZ, ht]
          · simp [hτ, Function.update_of_ne rT, Function.update_of_ne rZ, Function.update_of_ne rt]
    · ring_nf; omega

end Arith

/-- `b := C(e+j, j+1)` from `b = C(e−1+j, j)` (`B` the binomial, `J` holds `j`, `E` holds `e`; scratch `T`, `M`, `z`). -/
def binStep (B J E T M z : Fin nr) : WM ns nr :=
  .seq (copyR E M z) (.seq (copyR J M z) (.seq (mulR B M T z) (.seq (WM.clear B) (divR z J T B M))))

theorem binStep_spec (B J E T M z : Fin nr) (hd : [B, J, E, T, M, z].Nodup) (e j Λ : ℕ) (he : 1 ≤ e)
    (σ : WState ns nr) (hB : σ.val B = binom e j) (hJ : σ.val J = j) (hE : σ.val E = e) (hT : σ.val T = 0)
    (hM : σ.val M = 0) (hz : σ.val z = 0) (hΛ : binom e j * (e + j) ≤ Λ) (hejΛ : e + j ≤ Λ) (hcap : Λ + 1 ≤ cap) :
    WExec cap (binStep B J E T M z) σ (σ.setv B (binom e (j + 1))) (200 * (Λ + 1) ^ 2) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd
  obtain ⟨⟨b1, b2, b3, b4, b5⟩, ⟨j1, j2, j3, j4⟩, ⟨e1', e2', e3'⟩, ⟨t1, t2⟩, m1⟩ := hd
  have hbs := binom_succ e j he
  -- M := e + j
  have s1 := copyR_spec cap (v := E) (d := M) (t := z) e2' e3' m1 σ hz (by rw [hM, hE]; omega)
  rw [hM, hE, Nat.zero_add] at s1
  have s2 := copyR_spec cap (v := J) (d := M) (t := z) j3 j4 m1 (σ.setv M e)
    (by simp [Function.update_of_ne (Ne.symm m1), hz]) (by simp [Function.update_of_ne j3, hJ]; omega)
  simp only [WState.setv_val, Function.update_self, Function.update_of_ne j3, hJ, wsetv_setv] at s2
  -- T := b·(e + j)
  set σ2 := σ.setv M (e + j) with hσ2
  have s3 := mulR_spec cap B M T z b4 b3 b5 (Ne.symm t1) m1 t2 σ2 (binom e j) (e + j)
    (by simp [hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hB]) (by simp [hσ2])
    (by simp [hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hz])
    (by simp [hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hT]; nlinarith) (by omega)
  have vT2 : σ2.val T = 0 := by simp [hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hT]
  rw [vT2, Nat.zero_add] at s3
  set σ3 := (σ2.setv T ((e + j) * binom e j)).setv M 0 with hσ3
  -- B := 0
  have s4 := wclear_spec cap B (binom e j) σ3 (by simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hB])
    (by simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hB]; nlinarith)
  -- B := T / (j + 1)
  have hqb : binom e (j + 1) * (j + 1) ≤ Λ := by rw [← hbs]; exact hΛ
  have s5 := divR_spec cap z J T B M (Ne.symm j4) (Ne.symm t2) (Ne.symm m1) (Ne.symm b5) j2 j3 (Ne.symm b1) t1
    (Ne.symm b3) (Ne.symm b4) j (binom e (j + 1)) (σ3.setv B 0)
    (by simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hJ])
    (by simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1]; rw [← hbs]; ring)
    (by simp [hσ3, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1])
    (by simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hz])
    (by simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1]; nlinarith)
    (by omega)
    (by simp; have : binom e (j + 1) ≤ binom e (j + 1) * (j + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · apply WState.eq <;> try rfl
    funext r
    by_cases rB : r = B
    · subst rB; simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1]
    · by_cases rT : r = T
      · subst rT; simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hT]
      · by_cases rM : r = M
        · subst rM; simp [hσ3, hσ2, Function.update_apply, b1, b2, b3, b4, b5, j1, j2, j3, j4, e1', e2', e3', t1, t2, m1, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm b5, Ne.symm j1, Ne.symm j2, Ne.symm j3, Ne.symm j4, Ne.symm e1', Ne.symm e2', Ne.symm e3', Ne.symm t1, Ne.symm t2, Ne.symm m1, hM]
        · simp [hσ3, hσ2, Function.update_apply, rB, rT, rM]
  · have h4 : binom e j ≤ Λ := by
      have : binom e j ≤ binom e j * (e + j) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have h2 : (e + j) * (18 * binom e j + 3 + 4) ≤ 18 * Λ + 7 * Λ := by nlinarith
    have h3 : binom e (j + 1) * (30 * (j + 1) + 30) ≤ 60 * Λ := by nlinarith
    nlinarith

end NearCubicGates.Close.CounterMachine
