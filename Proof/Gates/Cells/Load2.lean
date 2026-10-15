import Proof.Gates.Cells.Load
import Proof.Gates.Cells.InputLen
import Proof.Gates.CounterMachine.CellIdx

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN callN paramsN witN circN gateN intN ratN bitN srList cellN_word
  flatMap_gateN_length flatMap_intN_length)

variable {C : Ctx}

def gN : Fin VV := ⟨21, by decide⟩
def gKd : Fin VV := ⟨22, by decide⟩
def gS : Fin VV := ⟨23, by decide⟩
def gJ : Fin VV := ⟨24, by decide⟩
def gRC : Fin VV := ⟨25, by decide⟩
def gJR : Fin VV := ⟨26, by decide⟩
def kf : Fin VV := ⟨27, by decide⟩

/-! ## Constants -/

/-- Add `k` to `x`. -/
def incS (x : Fin VV) : ℕ → St VV MM
  | 0 => skipS
  | k + 1 => .seq (.op (.inc x)) (incS x k)

theorem incS_spec (x : Fin VV) (hx : x ≠ vJ) :
    ∀ (k : ℕ) (a : DS VV MM), a.env x + k < 2 ^ C.Wd →
      Hs C (incS x k) a (2 * k + 1) (fun b => b.env x = a.env x + k ∧ b.sh = a.sh ∧ Fr a b [x, vJ]) := by
  intro k
  induction k with
  | zero =>
    intro a _
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ hx]; rfl, rfl, Fr.set a 0 (by simp)⟩
  | succ k ih =>
    intro a hk
    refine Hs.mono (Hs.seq (hs_inc C x a (by omega)) (fun b hb => ?_)) (by omega : 1 + (2 * k + 1) + 1 ≤ _)
      (fun _ h => h)
    subst hb
    refine Hs.mono (ih _ (by simp; omega)) le_rfl ?_
    rintro d ⟨h1, h2, h5⟩
    exact ⟨by simp at h1; omega, by simpa using h2, Fr.trans (Fr.set a _ (by simp)) h5⟩

/-- `x := k`. -/
def setK (x : Fin VV) (k : ℕ) : St VV MM := .seq (.op (.zero x)) (incS x k)

theorem setK_spec (x : Fin VV) (hx : x ≠ vJ) (k : ℕ) (a : DS VV MM) (hk : k < 2 ^ C.Wd) :
    Hs C (setK x k) a (2 * k + 3) (fun b => b.env x = k ∧ b.sh = a.sh ∧ Fr a b [x, vJ]) := by
  refine Hs.mono (Hs.seq (hs_zero C x a) (fun b hb => ?_)) (by omega : 1 + (2 * k + 1) + 1 ≤ _) (fun _ h => h)
  subst hb
  refine Hs.mono (incS_spec x hx k _ (by simpa using hk)) le_rfl ?_
  rintro d ⟨h1, h2, h5⟩
  exact ⟨by simpa using h1, by simpa using h2, Fr.trans (Fr.set a 0 (by simp)) h5⟩

theorem Loaded.sh {a b d : DS VV MM} {L : List ℕ} (h1 : Loaded a b L) (h2 : d.sh = b.sh) : Loaded a d L := by
  simp only [DS.sh, Prod.mk.injEq] at h2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := h2
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  exact ⟨by rw [e3, a1], by rw [e4, a2], by rw [e1, a3], by rw [e2, a4], by rw [e5, a5], by rw [e6, a6],
    by rw [e7, a7]⟩

/-! ## Segment loaders with uniform costs (`K = 30Λ + 45` per natural) -/

def loadT : List (Fin VV) := [c1, c2, t0, t1, t2, t3, t4, vJ, lc, kf, gN, gKd, gS, gJ, gRC, gJR]

theorem readL_spec' (str : Fin VV) (hstr : str ∉ readLT) (a : DS VV MM) (hc : Cst a) (S : List ℕ) (c : ℕ)
    (X : List ℕ) (hS : S = [c] ++ X) (tail : List Bool) (Λ : ℕ) (hcw : C.inp.drop a.ip = S.flatMap natWord ++ tail)
    (hX : X.length = c * a.env str) (hfit : ∀ x ∈ S, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd)
    (hL : c * a.env str < 2 ^ C.Wd) (hrc : a.rc sN = (a.ram sN).length) :
    Hs C (readL str) a (S.length * (30 * Λ + 45) + 10) (fun b => Loaded a b S ∧ Cst b ∧ Fr a b readLT) := by
  subst hS
  refine Hs.mono (readL_spec str hstr a hc c X tail Λ hcw hX hfit hΛ hL hrc) ?_ (fun _ h => h)
  simp only [List.length_append, List.length_singleton]; nlinarith

theorem readF_spec' (k : ℕ) (a : DS VV MM) (hc : Cst a) (L : List ℕ) (hk : L.length = k) (tail : List Bool)
    (Λ : ℕ) (hcw : C.inp.drop a.ip = L.flatMap natWord ++ tail) (hfit : ∀ x ∈ L, natBitLength x ≤ Λ)
    (hΛ : Λ + 2 ≤ C.Wd) (hL : k < 2 ^ C.Wd) (hrc : a.rc sN = (a.ram sN).length) (hk2 : k ≤ 20) :
    Hs C (.seq (setK kf k) (readF kf)) a (L.length * (30 * Λ + 45) + 50)
      (fun b => Loaded a b L ∧ Cst b ∧ Fr a b (kf :: readT)) := by
  refine Hs.mono (Hs.seq (t2 := L.length * (30 * Λ + 36) + 4) (setK_spec kf (by decide) k a hL)
    (fun b ⟨b1, b2, b3⟩ => ?_)) ?_ (fun _ h => h)
  · have hsh := Same.of_sh b2
    refine Hs.mono (readF_spec kf (by decide) b (Cst.of_fr hc b3 (by decide)) L tail Λ
      (by rw [hsh.ip, hcw]) (by rw [b1, hk]) hfit hΛ (by rw [hk]; exact hL) (by rw [hsh.rc, hsh.ram, hrc])) le_rfl ?_
    rintro d ⟨d1, d2, d3⟩
    refine ⟨?_, d2, Fr.trans (Fr.weaken b3 (by decide)) (Fr.weaken d3 (by decide))⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := d1
    refine ⟨by rw [e1, hsh.ram], by rw [e2, hsh.rc, hsh.ram], by rw [e3, hsh.ip], by rw [e4, hsh.out],
      by rw [e5, hsh.kin], by rw [e6, hsh.kout], by rw [e7, hsh.kc]⟩
  · subst hk; nlinarith

/-- One circuit: gates, top coefficients, table (stride `2n+3` in `gS`). -/
theorem circ_load (a : DS VV MM) (hc : Cst a) (n : ℕ) (Cc : NCircuit n) (hgS : a.env gS = 2 * n + 3)
    (tail : List Bool) (Λ : ℕ) (hcw : C.inp.drop a.ip = (circN Cc).flatMap natWord ++ tail)
    (hfit : ∀ x ∈ circN Cc, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd) (hbig : (circN Cc).length < 2 ^ C.Wd)
    (hrc : a.rc sN = (a.ram sN).length) :
    Hs C (.seq (readL gS) (.seq (readL v2) (readL v1))) a ((circN Cc).length * (30 * Λ + 45) + 40)
      (fun b => Loaded a b (circN Cc) ∧ Cst b ∧ Fr a b readLT) := by
  have hlen := CounterMachine.circN_length Cc
  set S1 := [Cc.gates.length] ++ Cc.gates.flatMap gateN
  set S2 := [Cc.coeffs.length] ++ Cc.coeffs.flatMap intN
  set S3 := [Cc.table.length] ++ Cc.table.map bitN
  have hcirc : circN Cc = S1 ++ S2 ++ S3 := by simp [circN, S1, S2, S3, List.append_assoc]
  have hl1 : S1.length = 1 + Cc.gates.length * (2 * n + 3) := by
    simp only [S1, List.length_append, List.length_singleton, flatMap_gateN_length]
  have hl2 : S2.length = 1 + Cc.coeffs.length * 2 := by
    simp only [S2, List.length_append, List.length_singleton, flatMap_intN_length]; ring
  have hl3 : S3.length = 1 + Cc.table.length := by simp [S3]; ring
  rw [hcirc] at hcw hfit ⊢
  have hlt : S1.length + S2.length + S3.length < 2 ^ C.Wd := by
    rw [hcirc] at hbig; simp only [List.length_append] at hbig; omega
  have hm := fun x (hx : x ∈ S1 ++ S2 ++ S3) => hfit x hx
  refine Hs.mono (Hs.seq (t2 := S2.length * (30 * Λ + 45) + 10 + (S3.length * (30 * Λ + 45) + 10) + 1)
    (readL_spec' gS (by decide) a hc S1 _ _ rfl ((S2 ++ S3).flatMap natWord ++ tail) Λ
    (by rw [hcw]; simp [List.flatMap_append, List.append_assoc])
    (by rw [hgS, flatMap_gateN_length]) (fun x hx => hm x (by simp [hx])) hΛ
    (by rw [hgS]; have : Cc.gates.length * (2 * n + 3) < 2 ^ C.Wd := by omega
        exact this) hrc) (fun b ⟨b1, b2, b3⟩ => ?_)) ?_ (fun _ h => h)
  · have hcwb : C.inp.drop b.ip = S2.flatMap natWord ++ (S3.flatMap natWord ++ tail) := by
      rw [Loaded.drop (R := S2 ++ S3) (tail := tail) b1 (by rw [hcw]; simp [List.flatMap_append, List.append_assoc])]
      simp [List.flatMap_append, List.append_assoc]
    refine Hs.seq (readL_spec' v2 (by decide) b b2 S2 _ _ rfl (S3.flatMap natWord ++ tail) Λ hcwb
      (by rw [b2.two, flatMap_intN_length]; ring) (fun x hx => hm x (by simp [hx])) hΛ
      (by rw [b2.two]; omega) (Loaded.rc_eq b1)) (fun d ⟨d1, d2, d3⟩ => ?_)
    have hcwd : C.inp.drop d.ip = S3.flatMap natWord ++ tail := by
      rw [Loaded.drop (R := S3) (tail := tail) d1 (by rw [hcwb]; simp [List.flatMap_append, List.append_assoc])]
    refine Hs.mono (readL_spec' v1 (by decide) d d2 S3 _ _ rfl tail Λ hcwd
      (by rw [d2.one]; simp) (fun x hx => hm x (by simp [hx])) hΛ
      (by rw [d2.one]; omega) (Loaded.rc_eq d1)) le_rfl ?_
    rintro e ⟨e1, e2, e3⟩
    exact ⟨by have := Loaded.trans (Loaded.trans b1 d1) e1; simpa [List.append_assoc] using this, e2,
      Fr.trans b3 (Fr.trans d3 e3)⟩
  · simp only [List.length_append]; nlinarith

end NearCubicGates.Close.Cells
