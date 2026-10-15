import Proof.Gates.CounterMachine.CellTablesCst
import Proof.Gates.CounterMachine.CellTablesBodySpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW)

def cA : Fin VV := ⟨81, by decide⟩
def cB : Fin VV := ⟨82, by decide⟩
def cI : Fin VV := ⟨83, by decide⟩
def cKB : Fin VV := ⟨84, by decide⟩
def cKL : Fin VV := ⟨85, by decide⟩
def cDB : Fin VV := ⟨86, by decide⟩
def cSD : Fin VV := ⟨87, by decide⟩
def cT : Fin VV := ⟨88, by decide⟩
def cKK : Fin VV := ⟨89, by decide⟩

/-! ## Loops -/

/-- `x := 2^c`. -/
def pow2P (x i c : Fin VV) : St VV MM := .seq (.op (.copy x v1)) (forS i c (.op (.shl x)))

theorem pow2P_spec (C : Ctx) (x i c : Fin VV) (hxi : x ≠ i) (hxc : x ≠ c) (hic : i ≠ c) (hx1 : x ≠ v1)
    (a : DS VV MM) (hc : Cst a) (m : ℕ) (hm : a.env c = m) (hW : m < C.Wd) :
    Hs C (pow2P x i c) a (5 * m + 6) (fun e => e.env x = 2 ^ m ∧ e.sh = a.sh ∧ Fr a e [x, i]) := by
  have hmW : m < 2 ^ C.Wd := lt_of_lt_of_le hW (Nat.lt_two_pow_self).le
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := m * (1 + 4) + 4) (hs_copy C x v1 a hx1) (fun b hb => ?_)) (by omega)
    (fun _ h => h)
  subst hb
  let I : ℕ → DS VV MM → Prop := fun k e => e.env x = 2 ^ k ∧ e.sh = a.sh ∧ Fr a e [x, i]
  refine Hs.mono (forS_spec' (C := C) i c hic _ _ m hmW I 1
    (fun k e v ⟨i1, i2, i3⟩ => ⟨by rw [DS.set_env_ne _ _ hxi]; exact i1, by simpa using i2,
      Fr.trans i3 (Fr.set e v (by simp))⟩)
    ⟨by vsimp [hc.one], by simp, Fr.set a _ (by simp)⟩ (by rw [DS.set_env_ne _ _ (Ne.symm hxc)]; exact hm) ?_)
    le_rfl (fun e ⟨h, _, _⟩ => h)
  intro k hk e ⟨i1, i2, i3⟩ hek hem
  have : 2 ^ (k + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hk
  have : 2 ^ m < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) hW
  refine Hs.mono (hs_shl C x e (by rw [i1, ← pow_succ']; omega)) le_rfl ?_
  rintro f rfl
  refine ⟨⟨by rw [DS.set_env_self, i1, pow_succ]; ring, by simpa using i2, Fr.trans i3 (Fr.set e _ (by simp))⟩,
    by rw [DS.set_env_ne _ _ (Ne.symm hxi)]; exact hek, by rw [DS.set_env_ne _ _ (Ne.symm hxc)]; exact hem⟩

/-- `m := size x`, `x := 0`. -/
def sizeP (x m : Fin VV) : St VV MM := .seq (.op (.zero m)) (.loop (.lt vZ x) (.seq (.op (.half x)) (.op (.inc m))))

theorem sizeP_spec (C : Ctx) (x m : Fin VV) (hxm : x ≠ m) (hx0 : x ≠ vZ) (hm0 : m ≠ vZ) (a : DS VV MM) (hc : Cst a)
    (v : ℕ) (hv : a.env x = v) (hsz : Nat.size v < 2 ^ C.Wd) :
    Hs C (sizeP x m) a (5 * Nat.size v + 4) (fun e => e.env m = Nat.size v ∧ e.env x = 0 ∧ e.sh = a.sh ∧
      Fr a e [x, m]) := by
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := Nat.size v * (3 + 2) + 2) (hs_zero C m a) (fun b hb => ?_)) (by omega)
    (fun _ h => h)
  subst hb
  let I : ℕ → DS VV MM → Prop := fun k e => e.env x = v / 2 ^ k ∧ e.env m = k ∧ e.env vZ = 0 ∧ e.sh = a.sh ∧
    Fr a e [x, m]
  refine Hs.mono (Hs.loopN (C := C) (c := .lt vZ x) (s := .seq (.op (.half x)) (.op (.inc m))) (Ne.symm hx0) I
    (Nat.size v) 3 ?_ ?_ (a.set m 0) ⟨by rw [DS.set_env_ne _ _ hxm, hv]; simp, by simp,
      by rw [DS.set_env_ne _ _ (Ne.symm hm0)]; exact hc.z, by simp, Fr.set a 0 (by simp)⟩) le_rfl ?_
  · intro k hk e ⟨i1, i2, i3, i4, i5⟩
    have hpos : 0 < v / 2 ^ k := Nat.div_pos (Nat.lt_size.mp hk) (Nat.two_pow_pos k)
    refine ⟨by simp [Cnd.eval, i1, i3, hpos], ?_⟩
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_half C x e) (fun f hf => ?_)
    subst hf
    refine Hs.mono (hs_inc C m _ (by rw [DS.set_env_ne _ _ (Ne.symm hxm), i2]; omega)) le_rfl ?_
    rintro g rfl
    refine ⟨?_, by vsimp [i2, Ne.symm hxm], ?_, by simpa using i4, Fr.trans i5 (Fr.trans (Fr.set _ _ (by simp))
      (Fr.set _ _ (by simp)))⟩
    · rw [DS.set_env_ne _ _ hxm, DS.set_env_self, i1, Nat.div_div_eq_div_mul, pow_succ]
    · rw [DS.set_env_ne _ _ (Ne.symm hm0), DS.set_env_ne _ _ (Ne.symm hx0)]; exact i3
  · intro e ⟨i1, _, i3, _, _⟩
    have : v / 2 ^ Nat.size v = 0 := Nat.div_eq_of_lt (Nat.lt_size_self v)
    simp [Cnd.eval, i1, i3, this]
  · rintro e ⟨i1, i2, _, i4, i5⟩
    exact ⟨i2, by rw [i1]; exact Nat.div_eq_of_lt (Nat.lt_size_self v), i4, i5⟩

/-- `x := x·y^c` (scratch `t`). -/
def powP (x y i c t : Fin VV) : St VV MM := forS i c (.seq (.op (.mul x y t)) (.op (.copy x t)))

theorem powP_spec (C : Ctx) (x y i c t : Fin VV) (hxy : x ≠ y) (hxi : x ≠ i) (hxc : x ≠ c) (hxt : x ≠ t)
    (hyi : y ≠ i) (hyt : y ≠ t) (hic : i ≠ c) (hit : i ≠ t) (hct : c ≠ t) (a : DS VV MM) (m u w : ℕ)
    (hm : a.env c = m) (hu : a.env x = u) (hw : a.env y = w) (hmW : m < 2 ^ C.Wd) (hfit : u * w ^ m < 2 ^ C.Wd) :
    Hs C (powP x y i c t) a (7 * m + 4) (fun e => e.env x = u * w ^ m ∧ e.sh = a.sh ∧ Fr a e [x, i, t]) := by
  let I : ℕ → DS VV MM → Prop := fun k e => e.env x = u * w ^ k ∧ e.env y = w ∧ e.sh = a.sh ∧ Fr a e [x, i, t]
  refine Hs.mono (forS_spec' (C := C) i c hic _ a m hmW I 3
    (fun k e v ⟨i1, i2, i3, i4⟩ => ⟨by rw [DS.set_env_ne _ _ hxi]; exact i1, by rw [DS.set_env_ne _ _ hyi]; exact i2,
      by simpa using i3, Fr.trans i4 (Fr.set e v (by simp))⟩)
    ⟨by rw [hu]; simp, hw, rfl, Fr.refl _ _⟩ hm ?_) (by omega) (fun e ⟨⟨h1, _, h3, h4⟩, _, _⟩ => ⟨h1, h3, h4⟩)
  intro k hk e ⟨i1, i2, i3, i4⟩ hek hem
  have hle : u * w ^ (k + 1) ≤ u * w ^ m ∨ w = 0 := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · right; exact h0
    · left; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h0 hk)
  have hfk : u * w ^ k * w < 2 ^ C.Wd := by
    rcases hle with h | h
    · rw [mul_assoc, ← pow_succ]; omega
    · rw [h]; simp
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_mul C x y t e hxy hxt hyt (by rw [i1, i2]; exact hfk)) (fun f hf => ?_)
  subst hf
  refine Hs.mono (hs_copy C x t _ hxt) le_rfl ?_
  rintro g rfl
  refine ⟨⟨?_, ?_, by simpa using i3, Fr.trans i4 (Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp)))⟩, ?_, ?_⟩
  · simp [i1, i2, pow_succ, mul_assoc]
  · rw [DS.set_env_ne _ _ (Ne.symm hxy), DS.set_env_ne _ _ hyt]; exact i2
  · rw [DS.set_env_ne _ _ (Ne.symm hxi), DS.set_env_ne _ _ hit]; exact hek
  · rw [DS.set_env_ne _ _ (Ne.symm hxc), DS.set_env_ne _ _ hct]; exact hem

end NearCubicGates.Close.CounterMachine.CellTablesProg
