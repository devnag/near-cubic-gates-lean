import Proof.Gates.CounterMachine.CellTablesBody6

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

theorem keyBits_two (p : Params) : 2 ≤ keyBits p := by
  unfold keyBits
  have : 2 ^ 1 ≤ p.P + p.J + 3 := by omega
  have := Nat.lt_size.mpr this
  omega

theorem resB_spec : ResBSpec resB := by
  intro B1 B2 cT PolyTab RK r Wd Lk Bk wb inp a part q t hF hP hpart hq ht hPC hQ hQE hQD hT
  set C := ctxK RK Wd inp Lk Bk with hC
  set X := (cellInput r).length with hX
  have hWd : 4 ≤ C.Wd := by have := hF.wd; show 4 ≤ Wd; omega
  obtain ⟨hqP, hqp⟩ := prime_le_P r hq
  have hq0 : 0 < q := hqp.pos
  have hq2 : 2 ≤ q := hqp.two_le
  have hpc : partCode part ≤ 2 := by cases part with | none => decide | some b => cases b <;> decide
  set x : TabCallReq B1 B2 cT := ⟨r, resId r.c r.p part q t, resId_mem r.c r.p part q t hpart hq hq0⟩ with hx
  have hqB : q < 2 ^ keyBits r.p := lt_keyB r.p q hqP
  have hKB2 := keyBits_two r.p
  have hB4 : 4 ≤ 2 ^ keyBits r.p := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ keyBits r.p := Nat.pow_le_pow_right (by norm_num) hKB2
  have hKL : keyLen r.c r.p = dOf r.c r.p + 3 := by unfold keyLen dOf; omega
  have hKBKL : 2 ^ (keyBits r.p * keyLen r.c r.p) ≤ 2 ^ C.Wd := by
    have := hF.wd; unfold lamW at this
    exact Nat.pow_le_pow_right (by norm_num) (by show _ ≤ Wd; omega)
  have hkey : (partCode part * 2 ^ keyBits r.p + q + 1) * (2 ^ keyBits r.p) ^ dOf r.c r.p ≤ 2 ^ C.Wd := by
    have h1 : partCode part * 2 ^ keyBits r.p + q + 1 ≤ 2 ^ keyBits r.p * 2 ^ keyBits r.p := by nlinarith
    have h2 : (2 ^ keyBits r.p) ^ dOf r.c r.p * (2 ^ keyBits r.p * 2 ^ keyBits r.p) ≤ 2 ^ (keyBits r.p * keyLen r.c r.p) := by
      rw [hKL, pow_mul, ← pow_two, ← pow_add]
      exact Nat.pow_le_pow_right (by positivity) (by omega)
    calc (partCode part * 2 ^ keyBits r.p + q + 1) * (2 ^ keyBits r.p) ^ dOf r.c r.p ≤ (2 ^ keyBits r.p * 2 ^ keyBits r.p) * (2 ^ keyBits r.p) ^ dOf r.c r.p :=
          Nat.mul_le_mul_right _ h1
      _ = (2 ^ keyBits r.p) ^ dOf r.c r.p * (2 ^ keyBits r.p * 2 ^ keyBits r.p) := by ring
      _ ≤ _ := h2.trans hKBKL
  have hLk : (tabCallInput x).length ≤ C.Lk := hF.lk x rfl
  have hRK : (tabCallInput x).length = (natWord 0).length + (natWord (partCode part)).length + (natWord q).length +
      (natWord (dOf r.c r.p)).length + ((digs q t (dOf r.c r.p)).flatMap natWord).length + X := by
    show ((descN (resId r.c r.p part q t)).flatMap natWord ++ cellInput r).length = _
    rw [descN_res]; simp only [List.length_append]; omega
  have nb : ∀ y : Fin VV, bodyVarB y = false → ¬ BodyVar y := fun y h => not_bodyVar h
  unfold resB
  apply Hx.hs
  refine Hs.then (resHead_spec RK r Wd Lk Bk wb inp a part q t hF hP hpart hq hPC hQ hQD)
    (fun e1 ⟨k1, key1, pw1, s1, c1, bf1, w1⟩ n1 hn1 => ?_)
  have hDW : dOf r.c r.p < 2 ^ C.Wd := by
    have := w1.env_lt kD; rwa [bf1 kD (nb kD (by decide)), hP.d] at this
  refine Hs.then (PrefixProg.Hs.valid (digL_spec C e1 c1 (by omega) q t (dOf r.c r.p) (2 ^ keyBits r.p) _ (natBitLength q) hq2
    (by rw [bf1 lQ (nb lQ (by decide))]; exact hQ) (by rw [bf1 lT (nb lT (by decide))]; exact hT)
    (by rw [bf1 kD (nb kD (by decide))]; exact hP.d) (by rw [bf1 kB2 (nb kB2 (by decide))]; exact hP.b2) pw1 key1
    (hF.qd q hq) hDW hqB.le hkey le_rfl (by rw [k1]; simp only [List.length_append]; omega)) w1 (by omega))
    (fun e2 ⟨⟨k2, key2, s2, c2, f2⟩, w2⟩ n2 hn2 => ?_)
  have bf2 : BF a e2 := BF.trans bf1 (BF.of_fr f2 (by decide))
  have e2ram : e2.ram = a.ram := s2.ram.trans s1.ram
  have e2rc : e2.rc = a.rc := s2.rc.trans s1.rc
  refine Hs.last (tail_spec RK Wd Lk Bk wb inp x e2 kVW2 lQE v1 (q ^ r.p.e) true hF (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w2 c2
    (by rw [e2ram]; exact hP.ramN) (by rw [bf2 wN (nb wN (by decide))]; exact hP.wN)
    (by rw [bf2 vH1 (nb vH1 (by decide))]; exact hP.h1) (by rw [bf2 vH0 (nb vH0 (by decide))]; exact hP.h0)
    (by rw [bf2 vSH (nb vSH (by decide))]; exact hP.sh)
    (by rw [k2, k1]; show _ = (descN (resId r.c r.p part q t)).flatMap natWord; rw [descN_res])
    (by rw [key2, bf2 kVW2 (nb kVW2 (by decide)), hP.vw2]; show _ = reqKey r.c r.p (resId r.c r.p part q t) * _
        rw [reqKey_res])
    (by rw [bf2 lQE (nb lQE (by decide))]; exact hQE) (by rw [c2.one]; rfl)
    (by intro part' q' κ σ h; simp only [hx, resId] at h; injection h with _ h2; exact ⟨rfl, by rw [h2]⟩)
    (by intro h; exfalso; exact h part q _ _ rfl)
    (fun _ => Nat.pow_pos hq0) (hF.qe q hq) (by rw [e2rc, e2ram]; exact hP.rcR))
    (fun e3 hp3 n3 hn3 => ?_)
  refine ⟨⟨by rw [hp3.ramR, e2ram], hp3.rcR, fun m h1 h2 => by rw [hp3.ram m h1 h2, e2ram], hp3.rcN,
    fun m h1 h2 h3 => by rw [hp3.rc m h1 h2 h3, e2rc], by rw [hp3.out, s2.out, s1.out],
    by rw [hp3.ip, s2.ip, s1.ip], hp3.kin, hp3.valid, hp3.cst, BF.trans bf2 hp3.fr⟩, ?_⟩
  have hrcN : e2.rc sN ≤ X := by
    have := w2.rc_le sN; rw [e2ram, hP.ramN] at this; exact this.trans (cellN_len_le r)
  have hA : (cellN r.c r.p r.wt).length * (40 * X + 42 + 4) ≤ X * (40 * X + 46) :=
    Nat.mul_le_mul_right _ (cellN_len_le r)
  have hnq : natBitLength q ≤ X := nbl_le_cellInput r q (prime_mem_cellN r hq)
  have hB : dOf r.c r.p * (40 * natBitLength q + 60 + 4) ≤ (2 * X + 2) * (40 * X + 64) :=
    Nat.mul_le_mul (dOf_le r) (by omega)
  unfold tailCost at hn3
  unfold bodyCost
  nlinarith

end NearCubicGates.Close.CounterMachine.CellTablesProg
