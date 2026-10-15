import Proof.Gates.CellsSys.CallB

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

theorem CS.set {e b : DS VV MM} {Rk : List Bool} (h : CS e Rk b) {x : Fin VV} (hx : FragVar x) (v : ℕ) :
    CS e Rk (b.set x v) :=
  h.step (Same.set b x v) (Fr.set b v (List.mem_singleton_self x)) (fun z hz => by
    rw [List.mem_singleton] at hz; rw [hz]; exact Or.inl hx)

def bitsB : St VV MM :=
  .seq (idxP vTS0 vTW0 l0P a0I l0N) (.seq (fetch sN prd b0) (.seq (.ite (.eq vKd v1)
    (.seq (idxP vTS1 vTW1 l1P a1I l1N) (.seq (fetch sN prd b1) (.op (.add b0 b1)))) skipS)
    (.ite (.eq vKd v2) (.seq (.op (.add b0 vOP)) (.op (.add b0 pI))) skipS)))

def bitsT : List (Fin VV) := [prd, c0, vJ, b0, b1]

def bitsCost (LN : ℕ) : ℕ := 12 * LN + 80

theorem bitsB_spec {e s : DS VV MM} {Rk : List Bool} {K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw : ℕ}
    {md : ℕ → ℕ → ℕ} (hN : CallN e K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw md C) (h : CS e Rk s)
    (a b : ℕ) (ha : a < N0) (hb : b < N1) (h0 : s.env a0I = a) (h1 : s.env a1I = b) :
    Hs C bitsB s (bitsCost (e.ram sN).length) (fun s' => s'.env b0 = b0f (e.ram sN) T0 W0 X0 Y0 a +
      (if K = 1 then b0f (e.ram sN) T1 W1 X1 Y1 b else 0) + (if K = 2 then OP + PI else 0) ∧ CS e Rk s' ∧
      Fr s s' bitsT) := by
  have ev : ∀ x, ¬ FragVar x → x ≠ vCnt → s.env x = e.env x := h.fr
  have hT : ∀ x ∈ bitsT, FragVar x ∨ x = vCnt := fun x hx => Or.inl (by revert x; decide)
  obtain ⟨i1, i2, i3⟩ := hN.i0 a ha
  have hw0 := hN.w0 (by omega)
  have hlen := hN.len
  have h4W : 4 ≤ 2 ^ C.Wd := by
    have := hN.BW
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine Hx.hs (Hs.then (idxP_spec (C := C) vTS0 vTW0 l0P a0I l0N (by decide) (by decide) (by decide) (by decide)
    (by decide) s T0 W0 X0 a Y0 (by rw [ev _ (by decide) (by decide)]; exact hN.hT0)
    (by rw [ev _ (by decide) (by decide)]; exact hN.hW0) (by rw [ev _ (by decide) (by decide)]; exact hN.hx0) h0
    (by rw [ev _ (by decide) (by decide)]; exact hN.hy0) i1 (by omega)) (fun s1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  have C1 := h.step p3 p2 (by decide)
  have hrc1 := C1.rc sN
  rw [C1.ram] at hrc1
  refine Hs.then (cs_fetchN C1 prd b0 (by decide) (by decide) (by decide) (by rw [p1, C1.ram]; exact i2)
    (by rw [p1]; omega)) (fun s2 ⟨q1, q2, q3⟩ k2 hk2 => ?_)
  rw [p1, C1.ram] at q1
  rw [p1] at hk2
  have F2 : Fr s s2 bitsT := Fr.trans (p2.weaken (by decide)) (q3.weaken (by decide))
  have c2 := q2.cst
  have s2K : s2.env vKd = K := by rw [q2.fr vKd (by decide) (by decide), hN.hK]
  -- the pair bit
  refine Hs.then (t := 9 + (6 * (e.ram sN).length + 9) + 3 + 1) (Hs.ite (c := .eq vKd v1) (show vKd ≠ v1 by decide)
    (R := fun s' => s'.env b0 = b0f (e.ram sN) T0 W0 X0 Y0 a + (if K = 1 then b0f (e.ram sN) T1 W1 X1 Y1 b else 0) ∧
      CS e Rk s' ∧ Fr s2 s' bitsT) (fun he => ?_) (fun he => ?_)) (fun s3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  · have hK1 : K = 1 := by simpa [Cnd.eval, c2.one, s2K] using he
    obtain ⟨j1, j2, j3⟩ := hN.i1 hK1 b hb
    have hw1 := hN.w1 hK1 (by omega)
    have ev2 : ∀ x, ¬ FragVar x → x ≠ vCnt → s2.env x = e.env x := q2.fr
    refine Hx.hs (Hs.then (idxP_spec (C := C) vTS1 vTW1 l1P a1I l1N (by decide) (by decide) (by decide)
      (by decide) (by decide) s2 T1 W1 X1 b Y1 (by rw [ev2 _ (by decide) (by decide)]; exact hN.hT1)
      (by rw [ev2 _ (by decide) (by decide)]; exact hN.hW1) (by rw [ev2 _ (by decide) (by decide)]; exact hN.hx1)
      (by rw [F2 a1I (by decide)]; exact h1) (by rw [ev2 _ (by decide) (by decide)]; exact hN.hy1) j1 (by omega))
      (fun s4 ⟨u1, u2, u3⟩ k4 hk4 => ?_))
    have C4 := q2.step u3 u2 (by decide)
    have hrc4 := C4.rc sN
    rw [C4.ram] at hrc4
    refine Hs.then (cs_fetchN C4 prd b1 (by decide) (by decide) (by decide) (by rw [u1, C4.ram]; exact j2)
      (by rw [u1]; omega)) (fun s5 ⟨v1', v2', v3'⟩ k5 hk5 => ?_)
    rw [u1, C4.ram] at v1'
    rw [u1] at hk5
    have s5b0 : s5.env b0 = b0f (e.ram sN) T0 W0 X0 Y0 a := by
      rw [v3' b0 (by decide), u2 b0 (by decide)]; exact q1
    have hb0' : b0f (e.ram sN) T0 W0 X0 Y0 a ≤ 1 := i3
    refine Hs.last (o_add b0 b1 s5 (by decide) (by rw [s5b0, v1']; omega))
      (fun s6 ⟨w1, w2, w3⟩ k6 hk6 => ⟨⟨by rw [w1, s5b0, v1', if_pos hK1]; rfl, v2'.step w3 w2 (by decide),
        Fr.trans (u2.weaken (by decide)) (Fr.trans (v3'.weaken (by decide)) (w2.weaken (by decide)))⟩, by omega⟩)
  · have hK1 : K ≠ 1 := by simpa [Cnd.eval, c2.one, s2K] using he
    refine Hs.mono (skip_spec (C := C) s2) (by omega) ?_
    rintro s' rfl
    refine ⟨by rw [DS.set_env_ne _ _ (by decide), q1, if_neg hK1, Nat.add_zero]; rfl, q2.set (by decide) 0, Fr.set s2 0 (by decide)⟩
  -- the parity bits
  have c3 := r2.cst
  have s3K : s3.env vKd = K := by rw [r2.fr vKd (by decide) (by decide), hN.hK]
  refine Hs.last (t := 4) (Hs.ite (c := .eq vKd v2) (show vKd ≠ v2 by decide)
    (R := fun s' => s'.env b0 = b0f (e.ram sN) T0 W0 X0 Y0 a + (if K = 1 then b0f (e.ram sN) T1 W1 X1 Y1 b else 0) +
      (if K = 2 then OP + PI else 0) ∧ CS e Rk s' ∧ Fr s3 s' bitsT) (fun he => ?_) (fun he => ?_))
    (fun s4 ⟨u1, u2, u3⟩ k4 hk4 => ⟨⟨u1, u2, Fr.trans F2 (Fr.trans r3 u3)⟩, by unfold bitsCost; omega⟩)
  · have hK2 : K = 2 := by simpa [Cnd.eval, c3.two, s3K] using he
    have hb1 : b0f (e.ram sN) T0 W0 X0 Y0 a ≤ 1 := i3
    have hsm := hN.small
    have r1' : s3.env b0 ≤ 1 := by rw [r1, if_neg (by omega)]; exact hb1
    refine Hx.hs (Hs.then (o_add b0 vOP s3 (by decide) (by
      rw [r2.fr vOP (by decide) (by decide), hN.hOP]; have := hN.BW; have : 4 ≤ 2 ^ C.Wd := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)) (fun s4 ⟨u1, u2, u3⟩ k4 hk4 => ?_))
    rw [r2.fr vOP (by decide) (by decide), hN.hOP] at u1
    have C4 := r2.step u3 u2 (by decide)
    have h4 : 4 ≤ 2 ^ C.Wd := by
      have := hN.BW
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine Hs.last (o_add b0 pI s4 (by decide) (by rw [u1, C4.fr pI (by decide) (by decide), hN.hPI]; omega))
      (fun s5 ⟨v1', v2', v3'⟩ k5 hk5 => ⟨⟨?_, C4.step v3' v2' (by decide),
        Fr.trans (u2.weaken (by decide)) (v2'.weaken (by decide))⟩, by omega⟩)
    rw [v1', u1, C4.fr pI (by decide) (by decide), hN.hPI, r1, if_pos hK2]; ring
  · have hK2 : K ≠ 2 := by simpa [Cnd.eval, c3.two, s3K] using he
    refine Hs.mono (skip_spec (C := C) s3) (by omega) ?_
    rintro s' rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide), r1, if_neg hK2, Nat.add_zero], r2.set (by decide) 0, Fr.set s3 0 (by decide)⟩

end NearCubicGates.Close.Cells.SystemsPhase
