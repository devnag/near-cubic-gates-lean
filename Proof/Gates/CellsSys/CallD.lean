import Proof.Gates.CellsSys.CallC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def addB : St VV MM := .seq (.op (.dm b0 v2 qB b1)) (.ite (.eq b1 v1) (.op (.add vCnt mV)) skipS)

theorem addB_spec {e s : DS VV MM} {Rk : List Bool} (h : CS e Rk s) (S m V : ℕ) (hS : s.env b0 = S)
    (hm : s.env mV = m) (hV : s.env vCnt = V) (hw : V + m < 2 ^ C.Wd) (h4 : 4 ≤ 2 ^ C.Wd) :
    Hs C addB s 4 (fun s' => s'.env vCnt = V + (if S % 2 = 1 then m else 0) ∧ CS e Rk s' ∧
      Fr s s' [qB, b1, vCnt, vJ]) := by
  have c0' := h.cst
  refine Hx.hs (Hs.then (o_dm b0 v2 qB b1 s (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [c0'.two]; norm_num) (by rw [c0'.two]; omega)) (fun s1 ⟨p1, p2, p3, p4⟩ k1 hk1 => ?_))
  rw [hS, c0'.two] at p2
  have C1 := h.step p4 p3 (by decide)
  have s1m : s1.env mV = m := by rw [p3 mV (by decide)]; exact hm
  have s1V : s1.env vCnt = V := by rw [p3 vCnt (by decide)]; exact hV
  refine Hs.last (Hs.ite (c := .eq b1 v1) (show b1 ≠ v1 by decide)
    (R := fun s' => s'.env vCnt = V + (if S % 2 = 1 then m else 0) ∧ CS e Rk s' ∧ Fr s1 s' [qB, b1, vCnt, vJ])
    (t := 1) (fun he => ?_) (fun he => ?_)) (fun s2 ⟨q1, q2, q3⟩ k2 hk2 => ⟨⟨q1, q2,
      Fr.trans (p3.weaken (by decide)) q3⟩, by omega⟩)
  · have hb : S % 2 = 1 := by simpa [Cnd.eval, p2, C1.cst.one] using he
    refine Hs.mono (o_add vCnt mV s1 (by decide) (by rw [s1m, s1V]; exact hw)) le_rfl ?_
    rintro s2 ⟨r1, r2, r3⟩
    exact ⟨by rw [r1, s1m, s1V, if_pos hb], C1.step r3 r2 (by decide), r2.weaken (by decide)⟩
  · have hb : ¬ S % 2 = 1 := by simpa [Cnd.eval, p2, C1.cst.one] using he
    refine Hs.mono (skip_spec (C := C) s1) le_rfl ?_
    rintro s2 rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide), s1V, if_neg hb, Nat.add_zero], C1.set (by decide) 0,
      Fr.set s1 0 (by decide)⟩

def cptB : St VV MM := .seq rdNatK (.seq rdNatK (.seq (.op (.copy mV t3)) (.seq rdNatK (.seq bitsB addB))))

def cptT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, mV, prd, c0, b0, b1, qB, vCnt]

def cptCost (Bw LN : ℕ) : ℕ := 3 * (30 * Bw + 30) + bitsCost LN + 20

theorem nbl01 (v Bw : ℕ) (hv : v ≤ 1) (hB : 1 ≤ Bw) : natBitLength v ≤ Bw := nbl_small v hv Bw hB

theorem cptB_spec {e s : DS VV MM} {R : List Bool} {K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw : ℕ}
    {md : ℕ → ℕ → ℕ} (hN : CallN e K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw md C)
    (a b : ℕ) (ha : a < N0) (hb : b < N1) (h : CS e (rdW md a b ++ R) s) (h0 : s.env a0I = a) (h1 : s.env a1I = b)
    (V : ℕ) (hV : s.env vCnt = V) (hw : V + md a b < 2 ^ C.Wd) :
    Hs C cptB s (cptCost Bw (e.ram sN).length) (fun s' =>
      s'.env vCnt = V + cfn (e.ram sN) K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 md a b ∧ CS e R s' ∧ Fr s s' cptT) := by
  have h4W : 4 ≤ 2 ^ C.Wd := by
    have := hN.BW
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold rdW at h
  simp only [List.append_assoc] at h
  refine Hx.hs (Hs.then (cs_rd 0 Bw h (nbl01 0 Bw (by norm_num) hN.B1) hN.BW) (fun s1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  refine Hs.then (cs_rd (md a b) Bw p2 (hN.bm a ha b hb) hN.BW) (fun s2 ⟨q1, q2, q3⟩ k2 hk2 => ?_)
  refine Hs.then (o_copy mV t3 s2 (by decide)) (fun s3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  rw [q1] at r1
  refine Hs.then (cs_rd 1 Bw (q2.step r3 r2 (by decide)) (nbl01 1 Bw le_rfl hN.B1) hN.BW)
    (fun s4 ⟨u1, u2, u3⟩ k4 hk4 => ?_)
  have F4 : Fr s s4 cptT := Fr.trans (p3.weaken (by decide)) (Fr.trans (q3.weaken (by decide))
    (Fr.trans (r2.weaken (by decide)) (u3.weaken (by decide))))
  refine Hs.then (bitsB_spec hN u2 a b ha hb (by rw [F4 a0I (by decide)]; exact h0)
    (by rw [F4 a1I (by decide)]; exact h1)) (fun s5 ⟨v1', v2', v3'⟩ k5 hk5 => ?_)
  have s5m : s5.env mV = md a b := by rw [v3' mV (by decide), u3 mV (by decide)]; exact r1
  have s5V : s5.env vCnt = V := by
    rw [v3' vCnt (by decide), u3 vCnt (by decide), r2 vCnt (by decide), q3 vCnt (by decide), p3 vCnt (by decide)]
    exact hV
  refine Hs.last (addB_spec v2' _ (md a b) V v1' s5m s5V hw h4W) (fun s6 ⟨w1, w2, w3⟩ k6 hk6 =>
    ⟨⟨by rw [w1]; rfl, w2, Fr.trans F4 (Fr.trans (v3'.weaken (by decide)) (w3.weaken (by decide)))⟩, ?_⟩)
  unfold cptCost; omega

end NearCubicGates.Close.Cells.SystemsPhase
