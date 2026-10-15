import Proof.Gates.CellsGatherK.Key2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.QueryKey

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def fetchP : St VV MM :=
  .seq (.op (.copy kX kI)) (.seq (.op (.add kX kI)) (.seq (fetch sE kX kA) (.seq (.op (.inc kX)) (fetch sE kX kB))))

def fetchT : List (Fin VV) := [kX, kA, kB, c0, vJ]

theorem fetchP_spec (a : DS VV MM) (idx : ℕ) (hI : a.env kI = idx) (hlen : 2 * idx + 1 < (a.ram sE).length)
    (hE : a.rc sE ≤ (a.ram sE).length) (hW : 2 * idx + 2 < 2 ^ C.Wd) :
    Hs C fetchP a (12 * (a.ram sE).length + 40) (fun b =>
      b.env kA = (a.ram sE).getD (2 * idx) 0 ∧ b.env kB = (a.ram sE).getD (2 * idx + 1) 0 ∧ KG fetchT a b) := by
  obtain ⟨s1, n1, e1, hn1, r1, f1, m1⟩ := o_copy (C := C) kX kI a (by decide)
  have g1 : s1.env kI = idx := by rw [f1.ev (by decide), hI]
  obtain ⟨s2, n2, e2, hn2, r2, f2, m2⟩ := o_add (C := C) kX kI s1 (by decide) (by rw [r1, g1, hI]; omega)
  have hx2 : s2.env kX = 2 * idx := by rw [r2, r1, g1, hI]; ring
  have hm2 : Same a s2 := m1.trans m2
  obtain ⟨s3, n3, e3, hn3, r3, f3, k3, c3⟩ := o_fetch (C := C) sE kX kA (by decide) (by decide) (by decide) s2
    (by rw [hx2, hm2.ram]; omega) (by rw [hx2]; omega)
  have hx3 : s3.env kX = 2 * idx := by rw [f3.ev (by decide), hx2]
  obtain ⟨s4, n4, e4, hn4, r4, f4, m4⟩ := o_inc (C := C) kX s3 (by rw [hx3]; omega)
  have hram4 : s4.ram = a.ram := by rw [m4.ram, k3.ram, hm2.ram]
  have hx4 : s4.env kX = 2 * idx + 1 := by rw [r4, hx3]
  obtain ⟨s5, n5, e5, hn5, r5, f5, k5, c5⟩ := o_fetch (C := C) sE kX kB (by decide) (by decide) (by decide) s4
    (by rw [hx4, hram4]; omega) (by rw [hx4]; omega)
  have hrc4 : s4.rc sE = 2 * idx + 1 := by rw [m4.rc, c3, hx2]; simp
  refine ⟨s5, n1 + (n2 + (n3 + (n4 + n5 + 1) + 1) + 1) + 1,
    Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 e5))), ?_, ?_, ?_, ?_⟩
  · rw [hm2.rc] at hn3; rw [hx2] at hn3; rw [hrc4, hx4] at hn5; omega
  · rw [f5.ev (by decide), f4.ev (by decide), r3, hx2, hm2.ram]
  · rw [r5, hx4, hram4]
  · refine ⟨?_, by rw [k5.ram, hram4], fun m hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((((f1.weaken (by decide)).trans (f2.weaken (by decide))).trans (f3.weaken (by decide))).trans
        (f4.weaken (by decide))).trans (f5.weaken (by decide))
    · rw [c5, Function.update_of_ne hm, m4.rc, c3, Function.update_of_ne hm, hm2.rc]
    · rw [c5, Function.update_self, hx4, k5.ram, hram4]; omega
    · rw [k5.ip, m4.ip, k3.ip, hm2.ip]
    · rw [k5.out, m4.out, k3.out, hm2.out]
    · rw [k5.kin, m4.kin, k3.kin, hm2.kin]
    · rw [k5.kout, m4.kout, k3.kout, hm2.kout]
    · rw [k5.kc, m4.kc, k3.kc, hm2.kc]

def fieldP : St VV MM :=
  .seq (.op (.dm kA kQ t6 t7)) (.seq (.op (.dm kB kQ t6 t8)) (.seq (.op (.dm vHE kQ t6 t9))
    (.seq (.op (.copy kA t7)) (.seq (.op (.add kA kD)) (.seq (.op (.inc kA)) (.seq (.op (.add kA kQ))
    (.seq (.op (.add kA kQ)) (.seq (.op (.copy kB t8)) (.seq (.op (.add kB t9)) (.seq (.op (.sub kA kB))
    (.op (.dm kA kQ t6 kD))))))))))))

def fieldT : List (Fin VV) := [t6, t7, t8, t9, kA, kB, kD]

theorem fieldP_spec (a : DS VV MM) (P N h d q : ℕ) (hP : a.env kA = P) (hN : a.env kB = N) (hh : a.env vHE = h)
    (hd : a.env kD = d) (hq : a.env kQ = q) (hq0 : 0 < q) (hW : 4 * q + d + 2 < 2 ^ C.Wd) :
    Hs C fieldP a 30 (fun b => b.env kD = (P % q + d + 1 + 2 * q - (N % q + h % q)) % q ∧ Fr a b fieldT ∧
      Same a b) := by
  have hq2 : 2 * q ≤ 2 ^ C.Wd := by omega
  obtain ⟨s1, n1, e1, hn1, -, r1, f1, m1⟩ := o_dm (C := C) kA kQ t6 t7 a (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hq]; exact hq0) (by rw [hq]; exact hq2)
  have g1 : ∀ x, x ≠ t6 → x ≠ t7 → s1.env x = a.env x := fun x h1 h2 => f1.ev (by simp; exact ⟨h1, h2⟩)
  obtain ⟨s2, n2, e2, hn2, -, r2, f2, m2⟩ := o_dm (C := C) kB kQ t6 t8 s1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [g1 kQ (by decide) (by decide), hq]; exact hq0)
    (by rw [g1 kQ (by decide) (by decide), hq]; exact hq2)
  have g2 : ∀ x, x ≠ t6 → x ≠ t7 → x ≠ t8 → s2.env x = a.env x := fun x h1 h2 h3 => by
    rw [f2.ev (by simp; exact ⟨h1, h3⟩)]; exact g1 x h1 h2
  obtain ⟨s3, n3, e3, hn3, -, r3, f3, m3⟩ := o_dm (C := C) vHE kQ t6 t9 s2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [g2 kQ (by decide) (by decide) (by decide), hq]; exact hq0)
    (by rw [g2 kQ (by decide) (by decide) (by decide), hq]; exact hq2)
  have g3 : ∀ x, x ≠ t6 → x ≠ t7 → x ≠ t8 → x ≠ t9 → s3.env x = a.env x := fun x h1 h2 h3 h4 => by
    rw [f3.ev (by simp; exact ⟨h1, h4⟩)]; exact g2 x h1 h2 h3
  have v7 : s3.env t7 = P % q := by
    rw [f3.ev (by decide), f2.ev (by decide), r1, hP, hq]
  have v8 : s3.env t8 = N % q := by
    rw [f3.ev (by decide), r2, g1 kB (by decide) (by decide), g1 kQ (by decide) (by decide), hN, hq]
  have v9 : s3.env t9 = h % q := by
    rw [r3, g2 vHE (by decide) (by decide) (by decide), g2 kQ (by decide) (by decide) (by decide), hh, hq]
  have vq : s3.env kQ = q := by rw [g3 kQ (by decide) (by decide) (by decide) (by decide), hq]
  have vd : s3.env kD = d := by rw [g3 kD (by decide) (by decide) (by decide) (by decide), hd]
  have hPq := Nat.mod_lt P hq0
  have hNq := Nat.mod_lt N hq0
  have hhq := Nat.mod_lt h hq0
  obtain ⟨s4, n4, e4, hn4, r4, f4, m4⟩ := o_copy (C := C) kA t7 s3 (by decide)
  obtain ⟨s5, n5, e5, hn5, r5, f5, m5⟩ := o_add (C := C) kA kD s4 (by decide)
    (by rw [r4, v7, f4.ev (by decide), vd]; omega)
  obtain ⟨s6, n6, e6, hn6, r6, f6, m6⟩ := o_inc (C := C) kA s5 (by rw [r5, r4, v7, f4.ev (by decide), vd]; omega)
  have hq6 : s6.env kQ = q := by rw [f6.ev (by decide), f5.ev (by decide), f4.ev (by decide), vq]
  have hA6 : s6.env kA = P % q + d + 1 := by rw [r6, r5, r4, v7, f4.ev (by decide), vd]
  obtain ⟨s7, n7, e7, hn7, r7, f7, m7⟩ := o_add (C := C) kA kQ s6 (by decide) (by rw [hA6, hq6]; omega)
  have hq7 : s7.env kQ = q := by rw [f7.ev (by decide), hq6]
  obtain ⟨s8, n8, e8, hn8, r8, f8, m8⟩ := o_add (C := C) kA kQ s7 (by decide) (by rw [r7, hA6, hq6, hq7]; omega)
  have hA8 : s8.env kA = P % q + d + 1 + 2 * q := by rw [r8, r7, hA6, hq6, hq7]; ring
  have h8 : ∀ x, x ≠ kA → s8.env x = s3.env x := fun x hx => by
    rw [f8.ev (by simp; exact hx), f7.ev (by simp; exact hx), f6.ev (by simp; exact hx),
      f5.ev (by simp; exact hx), f4.ev (by simp; exact hx)]
  obtain ⟨s9, n9, e9, hn9, r9, f9, m9⟩ := o_copy (C := C) kB t8 s8 (by decide)
  obtain ⟨s10, n10, e10, hn10, r10, f10, m10⟩ := o_add (C := C) kB t9 s9 (by decide)
    (by rw [r9, h8 t8 (by decide), v8, f9.ev (by decide), h8 t9 (by decide), v9]; omega)
  have hB10 : s10.env kB = N % q + h % q := by
    rw [r10, r9, h8 t8 (by decide), v8, f9.ev (by decide), h8 t9 (by decide), v9]
  have hA10 : s10.env kA = P % q + d + 1 + 2 * q := by rw [f10.ev (by decide), f9.ev (by decide), hA8]
  obtain ⟨s11, n11, e11, hn11, r11, f11, m11⟩ := o_sub (C := C) kA kB s10 (by decide) (by rw [hA10, hB10]; omega)
  have hq11 : s11.env kQ = q := by
    rw [f11.ev (by decide), f10.ev (by decide), f9.ev (by decide), h8 kQ (by decide), vq]
  obtain ⟨s12, n12, e12, hn12, -, r12, f12, m12⟩ := o_dm (C := C) kA kQ t6 kD s11 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hq11]; exact hq0) (by rw [hq11]; exact hq2)
  refine ⟨s12, n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + n12 + 1) + 1) + 1) + 1) + 1)
    + 1) + 1) + 1) + 1) + 1) + 1, Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 (Ex.seq e6 (Ex.seq e7
    (Ex.seq e8 (Ex.seq e9 (Ex.seq e10 (Ex.seq e11 e12)))))))))), by omega, ?_, ?_, ?_⟩
  · rw [r12, r11, hA10, hB10, hq11]
  · intro y hy
    simp only [fieldT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hy
    rw [f12.ev (by simp; exact ⟨h1, h7⟩), f11.ev (by simp; exact h5), f10.ev (by simp; exact h6),
      f9.ev (by simp; exact h6), h8 y h5, g3 y h1 h2 h3 h4]
  · exact (((((((((((m1.trans m2).trans m3).trans m4).trans m5).trans m6).trans m7).trans m8).trans m9).trans
      m10).trans m11).trans m12)

end NearCubicGates.Close.Cells.QueryKey
