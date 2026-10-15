import Proof.Gates.Cells.PackSpec
import Proof.Gates.Cells.Kit

set_option autoImplicit false

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `ratWord` of a natural number. -/
theorem ratWord_natCast (m : ℕ) : ratWord (m : ℚ) = natWord 0 ++ natWord m ++ natWord 1 := by
  simp [ratWord, Interfaces.intWord]

theorem add_two_lt_pow (w : ℕ) (hw : 3 ≤ w) : w + 2 < 2 ^ w := by
  induction w with
  | zero => omega
  | succ w ih =>
    rcases Nat.lt_or_ge w 3 with h | h
    · interval_cases w <;> simp_all
    · have := ih h; rw [pow_succ]; omega

theorem nbl_fit (C : Ctx) (v : ℕ) (hW : 3 ≤ C.Wd) (hv : v < 2 ^ C.Wd) :
    natBitLength v ≤ C.Wd ∧ natBitLength v + 2 < 2 ^ C.Wd := by
  have h1 := nbl_le_of_lt hv (by omega)
  exact ⟨h1, lt_of_le_of_lt (by omega) (add_two_lt_pow C.Wd hW)⟩

/-- **The output program.** -/
def outP : St VV MM :=
  .seq (.op (.zero t3)) (.seq emitNatO (.seq (.op (.copy t3 vCnt)) (.seq emitNatO
    (.seq (.op (.zero t3)) (.seq (.op (.inc t3)) (.seq emitNatO (.seq (.op (.copy t3 vUnc)) emitNatO)))))))

/-- The cost bound of `outP`. -/
def outCost (W : ℕ) : ℕ := 200 * W + 200

theorem t3_ne_vCnt : t3 ≠ vCnt := by decide
theorem t3_ne_vUnc : t3 ≠ vUnc := by decide
theorem vCnt_nmem : vCnt ∉ emitNatT := by decide
theorem vUnc_nmem : vUnc ∉ emitNatT := by decide
theorem t3_nmem : t3 ∉ emitNatT := by decide

theorem cst_set_t3 {a : DS VV MM} (hc : Cst a) (v : ℕ) : Cst (a.set t3 v) :=
  Cst.of_fr hc (Fr.set a v (T := [t3]) (by simp)) (by decide)

/-- One `emitNatO` of the value in `t3`, framed: what it prints and what it keeps. -/
theorem emit_step (C : Ctx) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (hv : a.env t3 < 2 ^ C.Wd) :
    Hs C emitNatO a (40 * C.Wd + 40) (fun b => b.out = a.out ++ natWord (a.env t3) ∧ Cst b ∧
      b.env vCnt = a.env vCnt ∧ b.env vUnc = a.env vUnc ∧ b.env t3 = a.env t3) := by
  obtain ⟨h1, h2⟩ := nbl_fit C _ hW hv
  refine Hs.mono (emitNatO_spec (C := C) a hc (by omega) h2) (by omega) ?_
  rintro b ⟨ho, -, hcb, hfr⟩
  exact ⟨ho, hcb, hfr vCnt vCnt_nmem, hfr vUnc vUnc_nmem, hfr t3 t3_nmem⟩

theorem seqC {C : Ctx} {s u : St VV MM} {a : DS VV MM} {t1 t2 T : ℕ} {R1 R2 : DS VV MM → Prop}
    (h1 : Hs C s a t1 R1) (h2 : ∀ b, R1 b → Hs C u b t2 R2) (hT : t1 + t2 + 1 ≤ T) : Hs C (.seq s u) a T R2 :=
  Hs.mono (Hs.seq h1 h2) hT (fun _ h => h)

/-- **`outP` prints `natWord 0 ++ natWord (vCnt) ++ natWord 1 ++ natWord (vUnc)`.** -/
theorem outP_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (hW : 3 ≤ C.Wd) (hm : b.env vCnt < 2 ^ C.Wd)
    (hu : b.env vUnc < 2 ^ C.Wd) :
    Hs C outP b (outCost C.Wd) (fun d => d.out = b.out ++ (natWord 0 ++ natWord (b.env vCnt) ++ natWord 1 ++
      natWord (b.env vUnc))) := by
  have h2 : (2 : ℕ) ≤ 2 ^ C.Wd := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  set E := 40 * C.Wd + 40 with hE
  -- zero t3
  refine seqC (t2 := 4 * E + 11) (hs_zero C t3 b) (fun b1 hb1 => ?_) (by unfold outCost; omega)
  subst hb1
  have c1 := cst_set_t3 hc 0
  -- emit natWord 0
  refine seqC (t2 := 3 * E + 10) (emit_step C _ c1 hW (by simp)) (fun b2 hb2 => ?_) (by omega)
  obtain ⟨o2, c2, m2, u2, -⟩ := hb2
  have m2' : b2.env vCnt = b.env vCnt := by rw [m2]; exact DS.set_env_ne _ _ t3_ne_vCnt.symm
  have u2' : b2.env vUnc = b.env vUnc := by rw [u2]; exact DS.set_env_ne _ _ t3_ne_vUnc.symm
  -- copy t3 vCnt
  refine seqC (t2 := 3 * E + 8) (hs_copy C t3 vCnt b2 t3_ne_vCnt) (fun b3 hb3 => ?_) (by omega)
  subst hb3
  have c3 := cst_set_t3 c2 (b2.env vCnt)
  -- emit natWord m
  refine seqC (t2 := 2 * E + 7) (emit_step C _ c3 hW (by simp; omega)) (fun b4 hb4 => ?_) (by omega)
  obtain ⟨o4, c4, -, u4, -⟩ := hb4
  have u4' : b4.env vUnc = b.env vUnc := by rw [u4, DS.set_env_ne _ _ t3_ne_vUnc.symm, u2']
  -- zero t3, inc t3
  refine seqC (t2 := 2 * E + 5) (hs_zero C t3 b4) (fun b5 hb5 => ?_) (by omega)
  subst hb5
  refine seqC (t2 := 2 * E + 3) (hs_inc C t3 _ (by simp; omega)) (fun b6 hb6 => ?_) (by omega)
  subst hb6
  have c6 : Cst ((b4.set t3 0).set t3 ((b4.set t3 0).env t3 + 1)) := cst_set_t3 (cst_set_t3 c4 0) _
  -- emit natWord 1
  refine seqC (t2 := E + 2) (emit_step C _ c6 hW (by simp; omega)) (fun b7 hb7 => ?_) (by omega)
  obtain ⟨o7, c7, -, u7, -⟩ := hb7
  have u7' : b7.env vUnc = b.env vUnc := by
    rw [u7, DS.set_env_ne _ _ t3_ne_vUnc.symm, DS.set_env_ne _ _ t3_ne_vUnc.symm, u4']
  -- copy t3 vUnc, emit natWord u
  refine seqC (t2 := E) (hs_copy C t3 vUnc b7 t3_ne_vUnc) (fun b8 hb8 => ?_) (by omega)
  subst hb8
  have c8 := cst_set_t3 c7 (b7.env vUnc)
  refine Hs.mono (emit_step C _ c8 hW (by simp; omega)) le_rfl ?_
  rintro d ⟨o9, -, -, -, -⟩
  simp only [o9, o7, o4, o2, DS.set_out, DS.env_set, Function.update_self, m2', u7']
  simp only [List.append_assoc]

end NearCubicGates.Close.CellsPack
