import Proof.Gates.Cells.FormsAll

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

/-- The cost bound of the forms phase (opaque for linear arithmetic). -/
@[irreducible] def formsCost (L n : ℕ) : ℕ := 1000 * (L + 1) * (L + n + 1)

theorem formsCost_ge (L n : ℕ) : 2 * roleCost L n + 30 * L + 300 ≤ formsCost L n := by
  rw [roleCost_eq]; unfold formsCost; nlinarith

section F
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

include hadm hs hw in
/-- **The forms phase of a cell.** -/
theorem formsP_spec (i Big : ℕ) (hBig : ∀ x ∈ cellN c p wt, natBitLength x ≤ Big)
    (hWd : 3 * Big + 6 * c.n + 20 ≤ C.Wd) (a : DS VV MM) (hpre : FormsPre c p wt i a) :
    Hs C formsP a (a.rc sE + a.rc sX + a.rc sZb + a.rc sN + a.rc sB + a.rc sG +
      formsCost (cellN c p wt).length c.n) (fun b =>
      b.ram sE = ctrL c p wt (cellOf wt.I i) ∧ b.rc sE = (ctrL c p wt (cellOf wt.I i)).length ∧
      b.ram sX = kxL c p wt (cellOf wt.I i) ∧ b.rc sX = (kxL c p wt (cellOf wt.I i)).length ∧
      b.ram sN = a.ram sN ∧ b.rc sN ≤ (cellN c p wt).length ∧ b.rc sB = 0 ∧ b.rc sG = 2 * p.J ∧
      b.rc sZb = 0 ∧ (b.ram sB).length ≤ max (a.ram sB).length (cellN c p wt).length ∧
      (b.ram sG).length ≤ max (a.ram sG).length (2 * p.J) ∧ 2 * p.J ≤ (b.ram sG).length ∧
      b.ram sZb = a.ram sZb ∧ Agr a b formsMs formsT) := by
  obtain ⟨hc, hN, hzb, hn, hRC, hJ, hB1, hWS, hFS, heL, hxL⟩ := hpre
  have hrc : roleCount c.kind = 1 ∨ roleCount c.kind = 2 := by cases c.kind <;> simp [roleCount]
  have hJ1 := hs.J_pos
  have hLlt := cellN_len_lt c p wt hadm hs w hw
  have hL4 : (cellN c p wt).length + 4 < 2 ^ C.Wd := by
    have : 2 ^ (5 * c.n + 7) * 2 ^ 1 ≤ 2 ^ C.Wd := by rw [← pow_add]; exact pw_mono (by omega)
    have : 2 ^ 7 ≤ 2 ^ (5 * c.n + 7) := pw_mono (by omega)
    omega
  have hnw : 2 * c.n + 3 < 2 ^ C.Wd := by
    have h1 : c.n < 2 ^ c.n := Nat.lt_two_pow_self
    have h2 : 2 ^ c.n * 2 ^ 2 ≤ 2 ^ C.Wd := by rw [← pow_add]; exact pw_mono (by omega)
    omega
  have hdf := Call.drop_factors c p wt
  have hfsl := drop_eq_len hdf (by simp)
  simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at hfsl
  have hnf := nfactors_eq c p wt hadm hs w hw
  have hJL : p.J ≤ (cellN c p wt).length := by omega
  have hP := formsCost_ge (cellN c p wt).length c.n
  -- initialisation
  refine Hs.bseq (formsInit_spec (C := C) a hc) (by omega) (fun e1 ⟨i1, i2, i3, i4, i5, i6, ag1⟩ => ?_)
  have e1c : Cst e1 := Cst.of_fr hc ag1.fr (by decide)
  have e1N : e1.rc sN = a.rc sN := ag1.rc sN (by decide)
  -- role 0 set-up
  have hb0 : (e1.ram sN).drop (e1.env xB) = circN c.first ++ (circN c.second ++ [c.parity.length] ++ c.parity ++
      ratN c.radius ++ (paramsN p ++ witN c p wt)) := by rw [i3, hN, i1]; exact idx_circ1 c p wt
  have hix0 := circ_idx c.first (cellN c p wt) _ 2 (idx_circ1 c p wt)
  have hsp0 := setP_spec (C := C) e1 c.first _ (by rw [ag1.fr gN (by decide)]; exact hn) hb0 (by rw [i1]; omega) hnw
  refine Hs.bseq (Hs.mono hsp0 (show e1.rc sN + 5 * e1.env xB + 9 + 19 + (e1.env xB + 1 + 5 * (e1.env xB + 1 +
      c.first.gates.length * (2 * c.n + 3)) + 9) + 5 + 3 ≤ a.rc sN + 6 * (cellN c p wt).length + 80 by
      rw [e1N, i1]; omega) (fun _ h => h)) (by omega) (fun e2 ⟨s1, s2, s3, s4, s5, s6, s7, s8, ag2⟩ => ?_)
  have e2c : Cst e2 := Cst.of_fr e1c ag2.fr (by decide)
  have f2 : ∀ y, y ∉ formsT → e2.env y = a.env y := fun y hy =>
    (ag2.fr y (fun h => hy (by simp [formsT, h]))).trans (ag1.fr y hy)
  -- role 0
  have hr0 : 0 < roleCount c.kind := roleCount_pos c.kind
  have hrv0 := roleP_val (C := C) c p wt hadm hs w hw i Big hBig hWd ⟨0, hr0⟩ e2 e2c
    (by rw [s8, i3, hN]) (by rw [ag2.ram sZb (by decide), i3, hzb]) (by rw [ag2.rc sZb (by decide), i6])
    (by rw [f2 gN (by decide), hn]) (by rw [ag2.fr fR (by decide), i2]) (by rw [f2 gRC (by decide), hRC])
    (by rw [f2 gJ (by decide), hJ]) 2 _ (by simpa [circ] using idx_circ1 c p wt) (by rw [s2, i1])
    (by simpa [circ] using s1) (by rw [s3, i1]; simp [circ]) (by simpa [circ] using s4)
    (by rw [s5, ag1.fr gWS (by decide), hWS]) (by rw [s6, ag1.fr gFS (by decide), hFS])
    (a.ram sE) [] (by rw [ag2.ram sE (by decide), i3, wr_nil]) (by rw [ag2.rc sE (by decide), i4]; rfl)
    (a.ram sX) [] (by rw [ag2.ram sX (by decide), i3, wr_nil]) (by rw [ag2.rc sX (by decide), i5]; rfl)
  have hix0' : 2 + 1 + c.first.gates.length * (2 * c.n + 3) + 1 ≤ (cellN c p wt).length := by omega
  have q1 : e2.rc sN = 2 + 1 + c.first.gates.length * (2 * c.n + 3) + 1 := by rw [s7, i1]
  have q2 : e2.rc sB = a.rc sB := by rw [ag2.rc sB (by decide), ag1.rc sB (by decide)]
  have q3 : e2.rc sG = a.rc sG := by rw [ag2.rc sG (by decide), ag1.rc sG (by decide)]
  have hcost : e2.rc sN + e2.rc sB + e2.rc sG + roleCost (cellN c p wt).length c.n ≤
      (cellN c p wt).length + a.rc sB + a.rc sG + roleCost (cellN c p wt).length c.n := by
    rw [q1, q2, q3]; omega
  refine Hs.bseq (Hs.mono hrv0 hcost (fun _ h => h)) (by omega)
    (fun e3 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, ag3⟩ => ?_)
  have e3c : Cst e3 := Cst.of_fr e2c ag3.fr (by decide)
  have f3 : ∀ y, y ∉ formsT → e3.env y = a.env y := fun y hy =>
    (ag3.fr y (fun h => hy (by simp [formsT, h]))).trans (f2 y hy)
  have e3RC : e3.env gRC = roleCount c.kind := by rw [f3 gRC (by decide), hRC]
  have e3fR : e3.env fR = 0 := by
    rw [ag3.fr fR (by decide), ag2.fr fR (by decide), i2]
  have e3N : e3.ram sN = cellN c p wt := by rw [r5, s8, i3, hN]
  have seg0 := seg_length p.J (fun j => ctr c p wt (cellOf wt.I i) (⟨0, hr0⟩, j))
  have ag13 : Agr a e3 formsMs formsT := (ag1.weaken (by decide) (by decide)).trans
    ((ag2.weaken (by decide) (by decide)).trans (ag3.weaken (by decide) (by decide)))
  have e3Zb : e3.ram sZb = zbL wt.I i := by rw [ag3.ram sZb (by decide), ag2.ram sZb (by decide), i3, hzb]
  have e3Zc : e3.rc sZb = 0 := by rw [ag3.rc sZb (by decide), ag2.rc sZb (by decide), i6]
  have e3Bl : (e3.ram sB).length ≤ max (a.ram sB).length (cellN c p wt).length := by
    rw [ag2.ram sB (by decide), i3] at r7; exact r7
  have e3Gl : (e3.ram sG).length ≤ max (a.ram sG).length (2 * p.J) := by
    rw [ag2.ram sG (by decide), i3] at r8; exact r8
  have hFSJ : iPsi (cellN c p wt) + 24 + nPr (cellN c p wt) + p.J ≤ (cellN c p wt).length := by omega
  have hseg0 : ((List.finRange p.J).flatMap fun j => pairOf (ctr c p wt (cellOf wt.I i) (⟨0, hr0⟩, j))).length =
      2 * p.J := seg_length p.J _
  refine Hs.mono (Hs.ite (t := 16 * (cellN c p wt).length + 60 + roleCost (cellN c p wt).length c.n)
    (show gRC ≠ v2 by decide) (fun ht => ?_) (fun ht => ?_)) (by omega) (fun _ h => h)
  · -- two roles
    simp only [Cnd.eval, e3RC, e3c.two, decide_eq_true_eq] at ht
    have hr1 : 1 < roleCount c.kind := by omega
    have e3B1 : e3.env gB1 = iG2 (cellN c p wt) := by rw [f3 gB1 (by decide), hB1]
    refine Hs.bseq (role1Init_spec (C := C) e3 (by rw [e3fR]; omega)) (by omega)
      (fun e4 ⟨u1, u2, u3, u4, ag4⟩ => ?_)
    have e4c : Cst e4 := Cst.of_fr e3c ag4.fr (by decide)
    have hb1 : (e4.ram sN).drop (e4.env xB) = circN c.second ++ ([c.parity.length] ++ c.parity ++
        ratN c.radius ++ (paramsN p ++ witN c p wt)) := by
      rw [u3, e3N, u2, e3B1]; exact Call.drop_iG2 c p wt
    have hix1 := circ_idx c.second (cellN c p wt) _ _ (Call.drop_iG2 c p wt)
    have hsp1 := setP_spec (C := C) e4 c.second _ (by rw [ag4.fr gN (by decide), f3 gN (by decide), hn]) hb1
      (by rw [u2, e3B1]; omega) hnw
    have hc1 : e4.rc sN + 5 * e4.env xB + 9 + 19 + (e4.env xB + 1 + 5 * (e4.env xB + 1 +
        c.second.gates.length * (2 * c.n + 3)) + 9) + 5 + 3 ≤ 12 * (cellN c p wt).length + 50 := by
      rw [u4, r11, u2, e3B1]; omega
    refine Hs.bseq (Hs.mono hsp1 hc1 (fun _ h => h)) (by omega)
      (fun e5 ⟨t1, t2, t3, t4, t5, t6, t7, t8, ag5⟩ => ?_)
    have e5c : Cst e5 := Cst.of_fr e4c ag5.fr (by decide)
    have f5 : ∀ y, y ∉ formsT → e5.env y = a.env y := fun y hy =>
      (ag5.fr y (fun h => hy (by simp [formsT, h]))).trans ((ag4.fr y hy).trans (f3 y hy))
    have e5E : e5.ram sE = e3.ram sE := by rw [ag5.ram sE (by decide), u3]
    have e5Ec : e5.rc sE = e3.rc sE := by rw [ag5.rc sE (by decide), u4]
    have e5X : e5.ram sX = e3.ram sX := by rw [ag5.ram sX (by decide), u3]
    have e5Xc : e5.rc sX = e3.rc sX := by rw [ag5.rc sX (by decide), u4]
    have hrv1 := roleP_val (C := C) c p wt hadm hs w hw i Big hBig hWd ⟨1, hr1⟩ e5 e5c
      (by rw [t8, u3, e3N]) (by rw [ag5.ram sZb (by decide), u3, e3Zb]) (by rw [ag5.rc sZb (by decide), u4, e3Zc])
      (by rw [f5 gN (by decide), hn]) (by rw [ag5.fr fR (by decide), u1, e3fR])
      (by rw [f5 gRC (by decide), hRC]) (by rw [f5 gJ (by decide), hJ]) (iG2 (cellN c p wt)) _
      (by simpa [circ] using Call.drop_iG2 c p wt) (by rw [t2, u2, e3B1]) (by simpa [circ] using t1)
      (by rw [t3, u2, e3B1]; simp [circ]) (by simpa [circ] using t4)
      (by rw [t5, ag4.fr gWS (by decide), f3 gWS (by decide), hWS])
      (by rw [t6, ag4.fr gFS (by decide), f3 gFS (by decide), hFS])
      (a.ram sE) ((List.finRange p.J).flatMap fun j => pairOf (ctr c p wt (cellOf wt.I i) (⟨0, hr0⟩, j)))
      (by rw [e5E, r1, List.nil_append]) (by rw [e5Ec, r2, hseg0]; simp)
      (a.ram sX) (pairOf (stageForm c wt 0 (p.J - 1) (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) ++
        pairOf (scoreForm c 0 (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))))
      (by rw [e5X, r3, List.nil_append]) (by rw [e5Xc, r4]; simp [pairOf])
    have hc2 : e5.rc sN + e5.rc sB + e5.rc sG + roleCost (cellN c p wt).length c.n ≤
        3 * (cellN c p wt).length + roleCost (cellN c p wt).length c.n := by
      rw [t7, ag5.rc sB (by decide), ag5.rc sG (by decide), u4, r6, r10, u2, e3B1]; omega
    refine Hs.mono (Hs.mono hrv1 hc2 (fun _ h => h)) (by omega) ?_
    rintro b ⟨v1', v2', v3', v4', v5', v6', v7', v8', v9', v10', v11', ag6⟩
    have hctr : ctrL c p wt (cellOf wt.I i) =
        ((List.finRange p.J).flatMap fun j => pairOf (ctr c p wt (cellOf wt.I i) (⟨0, hr0⟩, j))) ++
        ((List.finRange p.J).flatMap fun j => pairOf (ctr c p wt (cellOf wt.I i) (⟨1, hr1⟩, j))) :=
      flat_two ht _
    have hkx : kxL c p wt (cellOf wt.I i) =
        (pairOf (stageForm c wt 0 (p.J - 1) (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) ++
          pairOf (scoreForm c 0 (extend wt.I (cellOf wt.I i) (zeroPoint wt.I)))) ++
        (pairOf (stageForm c wt 1 (p.J - 1) (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) ++
          pairOf (scoreForm c 1 (extend wt.I (cellOf wt.I i) (zeroPoint wt.I)))) :=
      flat_two ht _
    have hs1 := seg_length p.J (fun j => ctr c p wt (cellOf wt.I i) (⟨1, hr1⟩, j))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, v6', v10', ?_, ?_, ?_, v9', ?_, ?_⟩
    · rw [v1', ← hctr]; exact wr_full _ _ heL
    · rw [v2', hctr, List.length_append, hseg0, hs1]
    · rw [v3', ← hkx]; exact wr_full _ _ hxL
    · rw [v4', hkx]; simp [pairOf]
    · rw [v5', t8, u3, e3N, hN]
    · rw [v11']; exact hFSJ
    · rw [ag6.rc sZb (by decide), ag5.rc sZb (by decide), u4, e3Zc]
    · have := v7'; rw [ag5.ram sB (by decide), u3] at this; omega
    · have := v8'; rw [ag5.ram sG (by decide), u3] at this; omega
    · rw [ag6.ram sZb (by decide), ag5.ram sZb (by decide), u3, e3Zb, hzb]
    · exact ag13.trans ((ag4.weaken (by decide) (by decide)).trans ((ag5.weaken (by decide) (by decide)).trans
        (ag6.weaken (by decide) (by decide))))
  · -- one role
    simp only [Cnd.eval, e3RC, e3c.two, decide_eq_false_iff_not] at ht
    have h1 : roleCount c.kind = 1 := by omega
    refine Hs.mono (skip_spec e3) (by omega) ?_
    rintro b rfl
    have hctr : ctrL c p wt (cellOf wt.I i) =
        (List.finRange p.J).flatMap fun j => pairOf (ctr c p wt (cellOf wt.I i) (⟨0, hr0⟩, j)) := flat_one h1 _
    have hkx : kxL c p wt (cellOf wt.I i) =
        pairOf (stageForm c wt 0 (p.J - 1) (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) ++
          pairOf (scoreForm c 0 (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) := flat_one h1 _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, r6, r10, ?_, ?_, ?_, r9, ?_, ?_⟩
    · rw [DS.set_ram, r1, List.nil_append, ← hctr]; exact wr_full _ _ heL
    · rw [DS.set_rc, r2, hctr, hseg0]; simp
    · rw [DS.set_ram, r3, List.nil_append, ← hkx]; exact wr_full _ _ hxL
    · rw [DS.set_rc, r4, hkx]; simp [pairOf]
    · rw [DS.set_ram, e3N, hN]
    · rw [DS.set_rc, r11]; exact hFSJ
    · rw [DS.set_rc, e3Zc]
    · exact e3Bl
    · exact e3Gl
    · rw [DS.set_ram, e3Zb, hzb]
    · exact ag13.trans (Agr.set _ _ _ (by decide))

end F

end NearCubicGates.Close.Cells
