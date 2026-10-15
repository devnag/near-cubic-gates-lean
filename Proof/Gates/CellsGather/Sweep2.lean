import Proof.Gates.CellsGather.Sweep

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

def swInit : St VV MM :=
  .seq (.op (.rwM sA)) (.seq (.op (.zero gNQ)) (.seq (.op (.zero gLast)) (.seq (.op (.mul p2VW p2K gPZ))
    (.seq (.op (.mul p2K gPZ gPad)) (.seq (.op (.shl gPad)) (.op (.rdM sG gx)))))))

def sweepP : St VV MM := .seq swInit swLoop

variable {C : Ctx}

theorem swInit_spec (e : DS VV MM) (Z VW KW : ℕ) (R : List ℕ) (n : ℕ) (hVW : e.env p2VW = 2 ^ VW)
    (hKW : e.env p2K = 2 ^ KW) (hZ : Z = VW + KW) (hG : e.ram sG = R ++ List.replicate n (2 * 2 ^ KW * 2 ^ Z))
    (hn : 1 ≤ n) (hrcG : e.rc sG = 0) (hW : 2 * (2 ^ KW * 2 ^ Z) < 2 ^ C.Wd) :
    Hs C swInit e (e.rc sA + 13) (fun b => SwI Z VW R n (2 * 2 ^ KW * 2 ^ Z) e 0 b) := by
  have hZp : 2 ^ VW * 2 ^ KW = 2 ^ Z := by rw [hZ, pow_add]
  have hKZ : 2 ^ KW ≤ 2 ^ KW * 2 ^ Z := Nat.le_mul_of_pos_right _ (by positivity)
  have hZK : 2 ^ Z ≤ 2 ^ KW * 2 ^ Z := Nat.le_mul_of_pos_left _ (by positivity)
  obtain ⟨s1, n1, e1, hn1, h1⟩ := hs_rwM C sA e
  subst h1
  obtain ⟨s2, n2, e2, hn2, h2, f2, m2⟩ := o_zero (C := C) gNQ (e.rew sA)
  obtain ⟨s3, n3, e3, hn3, h3, f3, m3⟩ := o_zero (C := C) gLast s2
  have hv3 : s3.env p2VW = 2 ^ VW := by rw [f3.ev (by decide), f2.ev (by decide)]; exact hVW
  have hk3 : s3.env p2K = 2 ^ KW := by rw [f3.ev (by decide), f2.ev (by decide)]; exact hKW
  obtain ⟨s4, n4, e4, hn4, h4, f4, m4⟩ := o_mul (C := C) p2VW p2K gPZ s3 (by decide) (by decide) (by decide)
    (by rw [hv3, hk3, hZp]; omega)
  have hk4 : s4.env p2K = 2 ^ KW := by rw [f4.ev (by decide), hk3]
  have hz4 : s4.env gPZ = 2 ^ Z := by rw [h4, hv3, hk3, hZp]
  obtain ⟨s5, n5, e5, hn5, h5, f5, m5⟩ := o_mul (C := C) p2K gPZ gPad s4 (by decide) (by decide) (by decide)
    (by rw [hk4, hz4]; omega)
  obtain ⟨s6, n6, e6, hn6, h6, f6, m6⟩ := o_shl (C := C) gPad s5 (by rw [h5, hk4, hz4]; exact hW)
  have hm6 : Same (e.rew sA) s6 := ((((m2.trans m3).trans m4).trans m5).trans m6)
  have hrc6 : s6.rc sG = 0 := by rw [hm6.rc]; simp [DS.rew, Function.update_of_ne (by decide : sG ≠ sA), hrcG]
  have hram6 : s6.ram = e.ram := by rw [hm6.ram]; rfl
  have hlen : s6.rc sG < (s6.ram sG).length := by rw [hrc6, hram6, hG]; simp; omega
  obtain ⟨s7, n7, e7, hn7, h7⟩ := hs_rdM C sG gx s6 hlen
  subst h7
  refine ⟨_, n1 + (n2 + (n3 + (n4 + (n5 + (n6 + n7 + 1) + 1) + 1) + 1) + 1) + 1,
    Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 (Ex.seq e6 e7))))), by omega, ?_⟩
  have fr6 : Fr e s6 swT2 := (((((show Fr e (e.rew sA) swT2 from fun _ _ => rfl).trans (f2.weaken (by decide))).trans
    (f3.weaken (by decide))).trans (f4.weaken (by decide))).trans (f5.weaken (by decide))).trans
    (f6.weaken (by decide))
  refine ⟨by omega, fun m _ => by simp only [DS.adv, DS.set]; rw [hram6], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [DS.adv, DS.set, Function.update_self]; rw [hrc6]
  · simp only [DS.adv, DS.set, DS.env_set, Function.update_self]; rw [hram6, hrc6, hG]
  · simp only [DS.adv, DS.set]; rw [hram6]; simp [sweep]
  · simp only [DS.adv, DS.set]
    rw [Function.update_of_ne (by decide : sA ≠ sG), hm6.rc]; simp [DS.rew, sweep]
  · simp only [DS.adv, DS.set, DS.env_set]
    rw [Function.update_of_ne (by decide), f6.ev (by decide), f5.ev (by decide), f4.ev (by decide), h3]; rfl
  · simp only [DS.adv, DS.set, DS.env_set]
    rw [Function.update_of_ne (by decide), f6.ev (by decide), f5.ev (by decide), f4.ev (by decide),
      f3.ev (by decide), h2]; simp [sweep]
  · simp only [DS.adv, DS.set, DS.env_set]
    rw [Function.update_of_ne (by decide), f6.ev (by decide), f5.ev (by decide), hz4]
  · simp only [DS.adv, DS.set, DS.env_set]
    rw [Function.update_of_ne (by decide), h6, h5, hk4, hz4]; ring
  · intro y hy
    have h1 : y ≠ gx := fun e' => hy (by rw [e']; decide)
    simp only [DS.adv, DS.set, DS.env_set]
    rw [Function.update_of_ne h1]; exact fr6 y hy
  · simp only [DS.adv, DS.set]; rw [hm6.ip]; rfl
  · simp only [DS.adv, DS.set]; rw [hm6.out]; rfl
  · simp only [DS.adv, DS.set]; rw [hm6.kin]; rfl
  · simp only [DS.adv, DS.set]; rw [hm6.kout]; rfl
  · simp only [DS.adv, DS.set]; rw [hm6.kc]; rfl

/-- **The sweep phase.** -/
theorem sweepP_spec (e : DS VV MM) (Z VW KW : ℕ) (R : List ℕ) (n : ℕ)
    (H : SwH C Z VW R n (2 * 2 ^ KW * 2 ^ Z) e) (hKW : e.env p2K = 2 ^ KW) (hZ : Z = VW + KW) (hrcG : e.rc sG = 0)
    (hW : 2 * (2 ^ KW * 2 ^ Z) < 2 ^ C.Wd) :
    Hs C sweepP e (e.rc sA + 16 * R.length + 16) (fun b => SwI Z VW R n (2 * 2 ^ KW * 2 ^ Z) e R.length b) :=
  Hs.mono (Hs.seq (swInit_spec e Z VW KW R n H.vw hKW hZ H.G H.n1 hrcG hW) (fun b hb => swLoop_spec H hb))
    (by omega) (fun _ h => h)

end NearCubicGates.Close.Cells.GatherPhase
