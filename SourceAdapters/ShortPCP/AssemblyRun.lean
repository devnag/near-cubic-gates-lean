import SourceAdapters.ShortPCP.AssemblyPhases

/-!
# Phase F and the whole middle program of P07

Phase F (proof of `thm:short-pcp-ours`): close the data frame; `ℓ = c0 + f + bL·|bits f|` (the computable bound of
`Field6.Pipeline.ell`); `fuel = KT·(|data| + ℓ + 1)^{eT}` (`Field6.Pipeline.compRequest`); print `frame 1^ℓ` and
`frame 1^fuel`, doubly framed, and the outer terminator. `mid_spec`: the program prints exactly
`frame (frame data ++ frame 1^ℓ ++ frame 1^fuel)` within `57·(U + 1)` cell steps.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Assembly

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- `uR := uR · sF^{sH}` by repeated multiplication (`sC` counts). -/
def powLoop : St VV MM := .loop (.lt sC sH) (.seq (.op (.mul uR sF sG)) (.seq (.op (.copy uR sG)) (.op (.inc sC))))

def phaseF (c0 bL KT eT : ℕ) : St VV MM :=
  .seq (lit [true, false]) (.seq (setC lR c0) (.seq (.op (.add lR fR)) (.seq (setC sH bL) (.seq (.op (.mul kR
    sH sG)) (.seq (.op (.add lR sG)) (.seq (.op (.copy sF dR)) (.seq (.op (.add sF lR)) (.seq (.op (.inc sF))
    (.seq (setC uR KT) (.seq (setC sH eT) (.seq (.op (.zero sC)) (.seq powLoop (.seq (repL [true, true, true,
    true] lR) (.seq (lit [true, false]) (.seq (repL [true, true, true, true] uR) (lit [true, false,
    false]))))))))))))))))

theorem powLoop_spec (a : DS VV MM) (hc : Cst a) (K B e : ℕ) (hB : 1 ≤ B) (hsC : a.env sC = 0) (hsH : a.env sH = e)
    (hsF : a.env sF = B) (huR : a.env uR = K) (hW : K * B ^ e < 2 ^ C.Wd) (he : e < 2 ^ C.Wd) :
    Hs C powLoop a (e * (5 + 2) + 2) (fun b => b.env uR = K * B ^ e ∧ b.out = a.out ∧ Cst b ∧
      Fr a b [uR, sG, sC]) := by
  let I : ℕ → DS VV MM → Prop := fun j b => b.env sC = j ∧ b.env sH = e ∧ b.env sF = B ∧ b.env uR = K * B ^ j ∧
    b.out = a.out ∧ Fr a b [uR, sG, sC]
  refine Hs.mono (Hs.loopN (c := .lt sC sH) (show sC ≠ sH by decide) I e 5 ?_ ?_ a
    ⟨hsC, hsH, hsF, by rw [huR]; simp, rfl, Fr.refl _ _⟩) le_rfl ?_
  · intro j hj b ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by simp [Cnd.eval, h1, h2, hj], ?_⟩
    have hle : K * B ^ (j + 1) ≤ K * B ^ e := Nat.mul_le_mul_left K (Nat.pow_le_pow_right hB hj)
    refine Hs.seq (t1 := 1) (t2 := 3) (hs_mul C uR sF sG b (by decide) (by decide) (by decide) (by
      rw [h4, h3, mul_assoc, ← pow_succ]; omega)) (fun d hd => ?_)
    subst hd
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C uR sG _ (by decide)) (fun d hd => ?_)
    subst hd
    refine Hs.mono (hs_inc C sC _ (by vsimp [h1]; omega)) le_rfl ?_
    rintro g rfl
    refine ⟨by vsimp [h1], by vsimp [h2], by vsimp [h3], by vsimp [h4, h3]; ring, by simp [h5], ?_⟩
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    vsimp [hy.1, hy.2.1, hy.2.2]
    exact h6 y (by simp [hy.1, hy.2.1, hy.2.2])
  · intro b hb
    obtain ⟨h1, h2, -⟩ := hb
    simp [Cnd.eval, h1, h2]
  · rintro b ⟨-, -, -, h4, h5, h6⟩
    exact ⟨h4, h5, Cst.of_fr hc h6 (by decide), h6⟩

theorem phaseF_spec (R : Run) (U : ℕ) (hg : R.Good C U) (a : DS VV MM) (ha : R.PostE a) :
    Hs C (phaseF R.c0 R.bL R.KT R.eT) a (17 * (U + 1)) (fun b => b.out = R.out) := by
  obtain ⟨hiU, hdU, hlU, hfU, hcU, hbU, hkU, heU, -, -⟩ := bound_facts R hg
  have hW := hg.hW
  have hc := ha.cst
  have hf := hg.f
  have hfl : R.f ≤ R.ell := by unfold Run.ell; omega
  have hkl : R.bL * natBitLength R.f ≤ R.ell := by unfold Run.ell; omega
  have hlt : ∀ v, 50 * v ≤ U → v < 2 ^ C.Wd := fun v hv => by omega
  have hlU' : 50 * (R.c0 + R.f + R.bL * natBitLength R.f) ≤ U := hlU
  -- close the data frame
  refine hs_step (Hs.mono (lit_spec [true, false] a hc.z) (by simp; omega) (fun _ h => h)) (fun b1 hb1 => ?_)
  subst hb1
  -- `ℓ`
  refine hs_step (Hs.mono (setC_spec (C := C) lR R.c0 _ (hlt _ hcU)) (by omega) (fun _ h => h)) (fun b2 hb2 => ?_)
  subst hb2
  refine hs_step (Hs.mono (hs_add C lR fR _ (by decide) (by vsimp [ha.f]; exact hlt _ (by omega)))
    (by omega) (fun _ h => h)) (fun b3 hb3 => ?_)
  subst hb3
  refine hs_step (Hs.mono (setC_spec (C := C) sH R.bL _ (hlt _ hbU)) (by omega) (fun _ h => h)) (fun b4 hb4 => ?_)
  subst hb4
  refine hs_step (Hs.mono (hs_mul C kR sH sG _ (by decide) (by decide) (by decide) (by
      vsimp [ha.k]; rw [Nat.mul_comm]; exact hlt _ (by omega))) (by omega) (fun _ h => h)) (fun b5 hb5 => ?_)
  subst hb5
  refine hs_step (Hs.mono (hs_add C lR sG _ (by decide) (by
      vsimp [ha.f, ha.k]; rw [Nat.mul_comm]; exact hlt _ (by omega))) (by omega)
    (fun _ h => h)) (fun b6 hb6 => ?_)
  subst hb6
  -- the fuel
  refine hs_step (Hs.mono (hs_copy C sF dR _ (by decide)) (by omega) (fun _ h => h)) (fun b7 hb7 => ?_)
  have c7 : Cst b7 := ⟨by rw [hb7]; vsimp [hc.z], by rw [hb7]; vsimp [hc.one], by rw [hb7]; vsimp [hc.two]⟩
  have l7 : b7.env lR = R.ell := by
    rw [hb7]; vsimp [ha.f, ha.k]; unfold Run.ell; ring
  have s7 : b7.env sF = R.data.length := by rw [hb7]; vsimp [ha.d]
  have o7 : b7.out = a.out ++ [true, false] := by rw [hb7]; simp
  have hsum : 50 * (R.data.length + R.ell + 1) ≤ U := by have hB := hg.hU; unfold Run.bound at hB; omega
  have hbase : R.data.length + R.ell + 1 < 2 ^ C.Wd := hlt _ hsum
  refine hs_step (Hs.mono (hs_add C sF lR b7 (by decide) (by rw [s7, l7]; omega)) (by omega) (fun _ h => h))
    (fun b8 hb8 => ?_)
  subst hb8
  refine hs_step (Hs.mono (hs_inc C sF _ (by vsimp [s7, l7]; omega)) (by omega) (fun _ h => h)) (fun b9 hb9 => ?_)
  subst hb9
  refine hs_step (Hs.mono (setC_spec (C := C) uR R.KT _ (hlt _ hkU)) (by omega) (fun _ h => h)) (fun b10 hb10 => ?_)
  subst hb10
  refine hs_step (Hs.mono (setC_spec (C := C) sH R.eT _ (hlt _ heU)) (by omega) (fun _ h => h)) (fun b11 hb11 => ?_)
  subst hb11
  refine hs_step (Hs.mono (hs_zero C sC _) (by omega) (fun _ h => h)) (fun b12 hb12 => ?_)
  -- the power
  have hfuel : R.fuel = R.KT * (R.data.length + R.ell + 1) ^ R.eT := rfl
  refine hs_step (Hs.mono (powLoop_spec b12 (by rw [hb12]; exact ⟨by vsimp [c7.z], by vsimp [c7.one], by vsimp [c7.two]⟩)
    R.KT (R.data.length + R.ell + 1) R.eT (by omega) (by rw [hb12]; vsimp []) (by rw [hb12]; vsimp [])
    (by rw [hb12]; vsimp [s7, l7]) (by rw [hb12]; vsimp []) (by rw [← hfuel]; exact hlt _ hfU) (hlt _ heU))
    (by omega) (fun _ h => h)) (fun b13 hb13 => ?_)
  obtain ⟨h131, h132, hc13, h134⟩ := hb13
  have l13 : b13.env lR = R.ell := by rw [h134 lR (by decide), hb12]; vsimp [l7]
  have o12 : b12.out = a.out ++ [true, false] := by rw [hb12]; simp [o7]
  -- the two unary frames
  refine hs_step (Hs.mono (repL_spec [true, true, true, true] lR (by decide) b13 hc13 (by rw [l13]; exact hlt _ hlU))
    (by rw [l13]; simp; omega) (fun _ h => h)) (fun b14 hb14 => ?_)
  obtain ⟨h141, h142, h143, h144, h145, h146⟩ := hb14
  have hc14 : Cst b14 := Cst.of_fr hc13 h146 (by decide)
  refine hs_step (Hs.mono (lit_spec [true, false] b14 hc14.z) (by simp; omega) (fun _ h => h)) (fun b15 hb15 => ?_)
  subst hb15
  have u15 : b14.env uR = R.fuel := by rw [h146 uR (by decide), h131, hfuel]
  refine hs_step (Hs.mono (repL_spec [true, true, true, true] uR (by decide) _ ⟨hc14.z, hc14.one, hc14.two⟩
    (by simp [u15]; exact hlt _ hfU))
    (by simp [u15]; omega) (fun _ h => h)) (fun b16 hb16 => ?_)
  obtain ⟨h161, -, -, -, -, h166⟩ := hb16
  have hc16 : Cst b16 := Cst.of_fr hc14 h166 (by decide)
  refine hs_one (Hs.mono (lit_spec [true, false, false] b16 hc16.z) (by simp; omega) (fun b hb => ?_))
  subst hb
  simp only [Run.out, frame_request]
  rw [h161]; simp only [u15]
  rw [h141, l13, h132, o12, ha.out]

/-! ## The whole middle program -/

/-- **The middle program**: phases A–F. -/
def mid (c0 bL KT eT : ℕ) : St VV MM :=
  .seq phaseA (.seq phaseB (.seq phaseC (.seq phaseD (.seq phaseE (phaseF c0 bL KT eT)))))

/-- **The run of the middle program**: from the initial cell state, it prints exactly the doubly framed compilation
request `frame (frame data ++ frame 1^ℓ ++ frame 1^fuel)`, within `57·(U + 1)` cell steps. -/
theorem mid_spec (R : Run) (U : ℕ) (hg : R.Good C U) :
    Hs C (mid R.c0 R.bL R.KT R.eT) a0 (57 * (U + 1)) (fun b => b.out = R.out) :=
  Hs.mono (Hs.seq (phaseA_spec R U hg) (fun a ha => Hs.seq (phaseB_spec R U hg a ha) (fun b hb =>
    Hs.seq (phaseC_spec R U hg b hb) (fun c hc => Hs.seq (phaseD_spec R U hg c hc) (fun d hd =>
    Hs.seq (phaseE_spec R U hg d hd) (fun e he => phaseF_spec R U hg e he)))))) (by ring_nf; omega) (fun _ h => h)

end NearCubicGates.Adapters.ShortPCP.Assembly
