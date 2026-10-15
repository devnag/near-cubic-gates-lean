import Proof.Wire_3_5.FinalPassFiltTabVisit

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.GF2

variable (cap : ℕ)

/-- The canonical state at a visit boundary. -/
def canon (m lb a L : ℕ) (tauw pmw vw ow : List Bool) : TSt where
  vw := vw
  ow := ow
  tauw := tauw
  pmw := pmw
  fv := frame (binary m 0)
  fu := frame (binary m 0)
  pw := frame (binary m 0)
  acc := frame (binary m 0)
  st := frame (binary m 0)
  kw := frame (binary lb 0)
  bw := frame (binary lb 0)
  ep := frame (List.replicate (lb + (lb - 1)) false)
  vh := 0
  bwh := 0
  eph := 0
  f := 0
  ck := 0
  s := 0
  ns := 0
  tf := 0
  j := 0
  m := m
  lb := lb
  a := a
  L := L
  cell := false

/-- Blank the field words. -/
def zeroM : TProg :=
  .seq (mapPass zeroOut keepS qFV qTAU gF gR) (.seq (mapPass zeroOut keepS qFU qTAU gF gR)
  (.seq (mapPass zeroOut keepS qPW qTAU gF gR) (.seq (mapPass zeroOut keepS qACC qTAU gF gR)
  (mapPass zeroOut keepS qST qTAU gF gR))))

/-- Blank the label, the translation and the diagonals. -/
def zeroL : TProg :=
  .seq (mapPass zeroOut keepS qK qBW gF gR) (.seq (mapPass zeroOut keepS qBW qK gF gR) (mapPass zeroOut keepS qEP qV gF gR))

/-- Blank the scratch words. -/
def zeroAll : TProg := .seq zeroM zeroL

/-- One zero pass on a scratch word, in the layout. -/
theorem zeroT_spec (A B : Fin 12) (hAB : A ≠ B) (y : TSt) (n : ℕ) (as bs restB : List Bool)
    (hA : y.w.st A = frameP as ++ [false]) (hhA : y.w.sh A = 0) (hB : y.w.st B = frameP bs ++ restB)
    (hhB : y.w.sh B = 0) (hl : as.length = bs.length) (hn : as.length = n) (hf : y.f = 0) (hcap : 2 * n + 2 ≤ cap) :
    WExec cap (mapPass zeroOut keepS A B gF gR) y.w (y.w.sets A (frameP (List.replicate n false) ++ [false]))
      (n * 41 + 3) := by
  have h := mapPass_spec cap zeroOut keepS A B gF gR hAB (by decide) (by omega) as bs [] restB false y.w hl
    (by simpa using hA) hhA hB hhB (by show y.f = _; simp [hf]) rfl (by omega)
  rw [mapS_zero _ _ _ hl, hn] at h
  have e : (y.w.sets A (frameP (List.replicate n false) ++ false :: [])).setv gF (false).toNat =
      y.w.sets A (frameP (List.replicate n false) ++ [false]) := by
    refine WState.eq rfl rfl ?_ rfl
    funext r
    simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with hr
    · subst hr; show 0 = y.f; rw [hf]
    · rfl
  rw [e] at h
  exact h

theorem frame_zero (n : ℕ) : frameP (List.replicate n false) ++ [false] = frame (binary n 0) := by
  rw [binary_zero', frame_eq_frameP]

/-- One zero pass on a word state. -/
theorem zeroW_spec (A B : Fin 12) (hAB : A ≠ B) (σ : TState) (n : ℕ) (as bs restB : List Bool)
    (hA : σ.st A = frameP as ++ [false]) (hhA : σ.sh A = 0) (hB : σ.st B = frameP bs ++ restB)
    (hhB : σ.sh B = 0) (hl : as.length = bs.length) (hn : as.length = n) (hf : σ.val gF = 0) (hR : σ.val gR = 0)
    (hcap : 2 * n + 2 ≤ cap) :
    WExec cap (mapPass zeroOut keepS A B gF gR) σ (σ.sets A (frameP (List.replicate n false) ++ [false]))
      (n * 41 + 3) := by
  have h := mapPass_spec cap zeroOut keepS A B gF gR hAB (by decide) (by omega) as bs [] restB false σ hl
    (by simpa using hA) hhA hB hhB (by simp [hf]) hR (by omega)
  rw [mapS_zero _ _ _ hl, hn] at h
  have e : (σ.sets A (frameP (List.replicate n false) ++ false :: [])).setv gF (false).toNat =
      σ.sets A (frameP (List.replicate n false) ++ [false]) := by
    refine WState.eq rfl rfl ?_ rfl
    funext r
    simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with hr
    · subst hr; rw [hf]; rfl
    · rfl
  rw [e] at h
  exact h

theorem w_zeroM (z : TSt) (F : List Bool) :
    ((((z.w.sets qFV F).sets qFU F).sets qPW F).sets qACC F).sets qST F =
      { z with fv := F, fu := F, pw := F, acc := F, st := F }.w := by tst_eq

theorem w_zeroL (z : TSt) (K E : List Bool) :
    ((z.w.sets qK K).sets qBW K).sets qEP E = { z with kw := K, bw := K, ep := E }.w := by tst_eq

theorem zeroM_spec (z : TSt) (tv : ℕ) (n1 n2 n3 n4 n5 : ℕ) (h1 : z.fv = frame (binary z.m n1))
    (h2 : z.fu = frame (binary z.m n2)) (h3 : z.pw = frame (binary z.m n3)) (h4 : z.acc = frame (binary z.m n4))
    (h5 : z.st = frame (binary z.m n5)) (hf : z.f = 0) (htau : z.tauw = frame (binary z.m tv))
    (hcap : 2 * z.m + 2 ≤ cap) :
    WExec cap zeroM z.w
      { z with fv := frame (binary z.m 0), fu := frame (binary z.m 0), pw := frame (binary z.m 0),
               acc := frame (binary z.m 0), st := frame (binary z.m 0) }.w (5 * (z.m * 41 + 3) + 4) := by
  obtain ⟨F, hF⟩ : ∃ l : List Bool, l = frameP (List.replicate z.m false) ++ [false] := ⟨_, rfl⟩
  have hT : z.w.st qTAU = frameP (binary z.m tv) ++ [false] := by show z.tauw = _; rw [htau, frame_bin]
  have s1 := zeroW_spec cap qFV qTAU (by decide) z.w z.m (binary z.m n1) (binary z.m tv) [false]
    (by show z.fv = _; rw [h1, frame_bin]) rfl hT rfl (by simp) (by simp) hf rfl (by omega)
  rw [← hF] at s1
  obtain ⟨σ1, hσ1⟩ : ∃ τ : TState, τ = z.w.sets qFV F := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have a2 : σ1.st qFU = frameP (binary z.m n2) ++ [false] := by
    rw [hσ1]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide)]; show z.fu = _; rw [h2, frame_bin]
  have t2 : σ1.st qTAU = frameP (binary z.m tv) ++ [false] := by
    rw [hσ1]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide)]; exact hT
  have s2 := zeroW_spec cap qFU qTAU (by decide) σ1 z.m (binary z.m n2) (binary z.m tv) [false] a2
    (by rw [hσ1]; rfl) t2 (by rw [hσ1]; rfl) (by simp) (by simp) (by rw [hσ1]; exact hf) (by rw [hσ1]; rfl) (by omega)
  rw [← hF] at s2
  obtain ⟨σ2, hσ2⟩ : ∃ τ : TState, τ = σ1.sets qFU F := ⟨_, rfl⟩
  rw [← hσ2] at s2
  have a3 : σ2.st qPW = frameP (binary z.m n3) ++ [false] := by
    rw [hσ2, hσ1]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; show z.pw = _; rw [h3, frame_bin]
  have t3 : σ2.st qTAU = frameP (binary z.m tv) ++ [false] := by
    rw [hσ2]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide)]; exact t2
  have s3 := zeroW_spec cap qPW qTAU (by decide) σ2 z.m (binary z.m n3) (binary z.m tv) [false] a3
    (by rw [hσ2, hσ1]; rfl) t3 (by rw [hσ2, hσ1]; rfl) (by simp) (by simp) (by rw [hσ2, hσ1]; exact hf)
    (by rw [hσ2, hσ1]; rfl) (by omega)
  rw [← hF] at s3
  obtain ⟨σ3, hσ3⟩ : ∃ τ : TState, τ = σ2.sets qPW F := ⟨_, rfl⟩
  rw [← hσ3] at s3
  have a4 : σ3.st qACC = frameP (binary z.m n4) ++ [false] := by
    rw [hσ3, hσ2, hσ1]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    show z.acc = _; rw [h4, frame_bin]
  have t4 : σ3.st qTAU = frameP (binary z.m tv) ++ [false] := by
    rw [hσ3]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide)]; exact t3
  have s4 := zeroW_spec cap qACC qTAU (by decide) σ3 z.m (binary z.m n4) (binary z.m tv) [false] a4
    (by rw [hσ3, hσ2, hσ1]; rfl) t4 (by rw [hσ3, hσ2, hσ1]; rfl) (by simp) (by simp) (by rw [hσ3, hσ2, hσ1]; exact hf)
    (by rw [hσ3, hσ2, hσ1]; rfl) (by omega)
  rw [← hF] at s4
  obtain ⟨σ4, hσ4⟩ : ∃ τ : TState, τ = σ3.sets qACC F := ⟨_, rfl⟩
  rw [← hσ4] at s4
  have a5 : σ4.st qST = frameP (binary z.m n5) ++ [false] := by
    rw [hσ4, hσ3, hσ2, hσ1]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    show z.st = _; rw [h5, frame_bin]
  have t5 : σ4.st qTAU = frameP (binary z.m tv) ++ [false] := by
    rw [hσ4]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide)]; exact t4
  have s5 := zeroW_spec cap qST qTAU (by decide) σ4 z.m (binary z.m n5) (binary z.m tv) [false] a5
    (by rw [hσ4, hσ3, hσ2, hσ1]; rfl) t5 (by rw [hσ4, hσ3, hσ2, hσ1]; rfl) (by simp) (by simp)
    (by rw [hσ4, hσ3, hσ2, hσ1]; exact hf) (by rw [hσ4, hσ3, hσ2, hσ1]; rfl) (by omega)
  rw [← hF] at s5
  have e5 : σ4.sets qST F = { z with fv := F, fu := F, pw := F, acc := F, st := F }.w := by
    rw [hσ4, hσ3, hσ2, hσ1, w_zeroM]
  rw [e5] at s5
  have e : F = frame (binary z.m 0) := by rw [hF, frame_zero]
  rw [← e]
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_
  omega

theorem zeroL_spec (z : TSt) (n6 n7 : ℕ) (E V0 restV : List Bool) (h6 : z.kw = frame (binary z.lb n6))
    (h7 : z.bw = frame (binary z.lb n7)) (hE : z.ep = frame E) (hEl : E.length = z.lb + (z.lb - 1))
    (hV : z.vw = frameP V0 ++ restV) (hV0 : z.lb + (z.lb - 1) ≤ V0.length) (hvh : z.vh = 0) (hbwh : z.bwh = 0)
    (heph : z.eph = 0) (hf : z.f = 0) (hcap : 4 * z.lb + 2 ≤ cap) :
    WExec cap zeroL z.w
      { z with kw := frame (binary z.lb 0), bw := frame (binary z.lb 0),
               ep := frame (List.replicate (z.lb + (z.lb - 1)) false) }.w
      (2 * (z.lb * 41 + 3) + ((z.lb + (z.lb - 1)) * 41 + 3) + 2) := by
  obtain ⟨K, hK⟩ : ∃ l : List Bool, l = frameP (List.replicate z.lb false) ++ [false] := ⟨_, rfl⟩
  have s1 := zeroW_spec cap qK qBW (by decide) z.w z.lb (binary z.lb n6) (binary z.lb n7) [false]
    (by show z.kw = _; rw [h6, frame_bin]) rfl (by show z.bw = _; rw [h7, frame_bin]) hbwh (by simp) (by simp) hf rfl
    (by omega)
  rw [← hK] at s1
  obtain ⟨σ1, hσ1⟩ : ∃ τ : TState, τ = z.w.sets qK K := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have a2 : σ1.st qBW = frameP (binary z.lb n7) ++ [false] := by
    rw [hσ1]; simp only [WState.sets_st]; rw [Function.update_of_ne (by decide)]; show z.bw = _; rw [h7, frame_bin]
  have b2 : σ1.st qK = frameP (binary z.lb 0) ++ [false] := by
    rw [hσ1]; simp only [WState.sets_st, Function.update_self]; rw [hK, binary_zero']
  have s2 := zeroW_spec cap qBW qK (by decide) σ1 z.lb (binary z.lb n7) (binary z.lb 0) [false] a2
    (by rw [hσ1]; exact hbwh) b2 (by rw [hσ1]; rfl) (by simp) (by simp) (by rw [hσ1]; exact hf) (by rw [hσ1]; rfl)
    (by omega)
  rw [← hK] at s2
  obtain ⟨σ2, hσ2⟩ : ∃ τ : TState, τ = σ1.sets qBW K := ⟨_, rfl⟩
  rw [← hσ2] at s2
  have hVs : frameP V0 = frameP (V0.take (z.lb + (z.lb - 1))) ++ frameP (V0.drop (z.lb + (z.lb - 1))) :=
    frameP_split V0 _
  have a3 : σ2.st qEP = frameP E ++ [false] := by
    rw [hσ2, hσ1]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; show z.ep = _; rw [hE, frame_eq_frameP]
  have b3 : σ2.st qV = frameP (V0.take (z.lb + (z.lb - 1))) ++ (frameP (V0.drop (z.lb + (z.lb - 1))) ++ restV) := by
    rw [hσ2, hσ1]; simp only [WState.sets_st]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; show z.vw = _
    rw [hV, hVs, List.append_assoc]
  have s3 := zeroW_spec cap qEP qV (by decide) σ2 (z.lb + (z.lb - 1)) E (V0.take (z.lb + (z.lb - 1)))
    (frameP (V0.drop (z.lb + (z.lb - 1))) ++ restV) a3 (by rw [hσ2, hσ1]; exact heph) b3
    (by rw [hσ2, hσ1]; exact hvh) (by simp [hEl]; omega) hEl (by rw [hσ2, hσ1]; exact hf) (by rw [hσ2, hσ1]; rfl)
    (by omega)
  have e3 : σ2.sets qEP (frameP (List.replicate (z.lb + (z.lb - 1)) false) ++ [false]) =
      { z with kw := K, bw := K, ep := frame (List.replicate (z.lb + (z.lb - 1)) false) }.w := by
    rw [hσ2, hσ1, ← frame_eq_frameP, w_zeroL]
  rw [e3] at s3
  have e : K = frame (binary z.lb 0) := by rw [hK, frame_zero]
  rw [← e]
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega)

theorem zeroAll_spec (z : TSt) (tv : ℕ) (V0 restV : List Bool) (hsh : Shaped z) (hvh : z.vh = 0) (hbwh : z.bwh = 0)
    (heph : z.eph = 0) (hf : z.f = 0) (htau : z.tauw = frame (binary z.m tv)) (hV : z.vw = frameP V0 ++ restV)
    (hV0 : z.lb + (z.lb - 1) ≤ V0.length) (hcap : 2 * z.m + 4 * z.lb + 2 ≤ cap) :
    WExec cap zeroAll z.w
      { z with fv := frame (binary z.m 0), fu := frame (binary z.m 0), pw := frame (binary z.m 0),
               acc := frame (binary z.m 0), st := frame (binary z.m 0), kw := frame (binary z.lb 0),
               bw := frame (binary z.lb 0), ep := frame (List.replicate (z.lb + (z.lb - 1)) false) }.w
      (5 * (z.m * 41 + 3) + 2 * (z.lb * 41 + 3) + ((z.lb + (z.lb - 1)) * 41 + 3) + 7) := by
  obtain ⟨⟨n1, h1⟩, ⟨n2, h2⟩, ⟨n3, h3⟩, ⟨n4, h4⟩, ⟨n5, h5⟩, ⟨n6, h6⟩, ⟨n7, h7⟩, ⟨E, hE, hEl⟩⟩ := hsh
  have s1 := zeroM_spec cap z tv n1 n2 n3 n4 n5 h1 h2 h3 h4 h5 hf htau (by omega)
  obtain ⟨M0, hM0⟩ : ∃ l : List Bool, l = frame (binary z.m 0) := ⟨_, rfl⟩
  rw [← hM0] at s1
  obtain ⟨x1, hx1⟩ : ∃ y : TSt, y = { z with fv := M0, fu := M0, pw := M0, acc := M0, st := M0 } := ⟨_, rfl⟩
  rw [← hx1] at s1
  have s2 := zeroL_spec cap x1 n6 n7 E V0 restV (by rw [hx1]; exact h6) (by rw [hx1]; exact h7) (by rw [hx1]; exact hE)
    (by rw [hx1]; exact hEl) (by rw [hx1]; exact hV) (by rw [hx1]; exact hV0) (by rw [hx1]; exact hvh)
    (by rw [hx1]; exact hbwh) (by rw [hx1]; exact heph) (by rw [hx1]; exact hf)
    (by rw [hx1]; show 4 * z.lb + 2 ≤ cap; omega)
  have hlb1 : x1.lb = z.lb := by rw [hx1]
  obtain ⟨B0, hB0⟩ : ∃ l : List Bool, l = frame (binary x1.lb 0) := ⟨_, rfl⟩
  obtain ⟨E0, hE0⟩ : ∃ l : List Bool, l = frame (List.replicate (x1.lb + (x1.lb - 1)) false) := ⟨_, rfl⟩
  rw [← hB0, ← hE0] at s2
  rw [hlb1] at hB0 hE0
  have e : ({ x1 with kw := B0, bw := B0, ep := E0 } : TSt) =
      { z with fv := M0, fu := M0, pw := M0, acc := M0, st := M0, kw := B0, bw := B0, ep := E0 } := by rw [hx1]
  rw [e] at s2
  rw [← hM0, ← hB0, ← hE0]
  refine WExec.mono (WExec.seq s1 s2) ?_
  rw [hlb1]; omega

/-- One visit between canonical states. -/
def visitZ : TProg := .seq visitT zeroAll

/-- The cost of one visit between canonical states. -/
def visitZCost (m lb a L n : ℕ) : ℕ :=
  visitCost m lb a L n + 1 + (5 * (m * 41 + 3) + 2 * (lb * 41 + 3) + ((lb + (lb - 1)) * 41 + 3) + 7)

theorem canon_shaped (m lb a L : ℕ) (tauw pmw vw ow : List Bool) : Shaped (canon m lb a L tauw pmw vw ow) :=
  ⟨⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨_, rfl, by simp [canon]⟩⟩

/-- **One visit** of the table builder: the visit's word is appended, the state is canonical again. -/
theorem visitZ_spec (p tv X n m lb a L : ℕ) (restV tauw pmw ow : List Bool) (hrest : ∃ t, restV = false :: t)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hlb : 1 ≤ lb) (ha : a ≤ lb)
    (htau : tauw = frame (binary m tv)) (hpm : pmw = frame (binary m p))
    (hcap : 2 * (wOf m lb * n) + 4 * lb + 2 * m + L + 10 ≤ cap) (hO : ow.length + n * (2 * L + 2) + 8 < cap) :
    WExec cap visitZ (canon m lb a L tauw pmw (frameP (binary (wOf m lb * n) X) ++ restV) ow).w
      (canon m lb a L tauw pmw (frameP (binary (wOf m lb * n) X) ++ restV)
        (ow ++ visitWord (copyList p m lb a tv X L n))).w (visitZCost m lb a L n) := by
  obtain ⟨z, h1, hsh, hz⟩ := visitT_spec cap p tv X n restV hrest (canon m lb a L tauw pmw
    (frameP (binary (wOf m lb * n) X) ++ restV) ow) rfl rfl hm hlb ha (canon_shaped _ _ _ _ _ _ _ _) htau hpm
    rfl rfl rfl rfl rfl rfl rfl rfl hcap hO
  have hw : lb + (lb - 1) ≤ (binary (wOf m lb * n) X).length := by
    simp only [binary_length]; unfold wOf; nlinarith
  have h2 := zeroAll_spec cap z tv (binary (wOf m lb * n) X) restV hsh (by rw [hz]; rfl) (by rw [hz]; rfl)
    (by rw [hz]; rfl) (by rw [hz]; rfl) (by rw [hz]; exact htau) (by rw [hz]; rfl) (by rw [hz]; exact hw)
    (by rw [hz]; show 2 * m + 4 * lb + 2 ≤ cap; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ ?_
  · rw [hz]; rfl
  · have hm' : z.m = m := by rw [hz]; rfl
    have hlb' : z.lb = lb := by rw [hz]; rfl
    rw [hm', hlb']; unfold visitZCost; simp only [canon]; omega

end NearCubicWires.WireExponent3_5.FinalPass.Filt
