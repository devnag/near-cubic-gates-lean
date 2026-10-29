import SourceAdapters.Routing.CoordinateMachineUpdate
import SourceAdapters.ShortPCP.Machines.FLangComp

/-!
# A complete triangular coefficient update

The construction in `lem:generator`: after evaluating the two old polynomials at the next basis point, invert the pivot, construct
both new coefficient vectors, and then replace the old vectors. The order keeps every old coefficient available to
both builders. The inverse is the actual reduced-word power operation, not an uncharged field function.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicGates.Adapters.ShortPCP.Machines.FL

/-- Construct both vectors before replacing either old vector. -/
def buildPair : S :=
  .seq (.set 35 (.add (.v 24) (.k 1)))
    (.seq rowProgram (.seq (.set 35 (.add (.v 24) (.k 2)))
      (.seq annProgram (.seq (.set 25 (.v 31)) (.set 26 (.v 32))))))

/-- The inverse, two packed builders, and final replacement of the stored vectors. -/
def updateStep : S := .seq (.set 30 (.finv (.v 28))) buildPair

theorem buildPair_spec (G : Glob) (s : FS) (L R : List ℕ) (n : ℕ)
    (hL : ∀ x ∈ L, x < 2 ^ s.fl) (hR : ∀ x ∈ R, x < 2 ^ s.fl)
    (h20 : s.env 20 = s.fl) (h24 : s.env 24 = n)
    (h25 : s.env 25 = packW s.fl L) (h26 : s.env 26 = packW s.fl R)
    (h28 : s.env 28 < 2 ^ s.fl) (h29 : s.env 29 < 2 ^ s.fl) (h30 : s.env 30 < 2 ^ s.fl)
    (hN : n + 2 ≤ G.N) (hK : s.fl * (n + 2) ≤ G.K) (hf : 1 ≤ s.fl) (hw : s.fl + 1 ≤ G.K) :
    let t := evalS G buildPair s
    t.env 25 = packW s.fl ((List.range (n + 2)).map (annValue s.fp s.fl (s.env 28) L)) ∧
      t.env 26 = packW s.fl ((List.range (n + 1)).map
        (rowValue s.fp s.fl (s.env 23) n (s.env 30) (s.env 29) L R)) ∧
      Wr [25, 26, 31, 32, 35, 36, 37] s t ∧ t.ip = s.ip := by
  intro t
  have hc := cap_ge G
  have hncap : n + 2 ≤ G.cap := le_trans (by nlinarith) hc
  have hc1 : min 1 G.cap = 1 := by omega
  have hc2 : min 2 G.cap = 2 := by omega
  let s1 := s.setv 35 (n + 1)
  let t1 := evalS G rowProgram s1
  have hr := rowProgram_spec G s1 L R (n + 1)
    (by simpa [s1] using hL) (by simpa [s1] using hR)
    (by simpa [s1] using h20) (by simpa [s1] using h25) (by simpa [s1] using h26)
    (by simpa [s1] using h29) (by simpa [s1] using h30)
    (by simp only [s1, FS.setv_env, Function.update_self]; omega)
    (by simpa only [s1, FS.setv_fl] using (show s.fl * (n + 1) ≤ G.K by nlinarith))
    (by simpa [s1] using hw)
  have hrw : Wr [32, 36, 37] s1 t1 := hr.2.1
  have t1fl : t1.fl = s.fl := hrw.fl
  have t1fp : t1.fp = s.fp := hrw.fp
  have t124 : t1.env 24 = n := by rw [hrw.env 24 (by decide)]; simpa [s1] using h24
  let s2 := t1.setv 35 (n + 2)
  let t2 := evalS G annProgram s2
  have hs2fl : s2.fl = s.fl := t1fl
  have hs2fp : s2.fp = s.fp := t1fp
  have ha := annProgram_spec G s2 L (n + 2)
    (by simpa only [hs2fl] using hL)
    (by simp only [s2, FS.setv_env, hrw.env 20 (by decide), s1,
      Function.update_of_ne (by decide : (20 : Var) ≠ 35), hs2fl, h20])
    (by simp only [s2, FS.setv_env, hrw.env 25 (by decide), s1,
      Function.update_of_ne (by decide : (25 : Var) ≠ 35), hs2fl, h25])
    (by simpa only [s2, FS.setv_env, Function.update_of_ne (by decide : (28 : Var) ≠ 35),
      hrw.env 28 (by decide), s1, Function.update_of_ne (by decide : (28 : Var) ≠ 35), hs2fl] using h28)
    (by simp only [s2, FS.setv_env, Function.update_self]; omega)
    (by simpa only [hs2fl] using hK) (by simpa only [hs2fl] using hw)
  have haw : Wr [31, 36, 37] s2 t2 := ha.2.1
  have hres25 : t2.env 31 = packW s.fl ((List.range (n + 2)).map (annValue s.fp s.fl (s.env 28) L)) := by
    have hp28 : s2.env 28 = s.env 28 := by
      simp only [s2, FS.setv_env, hrw.env 28 (by decide), s1,
        Function.update_of_ne (by decide : (28 : Var) ≠ 35)]
    simpa only [hs2fl, hs2fp, hp28] using ha.1
  have hres26 : t2.env 32 = packW s.fl ((List.range (n + 1)).map
      (rowValue s.fp s.fl (s.env 23) n (s.env 30) (s.env 29) L R)) := by
    rw [haw.env 32 (by decide)]
    simpa [s2, s1, h24] using hr.1
  have ht : t = (t2.setv 25 (t2.env 31)).setv 26 (t2.env 32) := by
    have he1 : evalE G s (.add (.v 24) (.k 1)) = n + 1 := by simp only [evalE, h24, hc1]; omega
    have he2 : evalE G t1 (.add (.v 24) (.k 2)) = n + 2 := by simp only [evalE, t124, hc2]; omega
    simp only [t, buildPair, evalS_seq, evalS_set, he1]
    change evalS G (.seq (.set 35 (.add (.v 24) (.k 2)))
      (.seq annProgram (.seq (.set 25 (.v 31)) (.set 26 (.v 32))))) t1 = _
    simp only [evalS_seq, evalS_set, he2]
    rfl
  rw [ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [FS.setv_env, Function.update_of_ne (by decide : (25 : Var) ≠ 26), Function.update_self]
      using hres25
  · simpa only [FS.setv_env, Function.update_self] using hres26
  · exact (((((Wr.setv s (by decide) (n + 1)).trans (hrw.mono (by decide))).trans
      (Wr.setv t1 (by decide) (n + 2))).trans (haw.mono (by decide))).trans
      (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
  · exact ha.2.2.trans hr.2.2

theorem updateStep_spec (G : Glob) (s : FS) (L R : List ℕ) (n : ℕ)
    (hL : ∀ x ∈ L, x < 2 ^ s.fl) (hR : ∀ x ∈ R, x < 2 ^ s.fl)
    (h20 : s.env 20 = s.fl) (h24 : s.env 24 = n)
    (h25 : s.env 25 = packW s.fl L) (h26 : s.env 26 = packW s.fl R)
    (h28 : s.env 28 < 2 ^ s.fl) (h29 : s.env 29 < 2 ^ s.fl)
    (hN : n + 2 ≤ G.N) (hK : s.fl * (n + 2) ≤ G.K) (hf : 1 ≤ s.fl) (hw : s.fl + 1 ≤ G.K) :
    let inv := powW s.fp s.fl (s.env 28) (2 ^ s.fl - 2)
    let t := evalS G updateStep s
    t.env 25 = packW s.fl ((List.range (n + 2)).map (annValue s.fp s.fl (s.env 28) L)) ∧
      t.env 26 = packW s.fl ((List.range (n + 1)).map
        (rowValue s.fp s.fl (s.env 23) n inv (s.env 29) L R)) ∧
      Wr [25, 26, 30, 31, 32, 35, 36, 37] s t ∧ t.ip = s.ip := by
  intro inv t
  let s1 := s.setv 30 inv
  have he : evalE G s (.finv (.v 28)) = inv := by
    simp only [evalE, Nat.mod_eq_of_lt h28, inv]
  have hb := buildPair_spec G s1 L R n
    (by simpa [s1] using hL) (by simpa [s1] using hR)
    (by simpa [s1] using h20) (by simpa [s1] using h24)
    (by simpa [s1] using h25) (by simpa [s1] using h26)
    (by simpa [s1] using h28) (by simpa [s1] using h29)
    (by simpa [s1, inv] using powW_lt s.fp s.fl (s.env 28) (2 ^ s.fl - 2))
    hN (by simpa [s1] using hK) (by simpa [s1] using hf) (by simpa [s1] using hw)
  have ht : t = evalS G buildPair s1 := by simp only [t, updateStep, evalS_seq, evalS_set, he, s1]
  rw [ht]
  refine ⟨?_, ?_, ?_, hb.2.2.2⟩
  · simpa only [s1, FS.setv_fl, FS.setv_fp, FS.setv_env,
      Function.update_of_ne (by decide : (28 : Var) ≠ 30)] using hb.1
  · simpa only [s1, FS.setv_fl, FS.setv_fp, FS.setv_env, Function.update_self,
      Function.update_of_ne (by decide : (23 : Var) ≠ 30),
      Function.update_of_ne (by decide : (29 : Var) ≠ 30)] using hb.2.1
  · exact (Wr.setv s (by decide) inv).trans (hb.2.2.1.mono (by decide))

theorem buildPair_wf (d : ℕ) (hd : d ≤ 7) : wfS buildPair d = true := by
  simp [buildPair, rowProgram, annProgram, genP, rowBody, annBody, getC, wfS, dE]
  omega

theorem updateStep_wf (d : ℕ) (hd : d ≤ 7) : wfS updateStep d = true := by
  simp [updateStep, wfS, dE, buildPair_wf d hd]

end NearCubicGates.Adapters.Routing.CoordinateMachine
