import SourceAdapters.Routing.CoordinateMachineSampleProgram

/-! The construction in `lem:generator`: sample the two stored coefficient vectors at α^n.
All preparation, both evaluator calls, and preservation are accounted for. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open ShortPCP.Machines.FL NearCubicWires.WireExponent3_5
open scoped BigOperators

theorem sample_spec (G : Glob) (s : FS) (L R : List ℕ) (n : ℕ)
    (hL : ∀ c ∈ L, c < 2 ^ s.fl) (hR : ∀ c ∈ R, c < 2 ^ s.fl)
    (hLl : L.length = n + 1) (hRl : R.length = n)
    (h20 : s.env 20 = s.fl) (h24 : s.env 24 = n)
    (h25 : s.env 25 = packW s.fl L) (h26 : s.env 26 = packW s.fl R)
    (hok : fieldOk G s.fl s.fp = true) (hn : n < s.fl)
    (hN : L.length ≤ G.N) (hK : L.length * s.fl ≤ G.K) :
    let t := evalS G sampleProgram s
    t.env 27 = 2 ^ n ∧ t.env 35 = n ∧
      t.env 28 < 2 ^ s.fl ∧
      GF.rep s.fp (t.env 28) =
        ∑ r ∈ Finset.range (n + 1), GF.rep s.fp (L.getD r 0) * (GF.rep s.fp (2 ^ n)) ^ (2 ^ r) ∧
      t.env 29 < 2 ^ s.fl ∧
      GF.rep s.fp (t.env 29) =
        ∑ r ∈ Finset.range n, GF.rep s.fp (R.getD r 0) * (GF.rep s.fp (2 ^ n)) ^ (2 ^ r) ∧
      Wr sampleWrites s t ∧ t.ip = s.ip := by
  intro t
  have hfK := (fl_bounds hok).2.1
  have hcK := cap_ge G
  have hf := tf_le hok
  have hx : 2 ^ n < 2 ^ s.fl := Nat.pow_lt_pow_right (by decide) hn
  have h1 : min 1 G.cap = 1 := min_eq_left (by omega)
  have hpow : min (2 ^ n) G.cap = 2 ^ n := min_eq_left (by omega)
  have hadd : min (n + 1) G.cap = n + 1 := min_eq_left (by omega)
  let s1 := (s.setv 27 (2 ^ n)).setv 35 (n + 1)
  have hprep : evalS G (.set 35 (.add (.v 24) (.k 1)))
      (evalS G (.set 27 (.shl (.k 1) (.v 24))) s) = s1 := by
    simp only [evalS_set, evalE, FS.setv_env,
      Function.update_of_ne (by decide : (24 : Var) ≠ 27), h24, h1, one_mul, hpow, hadd]
    rfl
  let u := evalS G (evalStored 25 28) s1
  have hcallL := evalStored_spec G s1 25 28 L L.length (2 ^ n)
    (by simpa only [s1, FS.setv_fl] using hL)
    (by simpa [s1] using h20) (by simpa [s1] using h25)
    (by simp [s1, hLl]) (by simp [s1])
    (by simpa only [s1, FS.setv_fl] using hx)
    (by simpa only [s1, FS.setv_fl, FS.setv_fp] using hok) hN
    (by simpa only [s1, FS.setv_fl] using hK.trans hcK)
  have hpreW : Wr sampleWrites s s1 :=
    (Wr.setv s (by simp [sampleWrites]) _).trans (Wr.setv _ (by simp [sampleWrites]) _)
  have huW : Wr sampleWrites s u :=
    hpreW.trans (hcallL.2.2.1.mono (by simp_all [sampleWrites]))
  have hu24 : u.env 24 = n := (huW.env 24 (by simp [sampleWrites])).trans h24
  have hu27 : u.env 27 = 2 ^ n := by
    have hh := hcallL.2.2.1.env 27 (by decide)
    simpa [s1] using hh
  let v := u.setv 35 n
  have hvW : Wr sampleWrites s v := huW.trans (Wr.setv _ (by simp [sampleWrites]) _)
  have hv20 : v.env 20 = v.fl := by
    rw [hvW.env 20 (by simp [sampleWrites]), hvW.fl, h20]
  have hv26 : v.env 26 = packW v.fl R := by
    rw [hvW.env 26 (by simp [sampleWrites]), hvW.fl, h26]
  have hcapR : R.length * s.fl ≤ G.cap := by
    have hlen : R.length ≤ L.length := by omega
    exact (Nat.mul_le_mul_right _ hlen).trans (hK.trans hcK)
  have hcallR := evalStored_spec G v 26 29 R R.length (2 ^ n)
    (by simpa only [hvW.fl] using hR) hv20 hv26
    (by simp [v, hRl]) (by simpa [v] using hu27)
    (by simpa only [hvW.fl] using hx)
    (by simpa only [hvW.fl, hvW.fp] using hok) (by omega)
    (by simpa only [hvW.fl] using hcapR)
  have ht : t = evalS G (evalStored 26 29) v := by
    simp only [t, sampleProgram, evalS_seq]
    rw [hprep]
    change evalS G (evalStored 26 29) (u.setv 35 (u.env 24)) = _
    rw [hu24]
  have ht28 : (evalS G (evalStored 26 29) v).env 28 = u.env 28 := by
    have hh := hcallR.2.2.1.env 28 (by decide)
    simpa [v] using hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, inputFree_ip G sampleProgram sample_inputFree s⟩
  · rw [ht, hcallR.2.2.1.env 27 (by decide)]
    simpa [v] using hu27
  · rw [ht, hcallR.2.2.1.env 35 (by decide)]
    simp [v]
  · rw [ht, ht28]
    exact hcallL.1
  · rw [ht, ht28]
    rw [← hLl]
    exact hcallL.2.1
  · rw [ht]
    simpa only [hvW.fl] using hcallR.1
  · rw [ht]
    have heR := hcallR.2.1
    change GF.rep v.fp ((evalS G (evalStored 26 29) v).env 29) =
      ∑ r ∈ Finset.range R.length, GF.rep v.fp (R.getD r 0) * (GF.rep v.fp (2 ^ n)) ^ (2 ^ r) at heR
    rw [hvW.fp, hRl] at heR
    exact heR
  · rw [ht]
    exact hvW.trans (hcallR.2.2.1.mono (by simp_all [sampleWrites]))

end NearCubicGates.Adapters.Routing.CoordinateMachine
