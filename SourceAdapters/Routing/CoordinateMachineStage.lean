import SourceAdapters.Routing.CoordinateMachineSampleBridge
import SourceAdapters.Routing.CoordinateMachineUpdateStep
import SourceAdapters.Routing.CoordinateMachineAlgebraUpdate
import SourceAdapters.Routing.CoordinateMachineAlgebraField

/-!
# One actual stage of the compact coordinate solver

The construction in `lem:generator`: evaluate the old annihilator and selected coordinate
row at the next monomial basis element, invert the nonzero annihilator
pivot, and replace both stored vectors with their next compact arrays.
-/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open Coordinates CoordinateMachineAlgebra
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.Joins
open NearCubicWires.WireExponent3_5

/-- Sample both old arrays before constructing and replacing either one. -/
def stageProgram : S := .seq sampleProgram updateStep

/-- Field parameters, dimension, selected row and stage counter are retained. -/
def stageWrites : List Var := [25, 26, 27, 28, 29, 30, 31, 32, 35, 36, 37, 40, 41, 42, 44, 45, 46]

theorem stage_wf (d : ℕ) (hd : d ≤ 7) : wfS stageProgram d = true := by
  simp only [stageProgram, wfS, sample_wellFormed d hd, updateStep_wf d hd, Bool.and_self]

/-- One complete stage preserves the stored-array invariant and the input cursor. -/
theorem stage_spec (G : Glob) (s : FS) (p : CoordReq) (h : CoordOk p)
    (a n : ℕ) (hn : n < p.m) (L R : List ℕ)
    (hL : ∀ x ∈ L, x < 2 ^ p.f) (hR : ∀ x ∈ R, x < 2 ^ p.f)
    (hLm : letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
      L.map (GF.rep p.irr) =
        List.ofFn (annihilatorCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) n))
    (hRm : letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
      R.map (GF.rep p.irr) =
        List.ofFn (coordinateCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) n a))
    (hfl : s.fl = p.f) (hfp : s.fp = p.irr)
    (h20 : s.env 20 = p.f) (h23 : s.env 23 = a) (h24 : s.env 24 = n)
    (h25 : s.env 25 = packW p.f L) (h26 : s.env 26 = packW p.f R)
    (hN : n + 2 ≤ G.N) (hK : p.f * (n + 2) ≤ G.K) (hw : p.f + 2 ≤ G.K) :
    letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
    let t := evalS G stageProgram s
    ∃ L' R' : List ℕ,
      t.env 25 = packW p.f L' ∧ t.env 26 = packW p.f R' ∧
      (∀ x ∈ L', x < 2 ^ p.f) ∧ (∀ x ∈ R', x < 2 ^ p.f) ∧
      L'.map (GF.rep p.irr) =
        List.ofFn (annihilatorCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) (n + 1)) ∧
      R'.map (GF.rep p.irr) =
        List.ofFn (coordinateCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) (n + 1) a) ∧
      Wr stageWrites s t ∧ t.ip = s.ip := by
  rcases s with ⟨env, out, fl, fp, ip, bad⟩
  change fl = p.f at hfl
  change fp = p.irr at hfp
  subst fl
  subst fp
  let s : FS := ⟨env, out, p.f, p.irr, ip, bad⟩
  have hfl : s.fl = p.f := rfl
  have hfp : s.fp = p.irr := rfl
  letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
  let e : ℕ → AdjoinRoot (GF.toPoly p.irr) := extendBasis (monoBasis (GF.toPoly p.irr) p.m)
  let u := evalS G sampleProgram s
  have hLl : L.length = n + 1 := by
    simpa only [List.length_map, List.length_ofFn] using congrArg List.length hLm
  have hRl : R.length = n := by
    simpa only [List.length_map, List.length_ofFn] using congrArg List.length hRm
  have hnf : n < p.f := by have := h.2.2.2; omega
  have hf : 1 ≤ p.f := by have := h.2.2; omega
  have hsamp := sample_linearized G s
  obtain ⟨_, _, h28, he28, h29, he29, hsW, hsip⟩ :=
    hsamp L R n (annihilatorCoefficients e n) (coordinateCoefficients e n a)
      hL hR hLl hRl hLm hRm h20 h24 h25 h26 (coordOk_fieldOk G p h hw) hnf
      (by omega) (by rw [hLl]; nlinarith)
  have hufl : u.fl = p.f := hsW.fl.trans hfl
  have hufp : u.fp = p.irr := hsW.fp.trans hfp
  have hu20 : u.env 20 = p.f := (hsW.env 20 (by simp [sampleWrites])).trans h20
  have hu23 : u.env 23 = a := (hsW.env 23 (by simp [sampleWrites])).trans h23
  have hu24 : u.env 24 = n := (hsW.env 24 (by simp [sampleWrites])).trans h24
  have hu25 : u.env 25 = packW p.f L := (hsW.env 25 (by simp [sampleWrites])).trans h25
  have hu26 : u.env 26 = packW p.f R := (hsW.env 26 (by simp [sampleWrites])).trans h26
  have hup := updateStep_spec G u L R n
  simp only [hufl, hufp, hu23] at hup
  obtain ⟨ht25, ht26, htW, htip⟩ :=
    hup hL hR hu20 hu24 hu25 hu26 h28 h29 hN hK hf (by omega)
  have hx : GF.xRoot p.irr ^ n = e n := by
    simp only [e, extendBasis, dif_pos hn, monoBasis, GF.xRoot]
  have hpivot : GF.rep p.irr (u.env 28) = linearizedValue (annihilatorCoefficients e n) (e n) := by
    exact he28.trans (congrArg (linearizedValue (annihilatorCoefficients e n)) hx)
  have hvalue : GF.rep p.irr (u.env 29) = linearizedValue (coordinateCoefficients e n a) (e n) := by
    exact he29.trans (congrArg (linearizedValue (coordinateCoefficients e n a)) hx)
  have hpzero : GF.rep p.irr (u.env 28) ≠ 0 := by
    rw [hpivot]
    simpa only [GF.rep_two_pow, hx] using request_pivot_ne_zero p h n hn
  have hinv := request_inverse p h (u.env 28) h28 hpzero
  rw [hpivot] at hinv
  let L' := (List.range (n + 2)).map (annValue p.irr p.f (u.env 28) L)
  let R' := (List.range (n + 1)).map
    (rowValue p.irr p.f a n (powW p.irr p.f (u.env 28) (2 ^ p.f - 2)) (u.env 29) L R)
  refine ⟨L', R', ht25, ht26, ?_, ?_, ?_, ?_, ?_, htip.trans hsip⟩
  · intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact annValue_lt p.irr p.f (u.env 28) L j
  · intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact rowValue_lt p.irr p.f a n _ (u.env 29) L R hR j
  · exact ann_values p.irr p.f (coordOk_modulusOk p h) e n (u.env 28) L hLm hpivot
  · exact row_values p.irr p.f (coordOk_modulusOk p h) e n a _ (u.env 29) L R hLm hRm hinv hvalue
  · exact (hsW.mono (by simp_all [sampleWrites, stageWrites])).trans
      (htW.mono (by simp_all [stageWrites]))

end NearCubicGates.Adapters.Routing.CoordinateMachine
