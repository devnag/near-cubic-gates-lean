import SourceAdapters.Routing.CoordinateMachineRows

/-!
# Row-major output of the coordinate array

The construction in `lem:generator`: after each iterative solve the reduced representatives identify the exact requested row. The
outer counted loop appends every row to the same output, preserving the parsed request throughout the computation.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins
open NearCubicWires

def arrayWrites : List Var :=
  [0, 1, 2, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 35, 36, 37, 40, 41, 42, 44, 45, 46]

noncomputable def rowBits (p : CoordReq) (h : CoordOk p) (a : Fin p.m) : List Bool :=
  (List.finRange p.m).flatMap fun r => WilliamsLoaderForms.fixedWidthNatBits p.f (coordMask p h a r)

theorem solvePrintRow_spec (G : Glob) (s : FS) (p : CoordReq) (h : CoordOk p) (a : Fin p.m)
    (hfl : s.fl = p.f) (hfp : s.fp = p.irr) (h20 : s.env 20 = p.f)
    (h22 : s.env 22 = p.m) (h23 : s.env 23 = a.val)
    (hN : p.m + 1 ≤ G.N) (hfN : p.f ≤ G.N) (hK : p.f * (p.m + 1) ≤ G.K)
    (hw : p.f + 2 ≤ G.K) (hpow : 2 ^ p.f ≤ G.cap) (hc : 2 ≤ G.cap) :
    Appends arrayWrites s (evalS G (.seq solveRow rowEmit) s) (rowBits p h a) := by
  let u := evalS G solveRow s
  obtain ⟨R, h26, hR, hRm, hW, hip⟩ := solveRow_spec G s p h a.val hfl hfp h20 h22 h23 hN hK hw
  have hlen := CoordinateMachineAlgebra.completed_row_length p h a R hRm
  have h20u : u.env 20 = p.f := (hW.env 20 (by decide)).trans h20
  have h22u : u.env 22 = R.length := (hW.env 22 (by decide)).trans (h22.trans hlen.symm)
  have hmf : R.length * p.f ≤ G.cap := by
    rw [hlen]
    have hh : p.m * p.f ≤ p.f * (p.m + 1) := by nlinarith
    exact hh.trans (hK.trans (cap_ge G))
  have hout := rowEmit_spec G u p.f R h20u h22u h26 hR (by omega) hfN hmf hpow hc
  have hpre : Appends arrayWrites s u [] := by
    have hw' := hW.mono (by decide : ∀ i ∈ rowWrites, i ∈ arrayWrites)
    exact ⟨hw'.env, by simpa using hw'.out, hw'.fl, hw'.fp, hip, hw'.bad⟩
  have hb := CoordinateMachineAlgebra.completed_row_bits p h a R hR hRm
  have hall := hpre.trans (hout.mono (by decide : ∀ i ∈ ([0, 1, 2] : List Var), i ∈ arrayWrites))
  simpa only [List.nil_append, hb, rowBits, evalS_seq, u] using hall

theorem rowPrefix_succ (p : CoordReq) (h : CoordOk p) (j : ℕ) (hj : j < p.m) :
    ((List.finRange p.m).take (j + 1)).flatMap (rowBits p h) =
      ((List.finRange p.m).take j).flatMap (rowBits p h) ++ rowBits p h ⟨j, hj⟩ := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hj), Option.toList_some,
    List.flatMap_append]
  simp

theorem solveArray_spec (G : Glob) (s : FS) (p : CoordReq) (h : CoordOk p)
    (hfl : s.fl = p.f) (hfp : s.fp = p.irr) (h20 : s.env 20 = p.f) (h22 : s.env 22 = p.m)
    (hN : p.m + 1 ≤ G.N) (hfN : p.f ≤ G.N) (hK : p.f * (p.m + 1) ≤ G.K)
    (hw : p.f + 2 ≤ G.K) (hpow : 2 ^ p.f ≤ G.cap) (hc : 2 ≤ G.cap) :
    Appends arrayWrites s (evalS G solveArray s) (coordWord p h) := by
  have hm : min (evalE G s (.v 22)) G.N = p.m := by simp only [evalE, h22]; omega
  have hl := loop_inv G (i := 23) (n := .v 22) (body := .seq solveRow rowEmit) (s := s)
    (fun j u => Appends arrayWrites s u (((List.finRange p.m).take j).flatMap (rowBits p h)))
    (by simpa using Appends.refl arrayWrites s) (by
      intro j hj u hu
      have hjm : j < p.m := by rwa [hm] at hj
      have h20u : (u.setv 23 j).env 20 = p.f := by
        simp only [FS.setv_env, Function.update_of_ne (by decide : (20 : Var) ≠ 23)]
        exact (hu.env 20 (by decide)).trans h20
      have h22u : (u.setv 23 j).env 22 = p.m := by
        simp only [FS.setv_env, Function.update_of_ne (by decide : (22 : Var) ≠ 23)]
        exact (hu.env 22 (by decide)).trans h22
      have hp := solvePrintRow_spec G (u.setv 23 j) p h ⟨j, hjm⟩
        (hu.fl.trans hfl) (hu.fp.trans hfp) h20u h22u (by simp)
        hN hfN hK hw hpow hc
      have hall := hu.trans ((Appends.setv arrayWrites u 23 (by decide) j).trans hp)
      simpa only [List.nil_append, rowPrefix_succ p h j hjm] using hall)
  rw [hm] at hl
  have ht : (List.finRange p.m).take p.m = List.finRange p.m := List.take_of_length_le (by simp)
  rw [ht] at hl
  exact hl

end NearCubicGates.Adapters.Routing.CoordinateMachine
