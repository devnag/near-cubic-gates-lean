import SourceAdapters.Routing.CoordinateMachineProgram
import SourceAdapters.Routing.CoordinateMachineStage
import SourceAdapters.Routing.CoordinateMachineAlgebraOutput

/-!
# Correctness of the complete triangular row loop

The construction in `lem:generator`: the loop maintains the exact existing annihilator and coordinate coefficients after each
basis element. The invariant retains reduced numeric arrays and every preserved field of the machine state.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open ShortPCP.Machines.FL Coordinates
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.RAMACSP
open NearCubicWires.WireExponent3_5

def rowWrites : List Var := [24, 25, 26, 27, 28, 29, 30, 31, 32, 35, 36, 37, 40, 41, 42, 44, 45, 46]

theorem solveRow_spec (G : Glob) (s : FS) (p : CoordReq) (h : CoordOk p) (a : ℕ)
    (hfl : s.fl = p.f) (hfp : s.fp = p.irr) (h20 : s.env 20 = p.f)
    (h22 : s.env 22 = p.m) (h23 : s.env 23 = a)
    (hN : p.m + 1 ≤ G.N) (hK : p.f * (p.m + 1) ≤ G.K) (hw : p.f + 2 ≤ G.K) :
    letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
    let t := evalS G solveRow s
    ∃ R : List ℕ, t.env 26 = packW p.f R ∧ (∀ x ∈ R, x < 2 ^ p.f) ∧
      R.map (GF.rep p.irr) =
        List.ofFn (coordinateCoefficients (extendBasis (monoBasis (GF.toPoly p.irr) p.m)) p.m a) ∧
      Wr rowWrites s t ∧ t.ip = s.ip := by
  letI : Fact (Irreducible (GF.toPoly p.irr)) := ⟨h.1⟩
  intro t
  let e := extendBasis (monoBasis (GF.toPoly p.irr) p.m)
  have hf : 1 ≤ p.f := by have := h.2.2.2; omega
  have hc := cap_ge G
  have hc0 : min 0 G.cap = 0 := by omega
  have hc1 : min 1 G.cap = 1 := by omega
  have hp1 : 1 < 2 ^ p.f := Nat.one_lt_two_pow (by omega)
  have hrep1 : GF.rep p.irr 1 = 1 := by
    rw [GF.rep, show GF.toPoly 1 = 1 by simp [GF.toPoly]]
    exact map_one _
  let s1 := (s.setv 25 1).setv 26 0
  let P : ℕ → FS → Prop := fun n u => ∃ L R : List ℕ,
    u.env 25 = packW p.f L ∧ u.env 26 = packW p.f R ∧
      (∀ x ∈ L, x < 2 ^ p.f) ∧ (∀ x ∈ R, x < 2 ^ p.f) ∧
      L.map (GF.rep p.irr) = List.ofFn (annihilatorCoefficients e n) ∧
      R.map (GF.rep p.irr) = List.ofFn (coordinateCoefficients e n a) ∧
      Wr rowWrites s u ∧ u.ip = s.ip
  have h0 : P 0 s1 := by
    refine ⟨[1], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp [s1, packW]
    · simp [s1, packW]
    · simpa only [List.mem_singleton, forall_eq] using hp1
    · simp
    · rw [CoordinateMachineAlgebra.annihilator_base]
      simp [hrep1]
    · simp
    · exact (Wr.setv s (by decide) 1).trans (Wr.setv _ (by decide) 0)
  have hm : min (evalE G s1 (.v 22)) G.N = p.m := by
    simp only [evalE, s1, FS.setv_env, Function.update_of_ne (by decide : (22 : Var) ≠ 26),
      Function.update_of_ne (by decide : (22 : Var) ≠ 25), h22]
    omega
  have hl := loop_inv G (i := 24) (n := .v 22) (body := stageProgram) (s := s1) P h0 (by
    intro j hj u hu
    have hjm : j < p.m := by rwa [hm] at hj
    obtain ⟨L, R, hu25, hu26, hL, hR, hLm, hRm, huW, huip⟩ := hu
    have h20u : (u.setv 24 j).env 20 = p.f := by
      simp only [FS.setv_env, Function.update_of_ne (by decide : (20 : Var) ≠ 24)]
      exact (huW.env 20 (by decide)).trans h20
    have h23u : (u.setv 24 j).env 23 = a := by
      simp only [FS.setv_env, Function.update_of_ne (by decide : (23 : Var) ≠ 24)]
      exact (huW.env 23 (by decide)).trans h23
    obtain ⟨L', R', h25', h26', hL', hR', hLm', hRm', hW', hip'⟩ :=
      stage_spec G (u.setv 24 j) p h a j hjm L R hL hR hLm hRm
        (huW.fl.trans hfl) (huW.fp.trans hfp) h20u h23u (by simp)
        (by simpa using hu25) (by simpa using hu26)
        (by omega) ((Nat.mul_le_mul_left p.f (by omega : j + 2 ≤ p.m + 1)).trans hK) hw
    exact ⟨L', R', h25', h26', hL', hR', hLm', hRm',
      (huW.trans (Wr.setv u (by decide) j)).trans (hW'.mono (by decide)), hip'.trans huip⟩)
  rw [hm] at hl
  have ht : t = evalS G (.loop 24 (.v 22) stageProgram) s1 := by
    simp only [t, solveRow, evalS_seq, evalS_set, evalE, hc0, hc1]
    rfl
  rw [ht]
  obtain ⟨L, R, _, h26, _, hR, _, hRm, hW, hip⟩ := hl
  exact ⟨R, h26, hR, hRm, hW, hip⟩

end NearCubicGates.Adapters.Routing.CoordinateMachine
