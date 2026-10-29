import SourceAdapters.Routing.CoordinateMachineSample
import SourceAdapters.Routing.CoordinateMachineEvalBridge

/-! The construction in `lem:generator`: the sampled field masks evaluate the two coefficient
vectors at the next monomial basis element, α^n. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open ShortPCP.Machines.FL NearCubicWires.WireExponent3_5

theorem sample_linearized (G : Glob) (s : FS)
    [Fact (Irreducible (GF.toPoly s.fp))]
    (L R : List ℕ) (n : ℕ)
    (cL : Fin (n + 1) → AdjoinRoot (GF.toPoly s.fp))
    (cR : Fin n → AdjoinRoot (GF.toPoly s.fp))
    (hL : ∀ c ∈ L, c < 2 ^ s.fl) (hR : ∀ c ∈ R, c < 2 ^ s.fl)
    (hLl : L.length = n + 1) (hRl : R.length = n)
    (hLm : L.map (GF.rep s.fp) = List.ofFn cL) (hRm : R.map (GF.rep s.fp) = List.ofFn cR)
    (h20 : s.env 20 = s.fl) (h24 : s.env 24 = n)
    (h25 : s.env 25 = packW s.fl L) (h26 : s.env 26 = packW s.fl R)
    (hok : fieldOk G s.fl s.fp = true) (hn : n < s.fl)
    (hN : L.length ≤ G.N) (hK : L.length * s.fl ≤ G.K) :
    let t := evalS G sampleProgram s
    t.env 27 = 2 ^ n ∧ t.env 35 = n ∧
      t.env 28 < 2 ^ s.fl ∧
      GF.rep s.fp (t.env 28) = Coordinates.linearizedValue cL ((GF.xRoot s.fp) ^ n) ∧
      t.env 29 < 2 ^ s.fl ∧
      GF.rep s.fp (t.env 29) = Coordinates.linearizedValue cR ((GF.xRoot s.fp) ^ n) ∧
      Wr sampleWrites s t ∧ t.ip = s.ip := by
  obtain ⟨h27, h35, h28, he28, h29, he29, hW, hip⟩ :=
    sample_spec G s L R n hL hR hLl hRl h20 h24 h25 h26 hok hn hN hK
  refine ⟨h27, h35, h28, ?_, h29, ?_, hW, hip⟩
  · simpa only [GF.rep_two_pow] using he28.trans
      (CoordinateMachineEval.sum_linearized L (n + 1) (GF.rep s.fp) cL (GF.rep s.fp (2 ^ n)) hLl hLm)
  · simpa only [GF.rep_two_pow] using he29.trans
      (CoordinateMachineEval.sum_linearized R n (GF.rep s.fp) cR (GF.rep s.fp (2 ^ n)) hRl hRm)

end NearCubicGates.Adapters.Routing.CoordinateMachine
