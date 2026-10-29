import SourceAdapters.Routing.CoordinateMachineEval
import SourceAdapters.Routing.CoordinatesLinearized

/-!
The construction in `lem:generator`: the machine's packed-list sum is the
same linearized evaluation used by the coordinate solver.
-/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachineEval

open ShortPCP.Machines.FL NearCubicWires.WireExponent3_5
open scoped BigOperators

theorem sum_linearized {F : Type*} [Field F] (cs : List ℕ) (n : ℕ)
    (encode : ℕ → F) (c : Fin n → F) (x : F)
    (hlen : cs.length = n) (hmap : cs.map encode = List.ofFn c) :
    (∑ r ∈ Finset.range n, encode (cs.getD r 0) * x ^ (2 ^ r)) =
      Coordinates.linearizedValue c x := by
  have hc (i : Fin n) : encode (cs.getD i.val 0) = c i := by
    have hi : i.val < cs.length := by rw [hlen]; exact i.isLt
    have hm := congrArg (fun l : List F => l.getD i.val 0) hmap
    have hml : (cs.map encode).getD i.val 0 = encode (cs.getD i.val 0) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi]
    rw [hml] at hm
    simpa [List.getD_eq_getElem] using hm
  rw [← Fin.sum_univ_eq_sum_range]
  unfold Coordinates.linearizedValue
  apply Finset.sum_congr rfl
  intro i _
  rw [hc]

/-- Direct coordinate-solver form of the evaluator's semantic theorem. -/
theorem program_linearized (G : Glob) (s : FS)
    [Fact (Irreducible (GF.toPoly s.fp))]
    (cs : List ℕ) (x : ℕ) (c : Fin cs.length → AdjoinRoot (GF.toPoly s.fp))
    (hcs : ∀ a ∈ cs, a < 2 ^ s.fl)
    (hmap : cs.map (GF.rep s.fp) = List.ofFn c)
    (h20 : s.env 20 = s.fl) (h40 : s.env 40 = packW s.fl cs)
    (h41 : s.env 41 = cs.length) (h42 : s.env 42 = x) (hx : x < 2 ^ s.fl)
    (hok : fieldOk G s.fl s.fp = true) (hN : cs.length ≤ G.N)
    (hcap : cs.length * s.fl ≤ G.cap) :
    let t := evalS G program s
    t.env 44 < 2 ^ s.fl ∧
      GF.rep s.fp (t.env 44) = Coordinates.linearizedValue c (GF.rep s.fp x) ∧
      t.env 46 < 2 ^ s.fl ∧ GF.rep s.fp (t.env 46) = (GF.rep s.fp x) ^ (2 ^ cs.length) ∧
      Wr [44, 45, 46] s t ∧ t.ip = s.ip := by
  have h := program_spec G s cs cs.length x hcs h20 h40 h41 h42 hx hok hN hcap
  exact ⟨h.1, h.2.1.trans (sum_linearized cs cs.length (GF.rep s.fp) c
    (GF.rep s.fp x) rfl hmap), h.2.2⟩

end NearCubicGates.Adapters.Routing.CoordinateMachineEval
