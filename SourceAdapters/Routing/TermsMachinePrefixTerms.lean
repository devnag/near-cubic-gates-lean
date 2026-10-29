import SourceAdapters.Routing.TermsMachinePrefixBounds

/-! Exact three-gate coefficient steps and the row's counted coefficient loop. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Prefix

open NearCubicWires
open ShortPCP.Machines.FL CoordinateMachine Joins

/-- One coefficient contributes a constant, product, then running sum. -/
theorem termStep_spec (G : Glob) (s : FS) (f m start b a r : ℕ) (cs : List ℕ)
    (hB : Bounds G f m start) (hcs : ∀ c ∈ cs, c < 2^f)
    (h20 : s.env 20 = f) (h21 : s.env 21 = m) (h22 : s.env 22 = packW f cs)
    (h33 : s.env 33 = start) (h34 : s.env 34 = a) (h35 : s.env 35 = r)
    (h36 : s.env 36 = b) (h24 : s.env 24 = b+1+3*r)
    (ha : a < m) (hr : r < m) (hb : b+3*m+1 ≤ start+3*m*m+2*m) :
    Appends gateWrites s (evalS G termStep s) (words (s.env 31) (termGates m start b a r cs)) ∧
      (evalS G termStep s).env 24 = b+1+3*(r+1) := by
  have hc3 := hB.three_cap
  have hidx : b+3*r+4 ≤ start+3*m*m+2*m := by omega
  have hc := hB.gate_count
  have hcoef := word_getD_le f cs hcs (a*m+r)
  have h1 := emitGate_spec G s 1 coefficient (.k 0) (cs.getD (a*m+r) 0) 0 (by omega)
    (coefficient_eval G (s.setv 7 1) f m a r cs
      (by simpa using h20) (by simpa using h21) (by simpa using h22)
      (by simpa using h34) (by simpa using h35) hcs hB.f_pos ha hr
      hB.coefficient_index hB.word_power)
    (by simp [evalE]) (hB.bits_tag (by omega)) (hB.bits_word hcoef)
    (hB.bits_tag (by omega)) hB.K_N (by omega)
  let t := evalS G (emitGate 1 coefficient (.k 0)) s
  have ht24 : t.env 24 = b+2+3*r := by dsimp [t]; omega
  have ht33 : t.env 33 = start := (h1.1.env 33 (by simp [gateWrites])).trans h33
  have ht35 : t.env 35 = r := (h1.1.env 35 (by simp [gateWrites])).trans h35
  have ht31 : t.env 31 = s.env 31 := h1.1.env 31 (by simp [gateWrites])
  have h2 := emitGate_spec G t 3 (.sub (.v 24) (.k 1)) (.add (.v 33) (.v 35))
    (b+1+3*r) (start+r) hc3
    (by simp [evalE, ht24, min_eq_left (show 1 ≤ G.cap by omega)])
    (by simp [evalE, ht33, ht35, min_eq_left ((hB.power_index hr).trans hc)])
    (hB.bits_tag (by omega)) (hB.bits_gate (by omega)) (hB.bits_gate (hB.power_index hr))
    hB.K_N (by omega)
  let u := evalS G (emitGate 3 (.sub (.v 24) (.k 1)) (.add (.v 33) (.v 35))) t
  have hu24 : u.env 24 = b+3+3*r := by dsimp [u]; omega
  have hu36 : u.env 36 = b :=
    (h2.1.env 36 (by simp [gateWrites])).trans ((h1.1.env 36 (by simp [gateWrites])).trans h36)
  have hu35 : u.env 35 = r := (h2.1.env 35 (by simp [gateWrites])).trans ht35
  have hu31 : u.env 31 = s.env 31 := (h2.1.env 31 (by simp [gateWrites])).trans ht31
  have h3 := emitGate_spec G u 2 (.add (.v 36) (.mul (.k 3) (.v 35))) (.sub (.v 24) (.k 1))
    (b+3*r) (b+2+3*r) (by omega)
    (by simp [evalE, hu36, hu35, min_eq_left hc3,
      min_eq_left (show 3*r ≤ G.cap by omega), min_eq_left (show b+3*r ≤ G.cap by omega)])
    (by simp [evalE, hu24, min_eq_left (show 1 ≤ G.cap by omega)])
    (hB.bits_tag (by omega)) (hB.bits_gate (by omega)) (hB.bits_gate (by omega))
    hB.K_N (by omega)
  refine ⟨?_, ?_⟩
  · have hall := h1.1.trans (h2.1.trans h3.1)
    change Appends gateWrites s (evalS G termStep s) _ at hall
    by_cases hm : s.env 31 = 0 <;>
      simpa only [ht31, hu31, hm, if_true, if_false, words, termGates,
        List.flatMap_cons, List.flatMap_nil, gateWord, List.append_nil,
        List.nil_append, List.append_assoc] using hall
  · change (evalS G (emitGate 2 (.add (.v 36) (.mul (.k 3) (.v 35)))
      (.sub (.v 24) (.k 1))) u).env 24 = _
    rw [h3.2, hu24]
    omega

end NearCubicGates.Adapters.Routing.TermsMachine.Prefix
