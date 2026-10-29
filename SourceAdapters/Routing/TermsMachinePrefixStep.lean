import SourceAdapters.Routing.TermsMachinePrefixProgram

/-! Exact single-gate output and bounded row-major coefficient access. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Prefix

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open ShortPCP.Machines.FL CoordinateMachine

/-- The staged argument evaluations account for both argument-register writes. -/
theorem emitGate_spec (G : Glob) (s : FS) (tag : ℕ) (x y : E) (xv yv : ℕ)
    (htag : tag ≤ G.cap)
    (hx : evalE G (s.setv 7 tag) x = xv)
    (hy : evalE G ((s.setv 7 tag).setv 8 xv) y = yv)
    (h7 : natBitLength tag + 2 ≤ G.K)
    (h8 : natBitLength xv + 2 ≤ G.K)
    (h9 : natBitLength yv + 2 ≤ G.K) (hN : G.K ≤ G.N)
    (hcounter : s.env 24 + 1 ≤ G.cap) :
    Appends gateWrites s (evalS G (emitGate tag x y) s)
      (if s.env 31 = 0 then [] else natWord tag ++ natWord xv ++ natWord yv) ∧
      (evalS G (emitGate tag x y) s).env 24 = s.env 24 + 1 := by
  let t := ((s.setv 7 tag).setv 8 xv).setv 9 yv
  have ht : evalS G (emitGate tag x y) s = evalS G gateStep t := by
    simp only [emitGate, evalS_seq, evalS_set, evalE, min_eq_left htag, hx, hy, t]
  have h := gateStep_spec G t (by simpa [t] using h7) (by simpa [t] using h8)
    (by simpa [t] using h9) hN (by simpa [t] using hcounter)
  have hs : Appends gateWrites s t [] := by
    simpa using (Appends.setv gateWrites s 7 (by simp [gateWrites]) tag).trans
      ((Appends.setv gateWrites (s.setv 7 tag) 8 (by simp [gateWrites]) xv).trans
        (Appends.setv gateWrites ((s.setv 7 tag).setv 8 xv) 9 (by simp [gateWrites]) yv))
  refine ⟨?_, ?_⟩
  · rw [ht]
    simpa [t] using hs.trans (h.1.mono (by simp [gateWrites]))
  · simpa [ht, t] using h.2

theorem coefficient_eval (G : Glob) (s : FS) (f m a r : ℕ) (cs : List ℕ)
    (h20 : s.env 20 = f) (h21 : s.env 21 = m) (h22 : s.env 22 = packW f cs)
    (h34 : s.env 34 = a) (h35 : s.env 35 = r)
    (hcs : ∀ c ∈ cs, c < 2^f) (hf : 1 ≤ f)
    (ha : a < m) (hr : r < m) (hcap : m*m*f ≤ G.cap) (hpow : 2^f ≤ G.cap) :
    evalE G s coefficient = cs.getD (a*m+r) 0 := by
  have ham : a*m ≤ m*m := Nat.mul_le_mul_right m (by omega)
  have hi : a*m+r ≤ m*m := by nlinarith
  have hmm : m*m ≤ G.cap := le_trans (Nat.le_mul_of_pos_right _ hf) hcap
  have hf' : (a*m+r)*f ≤ G.cap := le_trans (Nat.mul_le_mul_right f hi) hcap
  have hc1 : 1 ≤ G.cap := le_trans Nat.one_le_two_pow hpow
  simp only [coefficient, evalE, h20, h21, h22, h34, h35,
    min_eq_left (le_trans ham hmm), min_eq_left (le_trans hi hmm), min_eq_left hf',
    min_eq_left hc1, one_mul, min_eq_left hpow]
  exact packW_get f cs hcs (a*m+r)

end NearCubicGates.Adapters.Routing.TermsMachine.Prefix
