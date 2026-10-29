import SourceAdapters.Routing.TermsMachinePrefixRows

/-! Exact power and row loops of the coordinate-prefix printer. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Prefix

open ShortPCP.Machines.FL CoordinateMachine Joins

def squareWrites : List Var := gateWrites ++ [34]
def rowsWrites : List Var := gateWrites ++ [34, 35, 36]

theorem squareStep_spec (G : Glob) (s : FS) (f m start r : ℕ)
    (hB : Bounds G f m start) (h33 : s.env 33 = start) (h34 : s.env 34 = r)
    (h24 : s.env 24 = start+1+r) (hr : r < m) :
    Appends gateWrites s (evalS G squareStep s)
      (words (s.env 31) [.mul (start+r) (start+r)]) ∧
      (evalS G squareStep s).env 24 = start+1+(r+1) := by
  have hc := hB.gate_count
  have hp := hB.power_index hr
  have hh := emitGate_spec G s 3 (.add (.v 33) (.v 34)) (.add (.v 33) (.v 34))
    (start+r) (start+r) hB.three_cap
    (by simp [evalE, h33, h34, min_eq_left (hp.trans hc)])
    (by simp [evalE, h33, h34, min_eq_left (hp.trans hc)])
    (hB.bits_tag (by omega)) (hB.bits_gate hp) (hB.bits_gate hp) hB.K_N (by omega)
  refine ⟨?_, ?_⟩
  · simpa [squareStep, words, gateWord] using hh.1
  · simpa only [squareStep, h24, Nat.add_assoc] using hh.2

theorem squares_spec (G : Glob) (s : FS) (f m start : ℕ)
    (hB : Bounds G f m start) (h21 : s.env 21 = m) (h33 : s.env 33 = start)
    (h24 : s.env 24 = start+1) :
    Appends squareWrites s (evalS G (.loop 34 (.sub (.v 21) (.k 1)) squareStep) s)
      (words (s.env 31) (squares start (m-1))) ∧
      (evalS G (.loop 34 (.sub (.v 21) (.k 1)) squareStep) s).env 24 = start+m := by
  have hc3 := hB.three_cap
  have hmN := hB.m_N
  have hmp := hB.m_pos
  have hm : min (evalE G s (.sub (.v 21) (.k 1))) G.N = m-1 := by
    simp only [evalE, h21, min_eq_left (show 1 ≤ G.cap by omega)]
    omega
  have h := loop_inv G (i := 34) (n := .sub (.v 21) (.k 1)) (body := squareStep) (s := s)
    (fun j t => Appends squareWrites s t (words (s.env 31) (squares start j)) ∧
      t.env 24 = start+1+j)
    (by simpa [squares] using And.intro (Appends.refl squareWrites s) h24) (by
      rw [hm]
      intro j hj t ht
      let u := t.setv 34 j
      have hu : Appends squareWrites s u (words (s.env 31) (squares start j)) := by
        simpa using ht.1.trans (Appends.setv squareWrites t 34 (by simp [squareWrites]) j)
      have hu33 : u.env 33 = start := (hu.env 33 (by simp [squareWrites, gateWrites])).trans h33
      have hu24 : u.env 24 = start+1+j := by simpa [u] using ht.2
      have hu31 : u.env 31 = s.env 31 := hu.env 31 (by simp [squareWrites, gateWrites])
      have hh := squareStep_spec G u f m start j hB hu33 (by simp [u]) hu24 (by omega)
      refine ⟨?_, hh.2⟩
      have hw := hu.trans (hh.1.mono (by simp [squareWrites, gateWrites]))
      simpa only [hu31, squares_succ, words_append] using hw)
  rw [hm] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  omega

theorem rows_spec (G : Glob) (s : FS) (f m start : ℕ) (cs : List ℕ)
    (hB : Bounds G f m start) (hcs : ∀ c ∈ cs, c < 2^f)
    (h20 : s.env 20 = f) (h21 : s.env 21 = m) (h22 : s.env 22 = packW f cs)
    (h33 : s.env 33 = start) (h24 : s.env 24 = start+m) :
    Appends rowsWrites s (evalS G (.loop 34 (.v 21) rowStep) s)
      (words (s.env 31) (rows m start m cs)) ∧
      (evalS G (.loop 34 (.v 21) rowStep) s).env 24 = start+3*m*m+2*m := by
  have hm : min (evalE G s (.v 21)) G.N = m := by
    simp only [evalE, h21, min_eq_left hB.m_N]
  have h := loop_inv G (i := 34) (n := .v 21) (body := rowStep) (s := s)
    (fun j t => Appends rowsWrites s t (words (s.env 31) (rows m start j cs)) ∧
      t.env 24 = start+m+j*(3*m+1))
    (by simpa [rows] using And.intro (Appends.refl rowsWrites s) h24) (by
      rw [hm]
      intro j hj t ht
      let u := t.setv 34 j
      have hu : Appends rowsWrites s u (words (s.env 31) (rows m start j cs)) := by
        simpa using ht.1.trans (Appends.setv rowsWrites t 34 (by simp [rowsWrites]) j)
      have hu20 : u.env 20 = f := (hu.env 20 (by simp [rowsWrites, gateWrites])).trans h20
      have hu21 : u.env 21 = m := (hu.env 21 (by simp [rowsWrites, gateWrites])).trans h21
      have hu22 : u.env 22 = packW f cs := (hu.env 22 (by simp [rowsWrites, gateWrites])).trans h22
      have hu33 : u.env 33 = start := (hu.env 33 (by simp [rowsWrites, gateWrites])).trans h33
      have hu24 : u.env 24 = start+m+j*(3*m+1) := by simpa [u] using ht.2
      have hu31 : u.env 31 = s.env 31 := hu.env 31 (by simp [rowsWrites, gateWrites])
      have hh := rowStep_spec G u f m start (start+m+j*(3*m+1)) j cs hB hcs hu20 hu21 hu22
        hu33 (by simp [u]) hu24 hj (hB.row_end hj)
      refine ⟨?_, ?_⟩
      · have hw := hu.trans (hh.1.mono (by simp [rowsWrites, rowWrites, gateWrites]))
        simpa only [hu31, rows_succ, words_append] using hw
      · rw [hh.2]
        ring)
  rw [hm] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  ring

end NearCubicGates.Adapters.Routing.TermsMachine.Prefix
