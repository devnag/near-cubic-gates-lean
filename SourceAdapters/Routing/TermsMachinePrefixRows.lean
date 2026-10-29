import SourceAdapters.Routing.TermsMachinePrefixTerms

/-! Counted coefficient and coordinate-row loops, with exact gate words. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Prefix

open ShortPCP.Machines.FL CoordinateMachine Joins

def coefficientWrites : List Var := gateWrites ++ [35]

theorem terms_spec (G : Glob) (s : FS) (f m start b a : ℕ) (cs : List ℕ)
    (hB : Bounds G f m start) (hcs : ∀ c ∈ cs, c < 2^f)
    (h20 : s.env 20 = f) (h21 : s.env 21 = m) (h22 : s.env 22 = packW f cs)
    (h33 : s.env 33 = start) (h34 : s.env 34 = a) (h36 : s.env 36 = b)
    (h24 : s.env 24 = b+1) (ha : a < m)
    (hb : b+3*m+1 ≤ start+3*m*m+2*m) :
    Appends coefficientWrites s (evalS G (.loop 35 (.v 21) termStep) s)
      (words (s.env 31) (terms m start b a m cs)) ∧
      (evalS G (.loop 35 (.v 21) termStep) s).env 24 = b+1+3*m := by
  have hm : min (evalE G s (.v 21)) G.N = m := by
    simp only [evalE, h21, min_eq_left hB.m_N]
  have h := loop_inv G (i := 35) (n := .v 21) (body := termStep) (s := s)
    (fun j t => Appends coefficientWrites s t (words (s.env 31) (terms m start b a j cs)) ∧
      t.env 24 = b+1+3*j)
    (by simpa [terms] using And.intro (Appends.refl coefficientWrites s) h24) (by
      rw [hm]
      intro j hj t ht
      let u := t.setv 35 j
      have hu : Appends coefficientWrites s u (words (s.env 31) (terms m start b a j cs)) := by
        simpa using ht.1.trans (Appends.setv coefficientWrites t 35 (by simp [coefficientWrites]) j)
      have hu20 : u.env 20 = f := (hu.env 20 (by simp [coefficientWrites, gateWrites])).trans h20
      have hu21 : u.env 21 = m := (hu.env 21 (by simp [coefficientWrites, gateWrites])).trans h21
      have hu22 : u.env 22 = packW f cs := (hu.env 22 (by simp [coefficientWrites, gateWrites])).trans h22
      have hu33 : u.env 33 = start := (hu.env 33 (by simp [coefficientWrites, gateWrites])).trans h33
      have hu34 : u.env 34 = a := (hu.env 34 (by simp [coefficientWrites, gateWrites])).trans h34
      have hu36 : u.env 36 = b := (hu.env 36 (by simp [coefficientWrites, gateWrites])).trans h36
      have hu24 : u.env 24 = b+1+3*j := by simpa [u] using ht.2
      have hu31 : u.env 31 = s.env 31 := hu.env 31 (by simp [coefficientWrites, gateWrites])
      have hc := termStep_spec G u f m start b a j cs hB hcs hu20 hu21 hu22 hu33 hu34
        (by simp [u]) hu36 hu24 ha hj hb
      refine ⟨?_, hc.2⟩
      have hh := hu.trans (hc.1.mono (by simp [coefficientWrites, gateWrites]))
      simpa only [hu31, terms_succ, words_append] using hh)
  rwa [hm] at h

theorem rowStep_spec (G : Glob) (s : FS) (f m start b a : ℕ) (cs : List ℕ)
    (hB : Bounds G f m start) (hcs : ∀ c ∈ cs, c < 2^f)
    (h20 : s.env 20 = f) (h21 : s.env 21 = m) (h22 : s.env 22 = packW f cs)
    (h33 : s.env 33 = start) (h34 : s.env 34 = a) (h24 : s.env 24 = b)
    (ha : a < m) (hb : b+3*m+1 ≤ start+3*m*m+2*m) :
    Appends rowWrites s (evalS G rowStep s) (words (s.env 31) (rowGates m start b a cs)) ∧
      (evalS G rowStep s).env 24 = b+(3*m+1) := by
  let t := s.setv 36 b
  have hc3 := hB.three_cap
  have hc := hB.gate_count
  have hzero := emitGate_spec G t 1 (.k 0) (.k 0) 0 0 (by omega)
    (by simp [evalE]) (by simp [evalE])
    (hB.bits_tag (by omega)) (hB.bits_tag (by omega)) (hB.bits_tag (by omega)) hB.K_N
    (by simp only [t, FS.setv_env, Function.update_of_ne (by decide : (24 : Var) ≠ 36), h24]; omega)
  let u := evalS G (emitGate 1 (.k 0) (.k 0)) t
  have hu : Appends rowWrites s u (words (s.env 31) [.const 0]) := by
    have hh := (Appends.setv rowWrites s 36 (by simp [rowWrites]) b).trans
      (hzero.1.mono (by simp [rowWrites, gateWrites]))
    simpa [words, gateWord, t] using hh
  have hu20 : u.env 20 = f := (hu.env 20 (by simp [rowWrites, gateWrites])).trans h20
  have hu21 : u.env 21 = m := (hu.env 21 (by simp [rowWrites, gateWrites])).trans h21
  have hu22 : u.env 22 = packW f cs := (hu.env 22 (by simp [rowWrites, gateWrites])).trans h22
  have hu33 : u.env 33 = start := (hu.env 33 (by simp [rowWrites, gateWrites])).trans h33
  have hu34 : u.env 34 = a := (hu.env 34 (by simp [rowWrites, gateWrites])).trans h34
  have hu36 : u.env 36 = b := by simpa [t] using hzero.1.env 36 (by simp [gateWrites])
  have hu24 : u.env 24 = b+1 := by simpa [t, h24] using hzero.2
  have hu31 : u.env 31 = s.env 31 := hu.env 31 (by simp [rowWrites, gateWrites])
  have hl := terms_spec G u f m start b a cs hB hcs hu20 hu21 hu22 hu33 hu34 hu36 hu24 ha hb
  have he : evalS G rowStep s = evalS G (.loop 35 (.v 21) termStep) u := by
    simp only [rowStep, evalS_seq, evalS_set, evalE, h24]
    rfl
  refine ⟨?_, ?_⟩
  · rw [he]
    have hh := hu.trans (hl.1.mono (by simp [coefficientWrites, rowWrites, gateWrites]))
    simpa only [hu31, rowGates, words_append] using hh
  · rw [he, hl.2]
    omega

end NearCubicGates.Adapters.Routing.TermsMachine.Prefix
