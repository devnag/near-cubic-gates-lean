import SourceAdapters.Routing.TermsMachinePrefixLoops

/-! The construction in `lem:generator`: the paid coordinate-prefix printer and exact compiler list. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Prefix

open ShortPCP.Machines.FL CoordinateMachine Joins ACSP

theorem program_spec (G : Glob) (s : FS) (f m : ℕ) (cs : List ℕ)
    (hB : Bounds G f m (s.env 24)) (hcs : ∀ c ∈ cs, c < 2^f)
    (h20 : s.env 20 = f) (h21 : s.env 21 = m) (h22 : s.env 22 = packW f cs) :
    Appends writes s (evalS G program s) (words (s.env 31) (gates m (s.env 24) cs)) ∧
      (evalS G program s).env 24 = s.env 24+3*m*m+2*m ∧
      (evalS G program s).env 33 = s.env 24 := by
  let start := s.env 24
  let t := s.setv 33 start
  have hc3 := hB.three_cap
  have hc := hB.gate_count
  have hmp := hB.m_pos
  have hfirst := emitGate_spec G t 0 (.k 0) (.k 0) 0 0 (Nat.zero_le _)
    (by simp [evalE]) (by simp [evalE])
    (hB.bits_tag (by omega)) (hB.bits_tag (by omega)) (hB.bits_tag (by omega)) hB.K_N
    (by simp only [t, FS.setv_env, Function.update_of_ne (by decide : (24 : Var) ≠ 33)]; nlinarith)
  let u := evalS G (emitGate 0 (.k 0) (.k 0)) t
  have hu : Appends writes s u (words (s.env 31) [.input 0]) := by
    have hh := (Appends.setv writes s 33 (by simp [writes]) start).trans
      (hfirst.1.mono (by simp [writes, gateWrites]))
    simpa [words, gateWord, t] using hh
  have hu21 : u.env 21 = m := (hu.env 21 (by simp [writes, gateWrites])).trans h21
  have hu33 : u.env 33 = start := by simpa [t] using hfirst.1.env 33 (by simp [gateWrites])
  have hu24 : u.env 24 = start+1 := by simpa [t] using hfirst.2
  have hu31 : u.env 31 = s.env 31 := hu.env 31 (by simp [writes, gateWrites])
  have hsquare := squares_spec G u f m start hB hu21 hu33 hu24
  let v := evalS G (.loop 34 (.sub (.v 21) (.k 1)) squareStep) u
  have hv : Appends writes s v (words (s.env 31) ([.input 0] ++ squares start (m-1))) := by
    have hh := hu.trans (hsquare.1.mono (by simp [squareWrites, writes, gateWrites]))
    simpa only [hu31, words_append] using hh
  have hv20 : v.env 20 = f := (hv.env 20 (by simp [writes, gateWrites])).trans h20
  have hv21 : v.env 21 = m := (hv.env 21 (by simp [writes, gateWrites])).trans h21
  have hv22 : v.env 22 = packW f cs := (hv.env 22 (by simp [writes, gateWrites])).trans h22
  have hv33 : v.env 33 = start := (hsquare.1.env 33 (by simp [squareWrites, gateWrites])).trans hu33
  have hv31 : v.env 31 = s.env 31 := hv.env 31 (by simp [writes, gateWrites])
  have hrows := rows_spec G v f m start cs hB hcs hv20 hv21 hv22 hv33 hsquare.2
  have he : evalS G program s = evalS G (.loop 34 (.v 21) rowStep) v := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    have hh := hv.trans (hrows.1.mono (by simp [rowsWrites, writes, gateWrites]))
    simpa only [hv31, words_append, gates, start] using hh
  · rw [he]
    exact hrows.2
  · rw [he, hrows.1.env 33 (by simp [rowsWrites, gateWrites]), hv33]

/-- The generated numerical list is exactly the coordinate builder's suffix. -/
theorem program_compiles {F : Type} [Field F] (l : Layout) {e : Fin l.m → F}
    (coords : Coordinates l.m e) (encode : F → ℕ) (hzero : encode 0 = 0)
    (G : Glob) (s : FS) (f : ℕ) (cs : List ℕ) (gs : Circuit.Gates F)
    (hB : Bounds G f l.m gs.length) (hcs : ∀ c ∈ cs, c < 2^f)
    (h20 : s.env 20 = f) (h21 : s.env 21 = l.m) (h22 : s.env 22 = packW f cs)
    (h24 : s.env 24 = gs.length)
    (hcoeff : ∀ a r : Fin l.m, cs.getD (a.val*l.m+r.val) 0 = encode (coords.coeff a r)) :
    Appends writes s (evalS G program s)
      (words (s.env 31) ((Circuit.PrefixFormula.prefixGates l coords gs.length).map (codeGate encode))) ∧
      (evalS G program s).env 24 = ((compileCoordinates coords).run gs).2.length ∧
      ((compileCoordinates coords).run gs).1 =
        Circuit.PrefixFormula.rowIds l.m (gs.length+l.m) l.m := by
  have hh := program_spec G s f l.m cs (by simpa only [h24] using hB) hcs h20 h21 h22
  refine ⟨?_, ?_, ?_⟩
  · rw [gates_code l coords encode hzero gs.length cs hcoeff]
    simpa only [h24] using hh.1
  · rw [hh.2.1, h24, Circuit.PrefixFormula.compileCoordinates_length]
    ring
  · rw [Circuit.PrefixFormula.compileCoordinates_exact]

theorem program_size : szS program = 884 := by decide

theorem polynomial_cost (G : Glob) :
    costS G program ≤ 5657600 * (G.K+1)^3 * (G.N+1)^3 := by
  have hp : 1 ≤ (G.K+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hop : opc G ≤ 800*(G.K+1)^3 := by unfold opc; omega
  have hmul : 7072 * opc G ≤ 5657600*(G.K+1)^3 := by omega
  calc
    costS G program ≤ 7072 * opc G * (G.N+1)^3 := by
      simpa only [program_size] using cost_le G
    _ ≤ 5657600*(G.K+1)^3*(G.N+1)^3 := Nat.mul_le_mul_right _ hmul

end NearCubicGates.Adapters.Routing.TermsMachine.Prefix
