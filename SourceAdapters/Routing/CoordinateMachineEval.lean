import SourceAdapters.Routing.CoordinateMachineEvalProgram

/-!
The construction in `lem:generator`: exact reduced-word evaluation of the coefficient row.
The loop uses successive squaring, not iteration up to the exponent's value.
-/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachineEval

open ShortPCP.Machines.FL NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells
open scoped BigOperators

theorem step_eq (G : Glob) (s : FS) (cs : List ℕ) (j : ℕ)
    (hcs : ∀ c ∈ cs, c < 2 ^ s.fl)
    (h20 : s.env 20 = s.fl) (h40 : s.env 40 = packW s.fl cs) (h45 : s.env 45 = j)
    (hok : fieldOk G s.fl s.fp = true) (hj : j * s.fl ≤ G.cap)
    (h44 : s.env 44 < 2 ^ s.fl) (h46 : s.env 46 < 2 ^ s.fl) :
    evalS G step s =
      (s.setv 44 (s.env 44 ^^^ mulW s.fp s.fl (cs.getD j 0) (s.env 46))).setv 46
        (mulW s.fp s.fl (s.env 46) (s.env 46)) := by
  have hc : cs.getD j 0 < 2 ^ s.fl := by
    by_cases hjc : j < cs.length
    · rw [List.getD_eq_getElem _ _ hjc]
      exact hcs _ (List.getElem_mem hjc)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.two_pow_pos _
  have he := coefficient_eval G s cs j hcs h20 h40 h45 hok hj
  have hm : evalE G s (.fmul coefficient (.v 46)) =
      mulW s.fp s.fl (cs.getD j 0) (s.env 46) := by
    simp only [evalE, he, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt h46]
  have hx : evalE G s (.fadd (.v 44) (.fmul coefficient (.v 46))) =
      s.env 44 ^^^ mulW s.fp s.fl (cs.getD j 0) (s.env 46) := by
    change (s.env 44 ^^^ evalE G s (.fmul coefficient (.v 46))) % 2 ^ s.fl = _
    rw [hm]
    apply Nat.mod_eq_of_lt
    apply Nat.xor_lt_two_pow h44
    exact redW_lt _ _ _
  simp only [step, evalS_seq, evalS_set]
  rw [hx]
  simp only [evalE, FS.setv_env,
    Function.update_of_ne (by decide : (46 : Var) ≠ 44), FS.setv_fl, FS.setv_fp,
    Nat.mod_eq_of_lt h46]

/-- The exact sum and next Frobenius power, with the entire preserved state.
The coefficient list is extended by zero if `n` exceeds its length. -/
theorem program_spec (G : Glob) (s : FS) (cs : List ℕ) (n x : ℕ)
    (hcs : ∀ c ∈ cs, c < 2 ^ s.fl)
    (h20 : s.env 20 = s.fl) (h40 : s.env 40 = packW s.fl cs)
    (h41 : s.env 41 = n) (h42 : s.env 42 = x) (hx : x < 2 ^ s.fl)
    (hok : fieldOk G s.fl s.fp = true) (hN : n ≤ G.N) (hcap : n * s.fl ≤ G.cap) :
    let t := evalS G program s
    t.env 44 < 2 ^ s.fl ∧
      GF.rep s.fp (t.env 44) =
        ∑ r ∈ Finset.range n, GF.rep s.fp (cs.getD r 0) * (GF.rep s.fp x) ^ (2 ^ r) ∧
      t.env 46 < 2 ^ s.fl ∧ GF.rep s.fp (t.env 46) = (GF.rep s.fp x) ^ (2 ^ n) ∧
      Wr [44, 45, 46] s t ∧ t.ip = s.ip := by
  intro t
  have hmod := (fl_bounds hok).2.2.1
  let s1 := (s.setv 44 0).setv 46 x
  let P : ℕ → FS → Prop := fun j u =>
    u.env 44 < 2 ^ s.fl ∧
      GF.rep s.fp (u.env 44) =
        ∑ r ∈ Finset.range j, GF.rep s.fp (cs.getD r 0) * (GF.rep s.fp x) ^ (2 ^ r) ∧
      u.env 46 < 2 ^ s.fl ∧ GF.rep s.fp (u.env 46) = (GF.rep s.fp x) ^ (2 ^ j) ∧
      Wr [44, 45, 46] s u ∧ u.ip = s.ip
  have h0 : P 0 s1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s1]
    · simp [s1]
    · simpa [s1] using hx
    · simp [s1]
    · exact (Wr.setv s (by decide) 0).trans (Wr.setv _ (by decide) x)
    · rfl
  have hcount : min (evalE G s1 (.v 41)) G.N = n := by
    simpa [evalE, s1, h41] using min_eq_left hN
  have hloop := loop_inv G (i := 45) (n := .v 41) (body := step) (s := s1) P h0 (by
    rw [hcount]
    rintro j hj u ⟨hu44, hre44, hu46, hre46, hwr, hip⟩
    have h20u : u.env 20 = s.fl := (hwr.env 20 (by decide)).trans h20
    have h40u : u.env 40 = packW s.fl cs := (hwr.env 40 (by decide)).trans h40
    have hju : j * s.fl ≤ G.cap := (Nat.mul_le_mul_right _ hj.le).trans hcap
    let u1 := u.setv 45 j
    have eu : evalS G step u1 =
        (u1.setv 44 (u.env 44 ^^^ mulW s.fp s.fl (cs.getD j 0) (u.env 46))).setv 46
          (mulW s.fp s.fl (u.env 46) (u.env 46)) := by
      have hh := step_eq G u1 cs j
        (by simpa [u1, hwr.fl] using hcs)
        (by simpa [u1, hwr.fl] using h20u)
        (by simpa [u1, hwr.fl] using h40u)
        (by simp [u1])
        (by simpa [u1, hwr.fl, hwr.fp] using hok)
        (by simpa [u1, hwr.fl] using hju)
        (by simpa [u1, hwr.fl] using hu44)
        (by simpa [u1, hwr.fl] using hu46)
      simpa [u1, hwr.fl, hwr.fp] using hh
    change P (j + 1) (evalS G step u1)
    rw [eu]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [FS.setv_env, Function.update_of_ne (by decide : (44 : Var) ≠ 46),
        Function.update_self, mulW] using Nat.xor_lt_two_pow hu44
        (redW_lt s.fp s.fl (GF.toPoly (cs.getD j 0) * GF.toPoly (u.env 46)))
    · simp only [FS.setv_env, Function.update_of_ne (by decide : (44 : Var) ≠ 46),
        Function.update_self]
      rw [GF.rep_xor, rep_mulW _ _ _ _ hmod, hre44, hre46, Finset.sum_range_succ]
    · exact redW_lt _ _ _
    · simp only [FS.setv_env, Function.update_self]
      rw [rep_mulW _ _ _ _ hmod, hre46, ← pow_two, ← pow_mul, pow_succ]
    · exact hwr.trans ((Wr.setv u (by decide) j).trans
        ((Wr.setv u1 (by decide) _).trans (Wr.setv _ (by decide) _)))
    · simpa [u1] using hip)
  rw [hcount] at hloop
  have he : t = evalS G (.loop 45 (.v 41) step) s1 := by
    simp [t, program, evalE, s1, h42]
  exact he ▸ hloop

/-- The concrete compiled Cells run at depth zero. Its postcondition preserves
all stores and call channels and represents the exact state in `program_spec`.
The initial state relation supplies the field and physical-width premises. -/
theorem runs {C : NearCubicGates.Close.Cells.Ctx} {G : Glob} (hg : GOk C G)
    (s : FS) (a : NearCubicGates.Close.Cells.DS VV MM) (hr : Rel G s a)
    (hbad : s.bad = false) (cs : List ℕ) (n x : ℕ)
    (hcs : ∀ c ∈ cs, c < 2 ^ s.fl)
    (h20 : s.env 20 = s.fl) (h40 : s.env 40 = packW s.fl cs)
    (h41 : s.env 41 = n) (h42 : s.env 42 = x) (hx : x < 2 ^ s.fl)
    (hN : n ≤ G.N) (hcap : n * s.fl ≤ G.cap) :
    NearCubicGates.Close.Cells.Hs C (compS program 0) a (38 + G.N * (7 * opc G + 57))
      (SPost G 0 (evalS G program s) a) := by
  have h := program_spec G s cs n x hcs h20 h40 h41 h42 hx hr.fok hN hcap
  rw [← cost_eq]
  exact compiled hg 0 s a (by omega) wellFormed (h.2.2.2.2.1.bad.trans hbad) hr

end NearCubicGates.Adapters.Routing.CoordinateMachineEval
