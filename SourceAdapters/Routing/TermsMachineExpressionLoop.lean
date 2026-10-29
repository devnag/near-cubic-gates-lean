import SourceAdapters.Routing.TermsMachineExpressionBody

/-! The bounded while loop consumes a valid token list and its end marker. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Expression

open ShortPCP.Machines.FL CoordinateMachine Joins ACSP

theorem runWhile_spec (G : Glob) (l : Layout) (w E D B Bd : ℕ)
    (hB : Bounds G l w E D B) (hBd : BdOk G Bd)
    (ts : List TermTok) (s : FS) (fuel n pos : ℕ) (st : List ℕ)
    (hfuel : ts.length+1 ≤ fuel) (h40 : s.env 40 ≠ 0)
    (hvalid : Valid l ts ⟨n, st, []⟩)
    (hconst : ∀ t ∈ ts, ConstantBound B t)
    (hnext : n+ts.length ≤ E) (hdepth : st.length+ts.length ≤ D)
    (hstack : ∀ a ∈ st, a < E)
    (hat : At (s.env 10) pos (tokenWords ts)) (h14 : s.env 14 = pos)
    (hend : pos+(tokenWords ts).length ≤ Bd)
    (h23 : s.env 23 = packW w (globalBank l)) (h26 : s.env 26 = (globalBank l).length)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n) :
    let u := whileN (fun t => t.env 40 != 0) (evalS G body) fuel s
    u.env 28 = packW w (trace l ts n st).stack ∧
      u.env 29 = (trace l ts n st).stack.length ∧ u.env 24 = (trace l ts n st).next ∧
      u.env 14 = pos+(tokenWords ts).length ∧ u.env 40 = 0 ∧
      Appends writes s u (Prefix.words (s.env 31) ((trace l ts n st).gates.map (codeGate id))) := by
  induction ts generalizing s fuel n pos st with
  | nil =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          obtain ⟨u40, u14, hu⟩ := body_end G s pos Bd (by simpa [tokenWords] using hat)
            h14 (by simpa [tokenWords] using hend) hBd hB.five
          generalize he : evalS G body s = u at u40 u14 hu
          have hrun : whileN (fun t => t.env 40 != 0) (evalS G body) (fuel+1) s = u := by
            simp only [whileN, show (s.env 40 != 0) = true by simpa using h40, if_true, he]
            exact whileN_stopped G fuel u u40
          dsimp only
          rw [hrun]
          refine ⟨?_, ?_, ?_, ?_, u40, ?_⟩
          · exact (hu.env 28 (by decide)).trans h28
          · exact (hu.env 29 (by decide)).trans h29
          · exact (hu.env 24 (by decide)).trans h24
          · simpa [tokenWords] using u14
          · simpa [trace] using hu.mono (W' := writes) (by simp [writes, endWrites, tokenReadWrites])
  | cons t ts ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hv : popCount t ≤ st.length ∧ Valid l ts (tokenStep l ⟨n, st, []⟩ t) := hvalid
          have hn : n < E := by simp only [List.length_cons] at hnext; omega
          have hd : st.length ≤ D := by omega
          have hword : tokenWords (t::ts) = termTokWord t ++ tokenWords ts := by
            simp [tokenWords, List.append_assoc]
          have hats := At.append (hword ▸ hat)
          have hlen : pos+(termTokWord t).length+(tokenWords ts).length ≤ Bd := by
            simpa only [hword, List.length_append, Nat.add_assoc] using hend
          obtain ⟨u28, u29, u24, u14, hu⟩ := body_step G s l w n pos Bd st t hB.toDispatchBounds
            hats.1 h14 (by omega) hBd h23 h26 h28 h29 h30 h24
            (fun a ha => (hstack a ha).trans_le hB.gate_width)
            (hB.push_cap n st (popCount t) hn hstack hd)
            (by have := hB.stack_depth; omega)
            (hB.gateFits st t hstack (hconst t (by simp)))
            (by have := hB.gate_width.trans hB.width_power; omega)
          generalize he : evalS G body s = u at u28 u29 u24 u14 hu
          have hu10 : u.env 10 = s.env 10 := hu.env 10 (by decide)
          have hu23 : u.env 23 = packW w (globalBank l) := (hu.env 23 (by decide)).trans h23
          have hu26 : u.env 26 = (globalBank l).length := (hu.env 26 (by decide)).trans h26
          have hu30 : u.env 30 = w := (hu.env 30 (by decide)).trans h30
          have hu31 : u.env 31 = s.env 31 := hu.env 31 (by decide)
          have hu40 : u.env 40 ≠ 0 := by rw [hu.env 40 (by decide)]; exact h40
          have hv' : Valid l ts ⟨n+1, n::st.drop (popCount t), []⟩ := by
            have hh := hv.2
            rw [tokenStep_eq l ⟨n, st, []⟩ t hv.1] at hh
            exact (valid_irrel_gates l ts (n+1) (n::st.drop (popCount t)) _ []).mp hh
          have hs' : ∀ a ∈ n::st.drop (popCount t), a < E := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hn
            · exact hstack a (List.mem_of_mem_drop ha)
          have hdepth' : (n::st.drop (popCount t)).length+ts.length ≤ D := by
            simp only [List.length_cons, List.length_drop] at hdepth ⊢
            omega
          have hr := ih u fuel (n+1) (pos+(termTokWord t).length) (n::st.drop (popCount t))
            (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hfuel) hu40 hv'
            (fun t ht => hconst t (by simp [ht]))
            (by simp only [List.length_cons] at hnext; omega) hdepth' hs'
            (by simpa only [hu10] using hats.2) u14 hlen hu23 hu26 u28
            (by simpa using u29) hu30 u24
          have hrun : whileN (fun t => t.env 40 != 0) (evalS G body) (fuel+1) s =
              whileN (fun t => t.env 40 != 0) (evalS G body) fuel u := by
            simp only [whileN, show (s.env 40 != 0) = true by simpa using h40, if_true, he]
          dsimp only
          rw [hrun, trace_cons l t ts n st hv.1]
          refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, hr.2.2.2.2.1, ?_⟩
          · rw [hr.2.2.2.1, hword, List.length_append]
            omega
          · have hw := (hu.mono (W' := writes) (by simp [stepWrites, tokenReadWrites, dispatchWrites, writes])).trans
              hr.2.2.2.2.2
            change Appends writes s _ (Prefix.words (s.env 31)
              ([codeGate id (emittedGate l st t)] ++
                (trace l ts (n+1) (n::st.drop (popCount t))).gates.map (codeGate id)))
            rw [Prefix.words_append]
            simpa only [hu31] using hw

end NearCubicGates.Adapters.Routing.TermsMachine.Expression
