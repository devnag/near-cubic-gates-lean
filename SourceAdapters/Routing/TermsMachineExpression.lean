import SourceAdapters.Routing.TermsMachineExpressionLoop

/-! The construction in `lem:generator`: complete postfix expression printing with exact compiler output. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Expression

open NearCubicWires.RepairRepresentation (natWord)
open ShortPCP.Machines.FL CoordinateMachine Joins ACSP Circuit Circuit.Encoding

theorem tokenWords_length (ts : List TermTok) : ts.length+1 ≤ (tokenWords ts).length := by
  induction ts with
  | nil =>
      have h := natWord_pos 5
      simpa only [tokenWords, List.flatMap_nil, List.nil_append, endWord, List.length_append,
        List.length_nil, zero_add] using h.trans (Nat.le_add_right _ _)
  | cons t ts ih =>
      have ht : 1 ≤ (termTokWord t).length := by
        rw [tokenWord_eq, List.length_append]
        exact (natWord_pos _).trans (Nat.le_add_right _ _)
      have he : (tokenWords (t::ts)).length = (termTokWord t).length + (tokenWords ts).length := by
        simp [tokenWords]
      rw [he, List.length_cons]
      omega

/-- Raw expression output, exact input cursor, and its singleton result stack. -/
theorem program_spec {F : Type} (G : Glob) (s : FS) (l : Layout) (mk : F → ℕ) (e : Expr F)
    (w E D B pos Bd : ℕ) (hB : Bounds G l w E D B) (hBd : BdOk G Bd)
    (hnext : s.env 24+gateCount e ≤ E) (hdepth : gateCount e ≤ D)
    (hconst : ∀ t ∈ exprToks mk e, ConstantBound B t)
    (hat : At (s.env 10) pos (exprWord mk e)) (h14 : s.env 14 = pos)
    (hend : pos+(exprWord mk e).length ≤ Bd)
    (h23 : s.env 23 = packW w (globalBank l)) (h26 : s.env 26 = (globalBank l).length)
    (h30 : s.env 30 = w) :
    let u := evalS G program s
    Appends writes s u
      (Prefix.words (s.env 31) ((expressionGates l (s.env 24) e).map (codeGate mk))) ∧
      u.env 14 = pos+(exprWord mk e).length ∧ u.env 24 = s.env 24+gateCount e ∧
      u.env 28 = s.env 24+gateCount e-1 ∧ u.env 29 = 1 ∧ u.env 40 = 0 := by
  let t := ((s.setv 28 0).setv 29 0).setv 40 1
  have ht : Appends writes s t [] := by
    simpa using (Appends.setv writes s 28 (by simp [writes]) 0).trans
      ((Appends.setv writes _ 29 (by simp [writes]) 0).trans
        (Appends.setv writes _ 40 (by simp [writes]) 1))
  have hword : tokenWords (exprToks mk e) = exprWord mk e := rfl
  have hfuel : (exprToks mk e).length+1 ≤ G.N := by
    have hl := tokenWords_length (exprToks mk e)
    rw [hword] at hl
    have hb := hBd.2
    omega
  have hr := runWhile_spec G l w E D B Bd hB hBd (exprToks mk e) t G.N (s.env 24) pos []
    hfuel (by simp [t]) (valid_expression l mk e (s.env 24) [] []) hconst
    (by simpa only [exprToks_length] using hnext)
    (by simpa only [List.length_nil, zero_add, exprToks_length] using hdepth)
    (by simp) (by simpa only [t, FS.setv_env, Function.update_of_ne (by decide : (10 : Var) ≠ 40),
      Function.update_of_ne (by decide : (10 : Var) ≠ 29),
      Function.update_of_ne (by decide : (10 : Var) ≠ 28), hword] using hat)
    (by simpa [t] using h14) (by simpa only [hword] using hend)
    (by simpa [t] using h23) (by simpa [t] using h26)
    (by simp [t, packW]) (by simp [t]) (by simpa [t] using h30) (by simp [t])
  have he : evalS G program s = whileN (fun u => u.env 40 != 0) (evalS G body) G.N t := by
    have hc := hB.five
    simp only [program, evalS_seq, evalE, Nat.zero_min,
      min_eq_left (show 1 ≤ G.cap by omega), loopProgram, evalS]
    rfl
  simp only [trace_expression] at hr
  dsimp only
  rw [he]
  refine ⟨?_, ?_, hr.2.2.1, ?_, hr.2.1, hr.2.2.2.2.1⟩
  · have hh := ht.trans hr.2.2.2.2.2
    simpa only [t, FS.setv_env, Function.update_of_ne (by decide : (31 : Var) ≠ 40),
      Function.update_of_ne (by decide : (31 : Var) ≠ 29),
      Function.update_of_ne (by decide : (31 : Var) ≠ 28), List.nil_append,
      expression_code] using hh
  · simpa only [hword] using hr.2.2.2.1
  · simpa [packW] using hr.1

/-- All constants may be bounded at their common encoding width. -/
theorem program_spec_of_constants {F : Type} (G : Glob) (s : FS) (l : Layout)
    (mk : F → ℕ) (e : Expr F) (w E D B pos Bd : ℕ)
    (hB : Bounds G l w E D B) (hBd : BdOk G Bd)
    (hnext : s.env 24+gateCount e ≤ E) (hdepth : gateCount e ≤ D)
    (hconst : ∀ c, mk c ≤ B)
    (hat : At (s.env 10) pos (exprWord mk e)) (h14 : s.env 14 = pos)
    (hend : pos+(exprWord mk e).length ≤ Bd)
    (h23 : s.env 23 = packW w (globalBank l)) (h26 : s.env 26 = (globalBank l).length)
    (h30 : s.env 30 = w) :
    let u := evalS G program s
    Appends writes s u
      (Prefix.words (s.env 31) ((expressionGates l (s.env 24) e).map (codeGate mk))) ∧
      u.env 14 = pos+(exprWord mk e).length ∧ u.env 24 = s.env 24+gateCount e ∧
      u.env 28 = s.env 24+gateCount e-1 ∧ u.env 29 = 1 ∧ u.env 40 = 0 :=
  program_spec G s l mk e w E D B pos Bd hB hBd hnext hdepth
    (constants_expression mk e B hconst) hat h14 hend h23 h26 h30

theorem program_size : szS program = 1119 := by decide

theorem polynomial_cost (G : Glob) :
    costS G program ≤ 7161600*(G.K+1)^3*(G.N+1)^2 := by
  have hp : 1 ≤ (G.K+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hop : opc G ≤ 800*(G.K+1)^3 := by unfold opc; omega
  have hmul : 8952*opc G ≤ 7161600*(G.K+1)^3 := by omega
  calc
    costS G program ≤ 8952*opc G*(G.N+1)^2 := by
      simpa only [program_size] using cost_le G
    _ ≤ 7161600*(G.K+1)^3*(G.N+1)^2 := Nat.mul_le_mul_right _ hmul

end NearCubicGates.Adapters.Routing.TermsMachine.Expression
