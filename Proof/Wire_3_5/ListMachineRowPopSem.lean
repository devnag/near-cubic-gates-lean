import Proof.Wire_3_5.ListMachineRowPopInst

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

section
variable (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ) (hlabs : 4 * L ≤ labs.length)

/-- The visited list of visit `k`. -/
def visitData (k : Fin P.walkLen) : ListData := P.base.data (P.decode (e.vertex k))

/-- The store of the visited state `s'`: `[N_0, P_0, …]`. -/
noncomputable def visitFs (s' : Fin (P.M + 1)) : List (FSpec (negFam F35)) :=
  (List.finRange P.walkLen).flatMap fun k =>
    [visitSpec (visitData P e k) L s'.val sgn _ (Nat.le_of_lt_succ s'.isLt) le_rfl true labs hlabs,
     visitSpec (visitData P e k) L s'.val sgn _ (Nat.le_of_lt_succ s'.isLt) le_rfl false labs hlabs]

/-- The POP row's visited states: `s` itself, or `1, …, M` with coefficient `−1` for the zero coordinate. -/
noncomputable def popStates (s : Fin (P.M + 1)) : List (SSpec (negFam F35)) :=
  if s.val = 0 then (List.finRange P.M).map fun i => ((-1 : ℤ), visitFs P e L sgn labs hlabs ⟨i.val + 1, by omega⟩)
  else [(1, visitFs P e L sgn labs hlabs s)]

/-- The POP row's constant term (the zero coordinate's `1`, padded to `t` factors). -/
def popOne (s : ℕ) : Expr := if s = 0 then [(1, List.replicate P.walkLen [[]])] else []

theorem statePairs_visitFs (s' : Fin (P.M + 1)) :
    statePairs (visitFs P e L sgn labs hlabs s') = (List.finRange P.walkLen).map fun k =>
      ((visitSpec (visitData P e k) L s'.val sgn _ (Nat.le_of_lt_succ s'.isLt) le_rfl true labs hlabs).poly,
       (visitSpec (visitData P e k) L s'.val sgn _ (Nat.le_of_lt_succ s'.isLt) le_rfl false labs hlabs).poly) := by
  unfold statePairs visitFs
  induction (List.finRange P.walkLen) with
  | nil => rfl
  | cons k l ih => simp only [List.flatMap_cons, List.map_cons, List.cons_append]; rw [pairsOf, List.nil_append, ih]

/-- The stores' pairs, by state (empty past `M`). -/
noncomputable def pssOf (s' : ℕ) : List (Poly × Poly) :=
  if h : s' ≤ P.M then statePairs (visitFs P e L sgn labs hlabs ⟨s', by omega⟩) else []

theorem popStates_pairs (s : Fin (P.M + 1)) :
    (popStates P e L sgn labs hlabs s).map (fun st => (st.1, statePairs st.2)) =
      if s.val = 0 then (List.range P.M).map (fun i => ((-1 : ℤ), pssOf P e L sgn labs hlabs (i + 1)))
      else [(1, pssOf P e L sgn labs hlabs s.val)] := by
  unfold popStates
  split_ifs with h0
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, pssOf, Fin.cast_mk]
      rw [dif_pos (by simp at h2; omega)]
  · simp only [List.map_cons, List.map_nil, pssOf]
    rw [dif_pos (Nat.le_of_lt_succ s.isLt)]

/-- **The POP row's value** at every assignment of the corner pool. -/
theorem popRow_value (hnest : ∀ h j i, P.base.inLevel h (j + 1) i = true → P.base.inLevel h j i = true)
    (s : Fin (P.M + 1)) (σ : ℕ → Bool) :
    IntExpression.eval (popExprP (popOne P s.val) P.walkLen (majorityThreshold P.walkLen)
      ((popStates P e L sgn labs hlabs s).map fun st => (st.1, statePairs st.2))) σ =
      bitInt (decide (P.flatReport e (Pop.popBits sgn (readX (4 * L) labs σ)) = s.val)) := by
  set Z := Pop.popBits sgn (readX (4 * L) labs σ) with hZ
  have hlen : ∀ s', s' ≤ P.M → (pssOf P e L sgn labs hlabs s').length = P.walkLen := by
    intro s' h; simp only [pssOf, dif_pos h, statePairs_visitFs]; simp
  have hvals : ∀ s' (h : s' ≤ P.M) (k : ℕ) (hk : k < (pssOf P e L sgn labs hlabs s').length),
      F2Poly.eval (pssOf P e L sgn labs hlabs s')[k].2 σ = decide (P.visitReport e ⟨k, (hlen s' h) ▸ hk⟩ Z = s') ∧
      F2Poly.eval (pssOf P e L sgn labs hlabs s')[k].1 σ = !decide (P.visitReport e ⟨k, (hlen s' h) ▸ hk⟩ Z = s') := by
    intro s' h k hk
    have hk' : k < P.walkLen := (hlen s' h) ▸ hk
    simp only [pssOf, dif_pos h, statePairs_visitFs, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
    have hn : ∀ j i, (visitData P e ⟨k, hk'⟩).inLevel (j + 1) i = true → (visitData P e ⟨k, hk'⟩).inLevel j i = true :=
      fun j i hh => hnest _ j i hh
    rw [visitSpec_eval _ hn, visitSpec_eval _ hn]
    simp only [FlatListParams.visitReport, base_report_eq_fast, visitData, Bool.xor_false, Bool.xor_true, hZ]
    exact ⟨rfl, rfl⟩
  have hN : ∀ s', s' ≤ P.M → ∀ q ∈ pssOf P e L sgn labs hlabs s', F2Poly.eval q.1 σ = !F2Poly.eval q.2 σ := by
    intro s' h q hq
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    rw [(hvals s' h k hk).1, (hvals s' h k hk).2]
  have key := popExpr_eval P e Z σ s.val (Nat.le_of_lt_succ s.isLt) (pssOf P e L sgn labs hlabs) hlen
    (fun s' h k hk => (hvals s' h k hk).1) hN
  rw [popStates_pairs]
  exact key

/-- The POP row's expression. -/
noncomputable def popExprOf (s : Fin (P.M + 1)) : Expr :=
  popExprP (popOne P s.val) P.walkLen (majorityThreshold P.walkLen)
    ((popStates P e L sgn labs hlabs s).map fun st => (st.1, statePairs st.2))

theorem popRow_correct (hnest : ∀ h j i, P.base.inLevel h (j + 1) i = true → P.base.inLevel h j i = true)
    (s : Fin (P.M + 1)) (pre rest out B : List Bool) (R Lg cap : ℕ) (hR1 : 1 ≤ R) (hL : R + 1 ≤ Lg)
    (hok : ∀ st ∈ popStates P e L sgn labs hlabs s, StateOk P.walkLen R cap st) :
    (∃ A', Step (popRowM (negFam F35)) (popRowCost P.walkLen (majorityThreshold P.walkLen) R Lg cap
        ((popOne P s.val).flatMap fun t => true :: Rec.termWord t) (popStates P e L sgn labs hlabs s))
      (Fin.addCases (qH (negFam F35).t pre.length (popH (negFam F35).t 0 ![0, 0, 0, 0, 0, 0, out.length, 0]))
        (fun _ : Fin 1 => 0))
      (Fin.addCases (qA (negFam F35).t (pre ++ frame (popRowRec P.walkLen (majorityThreshold P.walkLen) R Lg cap
        ((popOne P s.val).flatMap fun t => true :: Rec.termWord t) (popStates P e L sgn labs hlabs s)) ++ rest)
        (entryA (negFam F35).t out B)) (fun _ : Fin 1 => []))
      (Fin.addCases (qH (negFam F35).t (pre.length + (2 * (popRowRec P.walkLen (majorityThreshold P.walkLen) R Lg cap
        ((popOne P s.val).flatMap fun t => true :: Rec.termWord t) (popStates P e L sgn labs hlabs s)).length + 1))
        (popH (negFam F35).t (popRowRec P.walkLen (majorityThreshold P.walkLen) R Lg cap
          ((popOne P s.val).flatMap fun t => true :: Rec.termWord t) (popStates P e L sgn labs hlabs s)).length
          ![0, 0, 0, 0, 0, 0, (out ++ Rec.exprWord (popExprOf P e L sgn labs hlabs s)).length, 0]))
        (fun _ : Fin 1 => 0)) A' ∧
      A' (Fin.castAdd 1 (inQ (negFam F35).t)) = pre ++ frame (popRowRec P.walkLen (majorityThreshold P.walkLen) R Lg cap
        ((popOne P s.val).flatMap fun t => true :: Rec.termWord t) (popStates P e L sgn labs hlabs s)) ++ rest ∧
      A' (Fin.castAdd 1 (pQ (negFam F35).t (eI (negFam F35).t 6))) =
        overlay (out ++ Rec.exprWord (popExprOf P e L sgn labs hlabs s)) B) ∧
    ∀ σ : ℕ → Bool, IntExpression.eval (popExprOf P e L sgn labs hlabs s) σ =
      bitInt (decide (P.flatReport e (Pop.popBits sgn (readX (4 * L) labs σ)) = s.val)) := by
  refine ⟨?_, fun σ => popRow_value P e L sgn labs hlabs hnest s σ⟩
  have h := popRow_step (negFam F35) P.walkLen (majorityThreshold P.walkLen)
    ((popOne P s.val).flatMap fun t => true :: Rec.termWord t) (popStates P e L sgn labs hlabs s) pre rest out B R Lg cap
    hR1 hL hok
  rw [popOut_eq] at h
  exact h

end

end NearCubicWires.WireExponent3_5.ListMachine.Row
