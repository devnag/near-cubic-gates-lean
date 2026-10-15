import Proof.Wire_3_5.ListMachineRowPopRec

/-! # C2 rows, part 16: the POP row's record, capacities and contract data

The POP row's self-contained record is computable (`popRowRecC`): the setup fields
with the scrub capacity `R` (above every factor stage's explicit cost bound, `costC`) and the log capacity `cap`
(above every masked stage's cost), then the population's states with their factor blocks.

* `popRowRecC_eq`: it is the record `popRow_correct` runs on;
* `popStates_ok`: every state satisfies the capacity side conditions `StateOk` at these capacities;
* **`popRow_run`**: the POP row, end to end, from its computable record, with its value theorem and its cost bound
  `2^t · 128 · (|record| + 1)^3`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord)
open NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.ExtDecompositionBatch

section
variable (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ)

/-- The visited states of a POP row: `s` (coefficient `1`), or `1, …, M` (coefficient `−1`) for the zero coordinate. -/
def statesC (s : Fin (P.M + 1)) : List (ℤ × Fin (P.M + 1)) :=
  if s.val = 0 then (List.finRange P.M).map fun i => ((-1 : ℤ), ⟨i.val + 1, by omega⟩) else [(1, s)]

/-- A state's factor blocks `[N_0, P_0, …]`. -/
def blocksC (s' : Fin (P.M + 1)) : List (List Bool) :=
  (List.finRange P.walkLen).flatMap fun k =>
    [blockC (visitData P e k) L s'.val sgn true labs, blockC (visitData P e k) L s'.val sgn false labs]

/-- A state's printed pairs `(N_k, P_k)`. -/
def pairsC (s' : Fin (P.M + 1)) : List (Poly × Poly) :=
  (List.finRange P.walkLen).map fun k =>
    (polyC (visitData P e k) L s'.val sgn true labs, polyC (visitData P e k) L s'.val sgn false labs)

/-- A state's factor-cost bounds, summed. -/
def costsC (s' : Fin (P.M + 1)) : ℕ :=
  ((List.finRange P.walkLen).map fun k =>
    costC (visitData P e k) L s'.val sgn true labs + costC (visitData P e k) L s'.val sgn false labs).sum

/-- **The scrub capacity** of the row. -/
def RC (s : Fin (P.M + 1)) : ℕ := 1 + ((statesC P s).map fun st => costsC P e L sgn labs st.2).sum

/-- The selection loop's cost of a state. -/
def selSumC (s' : Fin (P.M + 1)) : ℕ :=
  ((List.range P.walkLen).map fun j => selPass (pairsC P e L sgn labs s') j + 2).sum

/-- **The log capacity** of the row. -/
def capR (s : Fin (P.M + 1)) : ℕ :=
  ((statesC P s).map fun st => (blocksC P e L sgn labs st.2).length * (4 * RC P e L sgn labs s + 9) + 1 +
    (2 * (coefWord st.1).length + 1) + (2 * P.walkLen + 1) + (selSumC P e L sgn labs st.2 + 1)).sum

/-- The constant term's record field. -/
def oneWC (s : Fin (P.M + 1)) : List Bool := (popOne P s.val).flatMap fun t => true :: termWord t

/-- A state's record. -/
def stateRecC (st : ℤ × Fin (P.M + 1)) : List Bool :=
  true :: (frame (coefWord st.1) ++ ((blocksC P e L sgn labs st.2).flatMap (fun b => true :: b) ++ [false]))

/-- **The POP row record** (computable). -/
def popRowRecC (s : Fin (P.M + 1)) : List Bool :=
  fieldsWord (setupFields (19 + 1) P.walkLen (majorityThreshold P.walkLen) (RC P e L sgn labs s)
    (RC P e L sgn labs s + 1) (capR P e L sgn labs s)) ++
  (frame (oneWC P s) ++ ((statesC P s).flatMap (stateRecC P e L sgn labs) ++ [false]))

/-- **The POP row's reference expression** (computable). -/
def popRefC (s : Fin (P.M + 1)) : Expr :=
  popExprP (popOne P s.val) P.walkLen (majorityThreshold P.walkLen)
    ((statesC P s).map fun st => (st.1, pairsC P e L sgn labs st.2))

variable (hlabs : 4 * L ≤ labs.length)

theorem visitFs_blocks (s' : Fin (P.M + 1)) :
    (visitFs P e L sgn labs hlabs s').map FSpec.block = blocksC P e L sgn labs s' := by
  unfold visitFs blocksC
  rw [List.map_flatMap]
  congr 1

theorem visitFs_length (s' : Fin (P.M + 1)) : (visitFs P e L sgn labs hlabs s').length = 2 * P.walkLen := by
  simp [visitFs, List.length_flatMap, mul_comm]

theorem storeRec_visitFs (s' : Fin (P.M + 1)) :
    storeRec (visitFs P e L sgn labs hlabs s') = (blocksC P e L sgn labs s').flatMap (fun b => true :: b) ++ [false] := by
  rw [← visitFs_blocks P e L sgn labs hlabs s', List.flatMap_map]
  rfl

theorem statePairs_eq (s' : Fin (P.M + 1)) :
    statePairs (visitFs P e L sgn labs hlabs s') = pairsC P e L sgn labs s' := by
  rw [statePairs_visitFs]
  unfold pairsC
  congr 1

theorem popStates_eq (s : Fin (P.M + 1)) :
    popStates P e L sgn labs hlabs s = (statesC P s).map fun st => (st.1, visitFs P e L sgn labs hlabs st.2) := by
  unfold popStates statesC
  split_ifs
  · rw [List.map_map]; rfl
  · rfl

theorem popExprOf_eq (s : Fin (P.M + 1)) : popExprOf P e L sgn labs hlabs s = popRefC P e L sgn labs s := by
  unfold popExprOf popRefC
  rw [popStates_eq, List.map_map]
  congr 2
  funext st
  simp only [Function.comp_apply, statePairs_eq]

theorem popRowRecC_eq (s : Fin (P.M + 1)) :
    popRowRec P.walkLen (majorityThreshold P.walkLen) (RC P e L sgn labs s) (RC P e L sgn labs s + 1)
      (capR P e L sgn labs s) (oneWC P s) (popStates P e L sgn labs hlabs s) = popRowRecC P e L sgn labs s := by
  unfold popRowRec popRowRecC popRec
  rw [popStates_eq, List.flatMap_map]
  congr 3
  apply List.flatMap_congr
  intro st _
  simp only [srec, stateRec, storeRec_visitFs]
  rfl

theorem mem_visitFs (s' : Fin (P.M + 1)) (x : FSpec (negFam F35)) (hx : x ∈ visitFs P e L sgn labs hlabs s') :
    ∃ k : Fin P.walkLen, ∃ neg : Bool,
      x = visitSpec (visitData P e k) L s'.val sgn (capC (visitData P e k) L) (Nat.le_of_lt_succ s'.isLt) le_rfl neg labs
        hlabs := by
  unfold visitFs at hx
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact ⟨k, true, rfl⟩
  · exact ⟨k, false, rfl⟩

theorem costC_le_costsC (s' : Fin (P.M + 1)) (k : Fin P.walkLen) (neg : Bool) :
    costC (visitData P e k) L s'.val sgn neg labs ≤ costsC P e L sgn labs s' := by
  unfold costsC
  have h := List.le_sum_of_mem (List.mem_map_of_mem (f := fun k : Fin P.walkLen =>
    costC (visitData P e k) L s'.val sgn true labs + costC (visitData P e k) L s'.val sgn false labs)
    (List.mem_finRange k))
  cases neg <;> omega

theorem costsC_le_RC (s : Fin (P.M + 1)) (st : ℤ × Fin (P.M + 1)) (hst : st ∈ statesC P s) :
    costsC P e L sgn labs st.2 + 1 ≤ RC P e L sgn labs s := by
  unfold RC
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun st : ℤ × Fin (P.M + 1) => costsC P e L sgn labs st.2) hst)
  omega

theorem summand_le_capR (s : Fin (P.M + 1)) (st : ℤ × Fin (P.M + 1)) (hst : st ∈ statesC P s) :
    (blocksC P e L sgn labs st.2).length * (4 * RC P e L sgn labs s + 9) + 1 + (2 * (coefWord st.1).length + 1) +
      (2 * P.walkLen + 1) + (selSumC P e L sgn labs st.2 + 1) ≤ capR P e L sgn labs s := by
  unfold capR
  exact List.le_sum_of_mem (List.mem_map_of_mem (f := fun st : ℤ × Fin (P.M + 1) =>
    (blocksC P e L sgn labs st.2).length * (4 * RC P e L sgn labs s + 9) + 1 + (2 * (coefWord st.1).length + 1) +
      (2 * P.walkLen + 1) + (selSumC P e L sgn labs st.2 + 1)) hst)

/-- **The capacity side conditions hold** for every state of the POP row. -/
theorem popStates_ok (s : Fin (P.M + 1)) :
    ∀ st ∈ popStates P e L sgn labs hlabs s, StateOk P.walkLen (RC P e L sgn labs s) (capR P e L sgn labs s) st := by
  intro st hst
  rw [popStates_eq] at hst
  obtain ⟨st0, h0, rfl⟩ := List.mem_map.mp hst
  have hsum := summand_le_capR P e L sgn labs s st0 h0
  have hR : ∀ x ∈ visitFs P e L sgn labs hlabs st0.2, x.cost + 1 ≤ RC P e L sgn labs s := by
    intro x hx
    obtain ⟨k, neg, rfl⟩ := mem_visitFs P e L sgn labs hlabs st0.2 x hx
    have h1 := visitSpec_cost_le (visitData P e k) L st0.2.val sgn (Nat.le_of_lt_succ st0.2.isLt) neg labs hlabs
    have h2 := costC_le_costsC P e L sgn labs st0.2 k neg
    have h3 := costsC_le_RC P e L sgn labs s st0 h0
    omega
  have hlenb : (visitFs P e L sgn labs hlabs st0.2).length = (blocksC P e L sgn labs st0.2).length := by
    rw [← visitFs_blocks P e L sgn labs hlabs st0.2, List.length_map]
  unfold StateOk
  dsimp only
  refine ⟨visitFs_length P e L sgn labs hlabs st0.2, hR, ?_, by omega, by omega, ?_⟩
  · have := storeCost_le _ _ hR
    rw [hlenb] at this
    omega
  · rw [statePairs_eq]
    unfold selSumC at hsum
    omega

/-- The POP row machine (the stage-3∘5 negation family). -/
noncomputable abbrev popMachine := popRowM (negFam F35)

/-- The POP row's cost at its record. -/
noncomputable def popRowCostC (s : Fin (P.M + 1)) : ℕ :=
  popRowCost P.walkLen (majorityThreshold P.walkLen) (RC P e L sgn labs s) (RC P e L sgn labs s + 1)
    (capR P e L sgn labs s) (oneWC P s) (popStates P e L sgn labs hlabs s)

/-- **The POP row, end to end from its computable record**: the loop-body run writes `exprWord (popRefC …)`; the
reference takes the value `[flatReport(Z^±) = s]` at every assignment; the cost is at most
`2^t · 128 · (|record| + 1)^3`. -/
theorem popRow_run (hnest : ∀ h j i, P.base.inLevel h (j + 1) i = true → P.base.inLevel h j i = true)
    (s : Fin (P.M + 1)) (pre rest out B : List Bool) :
    (∃ A', Step (popMachine) (popRowCostC P e L sgn labs hlabs s)
      (Fin.addCases (qH (19 + 1) pre.length (popH (19 + 1) 0 ![0, 0, 0, 0, 0, 0, out.length, 0])) (fun _ : Fin 1 => 0))
      (Fin.addCases (qA (19 + 1) (pre ++ frame (popRowRecC P e L sgn labs s) ++ rest) (entryA (19 + 1) out B))
        (fun _ : Fin 1 => []))
      (Fin.addCases (qH (19 + 1) (pre.length + (2 * (popRowRecC P e L sgn labs s).length + 1))
        (popH (19 + 1) (popRowRecC P e L sgn labs s).length
          ![0, 0, 0, 0, 0, 0, (out ++ Rec.exprWord (popRefC P e L sgn labs s)).length, 0])) (fun _ : Fin 1 => 0)) A' ∧
      A' (Fin.castAdd 1 (inQ (19 + 1))) = pre ++ frame (popRowRecC P e L sgn labs s) ++ rest ∧
      A' (Fin.castAdd 1 (pQ (19 + 1) (eI (19 + 1) 6))) =
        NearCubicWires.RepairOrdinary.StablePartition.Workspace.overlay (out ++ Rec.exprWord (popRefC P e L sgn labs s)) B) ∧
    (∀ σ : ℕ → Bool, IntExpression.eval (popRefC P e L sgn labs s) σ =
      bitInt (decide (P.flatReport e (Pop.popBits sgn (readX (4 * L) labs σ)) = s.val))) ∧
    popRowCostC P e L sgn labs hlabs s ≤ 2 ^ P.walkLen * (128 * ((popRowRecC P e L sgn labs s).length + 1) ^ 3) := by
  obtain ⟨hrun, hval⟩ := popRow_correct P e L sgn labs hlabs hnest s pre rest out B (RC P e L sgn labs s)
    (RC P e L sgn labs s + 1) (capR P e L sgn labs s) (by unfold RC; omega) le_rfl (popStates_ok P e L sgn labs hlabs s)
  rw [show (List.flatMap (fun t => true :: termWord t) (popOne P s.val)) = oneWC P s from rfl, popRowRecC_eq,
    popExprOf_eq] at hrun
  refine ⟨hrun, fun σ => by rw [← popExprOf_eq P e L sgn labs hlabs]; exact hval σ, ?_⟩
  have := popRowCost_le P.walkLen (majorityThreshold P.walkLen) (RC P e L sgn labs s) (RC P e L sgn labs s + 1)
    (capR P e L sgn labs s) (oneWC P s) (popStates P e L sgn labs hlabs s) (popStates_ok P e L sgn labs hlabs s)
  rw [popRowRecC_eq] at this
  exact this

end

end NearCubicWires.WireExponent3_5.ListMachine.Row
