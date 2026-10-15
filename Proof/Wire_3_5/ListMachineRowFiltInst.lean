import Proof.Wire_3_5.ListMachineRowFiltWit

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound eval_congr_atoms eval_renamePoly)
open NearCubicWires.WireExponent3_5.ListMachine.Print (recInnerLCost labOf PointEval printGCost recSpecL)
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch

/-- The family of C5's stage-3∘7 evaluator. -/
def F37 : EvalFam := ⟨11, _, Filt.stage37Machine⟩

/-- The stage-3∘7 evaluator as a member: the table `tbl`, the threshold `thr`, the population's sign, capacity `c`. -/
def member37 (tbl : List (List (List Bool))) (thr L : ℕ) (sgn : Bool) (c : ℕ)
    (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L) (hc : Filt.capOf7 L tbl thr ≤ c) :
    Member F37 (4 * L) (fun X => Filt.tabEval thr tbl (Pop.popBits sgn X)) where
  data := Filt.stage37Data tbl thr sgn c
  cost := Filt.stage37Cost (Filt.tableWord tbl).length thr L
  step := fun X b hX => Filt.stage37_step tbl thr L sgn c hlen hc X b hX

/-- The largest visit. -/
def vmax (tbl : List (List (List Bool))) : ℕ := (tbl.map List.length).foldr max 0

theorem le_vmax : ∀ (tbl : List (List (List Bool))), ∀ vs ∈ tbl, vs.length ≤ vmax tbl
  | [], _, h => by simp at h
  | v :: tbl, vs, h => by
    simp only [List.mem_cons] at h
    simp only [vmax, List.map_cons, List.foldr_cons]
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact (le_vmax tbl vs h).trans (le_max_right _ _)

/-- The interpolation degree: above the witness's. -/
def filtDeg (tbl : List (List (List Bool))) : ℕ := 3 * (vmax tbl * tbl.length) + 1

/-- The filter as a function of the corner word. -/
def filtF (thr : ℕ) (tbl : List (List (List Bool))) (sgn : Bool) (X : List Bool) : Bool :=
  Filt.tabEval thr tbl (Pop.popBits sgn X)

/-- **The FILTER row's print** (computable). -/
def filtPolyC (thr : ℕ) (tbl : List (List (List Bool))) (L : ℕ) (sgn : Bool) (labs : List ℕ) : Poly :=
  factorPoly (filtF thr tbl sgn) (4 * L) (filtDeg tbl) labs

/-- **The print's value** at every assignment: the table's filter at the population point read through `labs`. -/
theorem filtPoly_eval (thr : ℕ) (tbl : List (List (List Bool))) (L : ℕ) (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L)
    (sgn : Bool) (labs : List ℕ) (σ : ℕ → Bool) :
    F2Poly.eval (filtPolyC thr tbl L sgn labs) σ = Filt.tabEval thr tbl (Pop.popBits sgn (readX (4 * L) labs σ)) := by
  have hren : F2Poly.eval (filtPolyC thr tbl L sgn labs) σ =
      F2Poly.eval (Interp.interpPrint (filtF thr tbl sgn) (4 * L) (filtDeg tbl)) (fun i => σ (labOf labs i)) :=
    eval_renamePoly (labOf labs) (Interp.interpPrint (filtF thr tbl sgn) (4 * L) (filtDeg tbl)) σ
  rw [hren]
  have hdeg := (filtWit_deg thr tbl sgn L (vmax tbl) hlen (le_vmax tbl)).mono (show 3 * (vmax tbl * tbl.length) ≤
    filtDeg tbl by unfold filtDeg; omega)
  have hat := filtWit_atoms thr tbl sgn L (vmax tbl) hlen (le_vmax tbl)
  have hi := Interp.interpPrint_eval (filtF thr tbl sgn) (4 * L) (filtDeg tbl) (filtWit thr tbl sgn) hdeg hat
    (fun T => by
      show Filt.tabEval thr tbl (Pop.popBits sgn (Interp.pointOf (4 * L) T)) = _
      rw [evalP_eq, filt_witness thr tbl L hlen sgn _ (pointOf_length _ T)])
    (fun i => σ (labOf labs i))
  rw [evalP_eq, evalP_eq] at hi
  rw [hi]
  have hX : (readX (4 * L) labs σ).length = 4 * L := by simp [readX]
  rw [filt_witness thr tbl L hlen sgn _ hX]
  apply eval_congr_atoms hat
  intro i hi'
  rw [readX_getD _ _ _ _ hi']

/-! ## The FILTER row on its record -/

/-- The evaluator's capacity. -/
def cap37 (tbl : List (List (List Bool))) (thr L : ℕ) : ℕ := Filt.capOf7 L tbl thr

/-- **The FILTER row record** (computable): the factor block with C5's table word as the evaluator's data. -/
def filtRecC (tbl : List (List (List Bool))) (thr L : ℕ) (sgn : Bool) (labs : List ℕ) : List Bool :=
  filterRecord (4 * L) (filtDeg tbl) labs (cap1C L labs) 0 (Filt.stage37Data tbl thr sgn (cap37 tbl thr L))

/-- **The FILTER row's reference** (computable): one term, one factor. -/
def filtRefC (tbl : List (List (List Bool))) (thr L : ℕ) (sgn : Bool) (labs : List ℕ) : Expr :=
  [(1, [filtPolyC thr tbl L sgn labs])]

/-- An explicit bound on the FILTER row's cost. -/
def filtCostC (tbl : List (List (List Bool))) (thr L : ℕ) (sgn : Bool) (labs : List ℕ) : ℕ :=
  (2 * (2 * (filtRecC tbl thr L sgn labs).length + 1) + 2) + 1 + putCost filterPre + 1 +
    (2 * loadCost (factorFields (4 * L) (filtDeg tbl) labs (cap1C L labs) 0
      (Filt.stage37Data tbl thr sgn (cap37 tbl thr L))) + 2 + 1 +
      ((4 * L + 1) ^ filtDeg tbl * 2 ^ filtDeg tbl *
        (Filt.stage37Cost (Filt.tableWord tbl).length thr L + 1 + 1 + 2 * labCost (4 * L) labs +
          100 * (4 * L + 1) ^ 2) + 3)) + 1 + putCost filterSuf

/-- **The FILTER row, end to end**: from the input cursor at `frame` of the row record,
EMPTY work tapes, the output receives `exprWord (filtRefC …)`; the reference's value at every assignment is the table's
filter at the population point; the cost is at most `filtCostC`. -/
theorem filtRow_run (tbl : List (List (List Bool))) (thr L : ℕ) (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L)
    (sgn : Bool) (labs : List ℕ) (hlabs : 4 * L ≤ labs.length) (pre rest out B : List Bool) (k : ℕ) :
    (∃ n A', n ≤ filtCostC tbl thr L sgn labs ∧ Step (filterRowM F37) n (rH F37.t pre.length (fH F37.t 0 out.length))
      (rA F37.t (pre ++ frame (filtRecC tbl thr L sgn labs) ++ rest)
        (fA [] (entryBank out B) (fun _ => []) (List.replicate k false)))
      (rH F37.t (pre.length + (2 * (filtRecC tbl thr L sgn labs).length + 1))
        (fH F37.t (filtRecC tbl thr L sgn labs).length (out ++ Rec.exprWord (filtRefC tbl thr L sgn labs)).length))
      A' ∧ A' (inR F37.t) = pre ++ frame (filtRecC tbl thr L sgn labs) ++ rest ∧
      A' (flR F37.t (outI F37.t)) = overlay (out ++ Rec.exprWord (filtRefC tbl thr L sgn labs)) B) ∧
    ∀ σ : ℕ → Bool, IntExpression.eval (filtRefC tbl thr L sgn labs) σ =
      bitInt (Filt.tabEval thr tbl (Pop.popBits sgn (readX (4 * L) labs σ))) := by
  obtain ⟨A', hs, hin, hout⟩ := filterRow_step F37 (member37 tbl thr L sgn (cap37 tbl thr L) hlen le_rfl) labs
    (filtDeg tbl) (by unfold filtDeg; omega) hlabs (cap1C L labs) 0 (le_max_left _ _)
    (fun xs hxs => by rw [recInnerLCost_len, hxs]; exact le_max_right _ _) pre rest out B k
  have hrec : filterRecord (4 * L) (filtDeg tbl) labs (cap1C L labs) 0
      (member37 tbl thr L sgn (cap37 tbl thr L) hlen le_rfl).data = filtRecC tbl thr L sgn labs := rfl
  have href : filterRef (fun X => Filt.tabEval thr tbl (Pop.popBits sgn X)) (4 * L) (filtDeg tbl) labs =
      filtRefC tbl thr L sgn labs := rfl
  rw [hrec] at hs hin
  rw [href] at hs hout
  refine ⟨⟨_, A', ?_, hs, hin, hout⟩, fun σ => ?_⟩
  · unfold filtCostC filterRowCost factorCost
    rw [hrec]
    have h := printGCost_le labs (member37 tbl thr L sgn (cap37 tbl thr L) hlen le_rfl).pe (filtDeg tbl)
      (by unfold filtDeg; omega)
    have e : (member37 tbl thr L sgn (cap37 tbl thr L) hlen le_rfl).pe.cost =
        Filt.stage37Cost (Filt.tableWord tbl).length thr L := rfl
    have e2 : (member37 tbl thr L sgn (cap37 tbl thr L) hlen le_rfl).data =
        Filt.stage37Data tbl thr sgn (cap37 tbl thr L) := rfl
    rw [e] at h
    rw [e2]
    have e3 : (4 * L + 1) ^ filtDeg tbl * 2 ^ filtDeg tbl *
        (Filt.stage37Cost (Filt.tableWord tbl).length thr L + 2 * labCost (4 * L) labs + 100 * (4 * L + 1) ^ 2) ≤
        (4 * L + 1) ^ filtDeg tbl * 2 ^ filtDeg tbl *
        (Filt.stage37Cost (Filt.tableWord tbl).length thr L + 1 + 1 + 2 * labCost (4 * L) labs +
          100 * (4 * L + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
    have hL : loadCost (factorFields (t := F37.t) (4 * L) (filtDeg tbl) labs (cap1C L labs) 0
        (Filt.stage37Data tbl thr sgn (cap37 tbl thr L))) = loadCost (factorFields (t := 11) (4 * L) (filtDeg tbl) labs
        (cap1C L labs) 0 (Filt.stage37Data tbl thr sgn (cap37 tbl thr L))) := rfl
    omega
  · have hv := filtPoly_eval thr tbl L hlen sgn labs σ
    simp only [filtRefC, IntExpression.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      List.sum_cons, List.sum_nil]
    rw [hv]
    cases Filt.tabEval thr tbl (Pop.popBits sgn (readX (4 * L) labs σ)) <;> simp [bitZ, bitInt]

end NearCubicWires.WireExponent3_5.ListMachine.Row
