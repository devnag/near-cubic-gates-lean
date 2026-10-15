import Proof.Wire_3_5.ListMachineRowNeg
import Proof.Wire_3_5.ListMachineRowPopRef
import Proof.Wire_3_5.ListMachineRowWitness
import Proof.Wire_3_5.FinalPassPopList
import Proof.Wire_3_5.FinalPassSym

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly listBound eval_congr_atoms eval_renamePoly)
open NearCubicWires.WireExponent3_5.ListMachine.Print (recInnerLCost labOf PointEval)
open NearCubicWires.WireExponent3_5.FinalPass

/-- The family of C5's stage-3∘5 evaluator. -/
def F35 : EvalFam := ⟨19, _, Pop.stage35Machine⟩

theorem rowsOf_length (D : ListData) (L j : ℕ) : (ListEval.rowsOf D L j).length = L := by
  simp [ListEval.rowsOf]

/-- The member for a visited list's data `D`, state `s`, sign `sgn`, register capacity `c`. -/
def member35 (D : ListData) (L s : ℕ) (sgn : Bool) (c : ℕ) (hs : s ≤ D.M)
    (hc : ListEval.capOf D.M D.J D.W (ListEval.rowsOf D L) L ≤ c) :
    Member F35 (4 * L) (fun X => decide (ListEval.reportRef D.M D.J D.W (ListEval.rowsOf D L) (Pop.popBits sgn X) = s)) where
  data := Pop.stage35Data D.M D.J D.W (ListEval.rowsOf D L) s sgn c
  cost := Pop.stage35Cost D.M D.J D.W (ListEval.rowsOf D L) L
  step := fun X b hX => Pop.stage35_step D.M D.J D.W (ListEval.rowsOf D L) L s sgn c
    (fun j _ => rowsOf_length D L j) hs hc X b hX

/-! ## The labelled record printer's capacity -/

/-- The record printer's cost depends on the bitmap only through its length. -/
def labCost (N : ℕ) (labs : List ℕ) : ℕ := recInnerLCost (List.replicate N false) labs

theorem recInnerLCost_len (xs : List Bool) (labs : List ℕ) : recInnerLCost xs labs = labCost xs.length labs := by
  simp [labCost, recInnerLCost, Print.loopLCost]

/-! ## One visit factor -/

/-- **One visit factor** of a POP row: `P_{k,s}` (`neg = false`) or its complement `N_{k,s}` (`neg = true`) for the
visited list `D`, over the corner labels `labs`. -/
noncomputable def visitSpec (D : ListData) (L s : ℕ) (sgn : Bool) (c : ℕ) (hs : s ≤ D.M)
    (hc : ListEval.capOf D.M D.J D.W (ListEval.rowsOf D L) L ≤ c) (neg : Bool) (labs : List ℕ)
    (hlabs : 4 * L ≤ labs.length) : FSpec (negFam F35) where
  L := 4 * L
  f := fun X => xor (decide (ListEval.reportRef D.M D.J D.W (ListEval.rowsOf D L) (Pop.popBits sgn X) = s)) neg
  m := negMember F35 (member35 D L s sgn c hs hc) neg
  labs := labs
  d := 3 * listBound D
  cap1 := max (2 * (4 * L) + 1) (labCost (4 * L) labs)
  cap2 := 0
  hd := by unfold listBound; omega
  hlabs := hlabs
  hc1 := le_max_left _ _
  hc2 := fun xs hxs => by rw [recInnerLCost_len, hxs]; exact le_max_right _ _

/-- The corner word read from an assignment through the labels. -/
def readX (N : ℕ) (labs : List ℕ) (σ : ℕ → Bool) : List Bool := (List.range N).map fun i => σ (labOf labs i)

theorem readX_getD (N : ℕ) (labs : List ℕ) (σ : ℕ → Bool) (i : ℕ) (hi : i < N) :
    (readX N labs σ).getD i false = σ (labOf labs i) := by
  simp [readX, List.getElem?_range hi]

theorem pointOf_length (N : ℕ) (T : List ℕ) : (Interp.pointOf N T).length = N := by simp [Interp.pointOf]

/-- The witness of a visit factor. -/
def visitWit (D : ListData) (L s : ℕ) (sgn neg : Bool) : Poly :=
  if neg then NearCubicWires.WireExponent3_5.ListMachine.pnot (witness35 D L s sgn) else witness35 D L s sgn

theorem visitWit_eval (D : ListData) (L s : ℕ) (sgn neg : Bool) (ρ : ℕ → Bool) :
    F2Poly.eval (visitWit D L s sgn neg) ρ = xor (F2Poly.eval (witness35 D L s sgn) ρ) neg := by
  cases neg <;> simp [visitWit]

theorem visitWit_deg (D : ListData) (L s : ℕ) (sgn neg : Bool) : DegLe (visitWit D L s sgn neg) (3 * listBound D) := by
  cases neg
  · exact witness35_deg D L s sgn
  · intro m hm
    simp only [visitWit, if_true, NearCubicWires.WireExponent3_5.ListMachine.pnot, List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp
    · exact witness35_deg D L s sgn m hm

theorem visitWit_atoms (D : ListData) (L s : ℕ) (sgn neg : Bool) : AtomsLt (visitWit D L s sgn neg) (4 * L) := by
  cases neg
  · exact witness35_atoms D L s sgn
  · intro m hm
    simp only [visitWit, if_true, NearCubicWires.WireExponent3_5.ListMachine.pnot, List.mem_cons] at hm
    rcases hm with rfl | hm
    · simp
    · exact witness35_atoms D L s sgn m hm

/-- **A visit factor's value**: at every assignment `σ`, the printed factor takes the value
`xor [report_D(Z^±) = s] neg` at the population point `Z^± = popBits sgn X`, `X` read from `σ` through `labs`. -/
theorem visitSpec_eval (D : ListData) (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (L s : ℕ) (sgn : Bool) (c : ℕ) (hs : s ≤ D.M) (hc : ListEval.capOf D.M D.J D.W (ListEval.rowsOf D L) L ≤ c)
    (neg : Bool) (labs : List ℕ) (hlabs : 4 * L ≤ labs.length) (σ : ℕ → Bool) :
    F2Poly.eval (visitSpec D L s sgn c hs hc neg labs hlabs).poly σ =
      xor (decide (ListFast.listReportFast D (Pop.popBits sgn (readX (4 * L) labs σ)) = s)) neg := by
  have hren : F2Poly.eval (visitSpec D L s sgn c hs hc neg labs hlabs).poly σ =
      F2Poly.eval (Interp.interpPrint (visitSpec D L s sgn c hs hc neg labs hlabs).f (4 * L) (3 * listBound D))
        (fun i => σ (labOf labs i)) := by
    have := eval_renamePoly (labOf labs) (Interp.interpPrint (visitSpec D L s sgn c hs hc neg labs hlabs).f (4 * L)
      (3 * listBound D)) σ
    exact this
  rw [hren]
  have hi := Interp.interpPrint_eval (visitSpec D L s sgn c hs hc neg labs hlabs).f (4 * L) (3 * listBound D)
    (visitWit D L s sgn neg) (visitWit_deg D L s sgn neg) (visitWit_atoms D L s sgn neg)
    (fun T => by
      show xor _ neg = _
      rw [evalP_eq, visitWit_eval, ← corner_witness D hnest L s hs sgn _ (pointOf_length _ T)])
    (fun i => σ (labOf labs i))
  rw [evalP_eq, evalP_eq] at hi
  rw [hi, visitWit_eval]
  congr 1
  have hX : (readX (4 * L) labs σ).length = 4 * L := by simp [readX]
  rw [← ListEval.reportRef_eq_fast D L _ (Pop.popBits_length sgn L _ hX), corner_witness D hnest L s hs sgn _ hX]
  apply eval_congr_atoms (witness35_atoms D L s sgn)
  intro i hi'
  rw [readX_getD _ _ _ _ hi']

end NearCubicWires.WireExponent3_5.ListMachine.Row
