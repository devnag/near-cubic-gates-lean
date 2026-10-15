import Proof.Wire_3_5.ListMachineRowPopSem
import Proof.Wire_3_5.ListMachineRowCost

/-! # C2 rows, part 15: the POP row's record and reference, computable

The POP row's record (the row input written by PA.tables) and its reference expression are given by
COMPUTABLE definitions (the computability anchor), equal to the machine-side ones:

* `blockC`, `polyC`: a visit factor's record block and print (`visitSpec_block`, `visitSpec_poly`);
* `costC` with `visitSpec_cost_le`: an explicit bound on a factor stage's cost, from `printGCost_le` and C5's step
  cost (the scrub capacity `R` of the row is built from it);
* `popRefC`: the POP row's reference expression (`popExprOf_eq`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.WireExponent3_5.ListMachine.Print (recInnerLCost labOf PointEval printGCost recSpecL)
open NearCubicWires.SupplierWalk
open NearCubicWires.WireExponent3_5.FinalPass

/-! ## One visit factor, computable -/

/-- The register capacity of C5's evaluator for a visited list. -/
def capC (D : ListData) (L : ℕ) : ℕ := ListEval.capOf D.M D.J D.W (ListEval.rowsOf D L) L

/-- The record printer's log capacity. -/
def cap1C (L : ℕ) (labs : List ℕ) : ℕ := max (2 * (4 * L) + 1) (labCost (4 * L) labs)

/-- The evaluator's data tapes of a visit factor: C5's, then the negation flag. -/
def dataC (D : ListData) (L s : ℕ) (sgn neg : Bool) : Fin (19 + 1) → List Bool :=
  Fin.addCases (m := 19) (n := 1) (Pop.stage35Data D.M D.J D.W (ListEval.rowsOf D L) s sgn (capC D L)) fun _ => [neg]

/-- **A visit factor's record block.** -/
def blockC (D : ListData) (L s : ℕ) (sgn neg : Bool) (labs : List ℕ) : List Bool :=
  factorBlock (4 * L) (3 * listBound D) labs (cap1C L labs) 0 (dataC D L s sgn neg)

/-- The evaluated function of a visit factor. -/
def fC (D : ListData) (L s : ℕ) (sgn neg : Bool) (X : List Bool) : Bool :=
  xor (decide (ListEval.reportRef D.M D.J D.W (ListEval.rowsOf D L) (Pop.popBits sgn X) = s)) neg

/-- **A visit factor's print.** -/
def polyC (D : ListData) (L s : ℕ) (sgn neg : Bool) (labs : List ℕ) : Poly :=
  factorPoly (fC D L s sgn neg) (4 * L) (3 * listBound D) labs

/-- **An explicit bound on a visit factor's stage cost.** -/
def costC (D : ListData) (L s : ℕ) (sgn neg : Bool) (labs : List ℕ) : ℕ :=
  2 * loadCost (factorFields (4 * L) (3 * listBound D) labs (cap1C L labs) 0 (dataC D L s sgn neg)) + 2 + 1 +
    ((4 * L + 1) ^ (3 * listBound D) * 2 ^ (3 * listBound D) *
      (Pop.stage35Cost D.M D.J D.W (ListEval.rowsOf D L) L + 1 + 1 + 2 * labCost (4 * L) labs + 100 * (4 * L + 1) ^ 2) + 3)

section
variable (D : ListData) (L s : ℕ) (sgn : Bool) (hs : s ≤ D.M) (neg : Bool) (labs : List ℕ) (hlabs : 4 * L ≤ labs.length)

theorem visitSpec_block : (visitSpec D L s sgn (capC D L) hs le_rfl neg labs hlabs).block = blockC D L s sgn neg labs := by
  simp only [FSpec.block, visitSpec, blockC, negMember, member35, cap1C, capC]
  rfl

theorem visitSpec_poly : (visitSpec D L s sgn (capC D L) hs le_rfl neg labs hlabs).poly = polyC D L s sgn neg labs := by
  simp only [FSpec.poly, visitSpec, polyC]
  rfl

theorem visitSpec_cost_le : (visitSpec D L s sgn (capC D L) hs le_rfl neg labs hlabs).cost ≤ costC D L s sgn neg labs := by
  show 2 * loadCost _ + 2 + 1 + printGCost (recSpecL labs) (negMember F35 (member35 D L s sgn _ hs le_rfl) neg).pe
    (3 * listBound D) ≤ _
  have h := printGCost_le labs (negMember F35 (member35 D L s sgn (capC D L) hs le_rfl) neg).pe (3 * listBound D)
    (by unfold listBound; omega)
  unfold costC
  exact Nat.add_le_add_left h _

end

end NearCubicWires.WireExponent3_5.ListMachine.Row
