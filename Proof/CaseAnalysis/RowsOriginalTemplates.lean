import Proof.Hierarchy.CompetitorSourceTests
import Proof.CaseAnalysis.RowsScalarFits

/-! Exact signed templates for the three original source tests. The parity
field denotes a carried systematic atom, never an original family index.
The factor list retains its order and every repeated family occurrence. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTemplates
open ComponentwiseValidity CloseoutRowsScalarFits
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Row where
  rho : ℚ
  parity : Option (Fin 2)
  factors : List (Fin 2)

def plain (rho : ℚ) (factors : List (Fin 2)) : Row := ⟨rho,none,factors⟩
def carried (rho : ℚ) (side : Fin 2) (factors : List (Fin 2)) : Row := ⟨rho,some side,factors⟩
def Row.value (r : Row) (x e : Fin 2 → ℝ) : ℝ :=
  (r.rho : ℝ)*(match r.parity with | none=>1 | some side=>e side)*(r.factors.map x).prod
def value (rows : List Row) (x e : Fin 2 → ℝ) := (rows.map (fun r=>r.value x e)).sum

def auxiliary (side : Fin 2) : List Row :=
  [plain 1 [side,side],plain (-2) [side,side,side],plain 1 [side,side,side,side]]
def systematic (side : Fin 2) : List Row :=
  [carried 1 side [],carried (-2) side [side],plain 1 [side,side]]
def moment : List Row := [plain 1 [0,0]]
def clause : Bool → Bool → List Row
  | false,false => [plain 1 [0],plain 1 [1],plain (-1) [0,1]]
  | false,true => [plain 1 [],plain (-1) [1],plain 1 [0,1]]
  | true,false => [plain 1 [],plain (-1) [0],plain 1 [0,1]]
  | true,true => [plain 1 [],plain (-1) [0,1]]

theorem auxiliary_value (side : Fin 2) (x e : Fin 2 → ℝ) :
    value (auxiliary side) x e=booleanityPenalty (x side) := by
  simp [value,auxiliary,plain,Row.value,booleanityPenalty]
  ring

theorem systematic_value (side : Fin 2) (x e : Fin 2 → ℝ) (expected : Bool)
    (he : e side=bitAsReal expected) :
    value (systematic side) x e=systematicPenalty expected (x side) := by
  cases expected <;> simp [value,systematic,plain,carried,Row.value,systematicPenalty,he,bitAsReal] <;> ring

theorem moment_value (x e : Fin 2 → ℝ) : value moment x e=(x 0)^2 := by
  simp [value,moment,plain,Row.value,pow_two]

theorem clause_value (leftNegative rightNegative : Bool) (x e : Fin 2 → ℝ) :
    value (clause leftNegative rightNegative) x e=clauseValue leftNegative rightNegative (x 0) (x 1) := by
  cases leftNegative <;> cases rightNegative <;>
    simp [value,clause,plain,Row.value,clauseValue,literalValue] <;> ring

def Legal (r : Row) : Prop := r.factors.length ≤ 4 ∧ RationalBound 2 r.rho

theorem auxiliary_legal (side : Fin 2) : ∀ r∈auxiliary side,Legal r := by
  simp [auxiliary,Legal,plain,RationalBound]

theorem systematic_legal (side : Fin 2) : ∀ r∈systematic side,Legal r := by
  simp [systematic,Legal,plain,carried,RationalBound]

theorem moment_legal : ∀ r∈moment,Legal r := by
  simp [moment,Legal,plain,RationalBound]

theorem clause_legal (leftNegative rightNegative : Bool) :
    ∀ r∈clause leftNegative rightNegative,Legal r := by
  cases leftNegative <;> cases rightNegative <;> simp [clause,Legal,plain,RationalBound]

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTemplates
