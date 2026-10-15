import Proof.CaseAnalysis.RowsOriginalTemplates

/-! Every clause case uses three fixed slots. The short case has one
literal zero row, preserving its exact polynomial and bounded coefficients. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTemplates
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot (rows : List Row) (j : Fin 3) := rows[j.val]?.getD (plain 0 [])
def penaltySlot (aux : Bool) (side : Fin 2) (j : Fin 3):=
  slot (if aux then auxiliary side else systematic side) j
def clauseSlot (a b : Bool) (j : Fin 3):=slot (clause a b) j

theorem penalty_slot_legal (aux : Bool) (side : Fin 2) (j : Fin 3) : Legal (penaltySlot aux side j) := by
  cases aux <;>fin_cases j <;>simp [penaltySlot,slot,auxiliary,systematic,Legal,plain,carried,
    CloseoutRowsScalarFits.RationalBound]

theorem clause_slot_legal (a b : Bool) (j : Fin 3) : Legal (clauseSlot a b j) := by
  cases a <;>cases b <;>fin_cases j <;>simp [clauseSlot,slot,clause,Legal,plain,CloseoutRowsScalarFits.RationalBound]

theorem penalty_slots (aux : Bool) (side : Fin 2) : List.ofFn (penaltySlot aux side)=
    if aux then auxiliary side else systematic side := by
  cases aux <;>simp [penaltySlot,slot,auxiliary,systematic,List.ofFn_succ,Fin.succ]

theorem clause_slots_value (a b : Bool) (x e : Fin 2→ℝ) :
    value (List.ofFn (clauseSlot a b)) x e=ComponentwiseValidity.clauseValue a b (x 0) (x 1) := by
  rw [←clause_value a b x e]
  cases a <;>cases b <;>
    simp [value,clauseSlot,slot,clause,List.ofFn_succ,Fin.succ,plain,Row.value]

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTemplates
