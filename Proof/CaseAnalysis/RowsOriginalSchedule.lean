import Proof.CaseAnalysis.RowsOriginalSourceTask

/-! Three grouped phases retain the original indexed clause distribution.
The six and three template slots are sums, never new averaging indices. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open CloseoutRowsOriginalTemplates CloseoutRowsOriginalTask ComponentwiseValidity
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

inductive Phase where
  | penalty | moment | clause

def tasks : Phase→List Task
  | .penalty=>List.ofFn (Task.penalty 0)++List.ofFn (Task.penalty 1)
  | .moment=>[Task.moment]
  | .clause=>List.ofFn Task.clause
def divisor : Phase→ℕ
  | .penalty=>2
  | .moment=>1
  | .clause=>1
def denominator (phase : Phase) (clauseBits : ℕ):=divisor phase*2^clauseBits
def value (phase : Phase) (bits : Fin 4→Bool) (x e : Fin 2→ℝ) : ℝ:=
  ((tasks phase).map (fun t=>(row t bits).value x e)).sum

theorem lengths : (tasks .penalty).length=6 ∧ (tasks .moment).length=1 ∧ (tasks .clause).length=3 := by
  simp [tasks]

theorem side_value (aux : Bool) (side : Fin 2) (x e : Fin 2→ℝ) (constraint : Option Bool)
    (ha : aux=constraint.isNone) (he : ∀ b,constraint=some b→e side=bitAsReal b) :
    CloseoutRowsOriginalTemplates.value (List.ofFn (penaltySlot aux side)) x e=
      validityPenalty constraint (x side) := by
  rw [penalty_slots,ha]
  cases constraint with
  | none=>exact auxiliary_value side x e
  | some b=>exact systematic_value side x e b (he b rfl)

theorem penalty_value (bits : Fin 4→Bool) (x e : Fin 2→ℝ) (constraint : Fin 2→Option Bool)
    (ha : ∀ side,bits (Fin.natAdd 2 side)=(constraint side).isNone)
    (he : ∀ side b,constraint side=some b→e side=bitAsReal b) :
    value .penalty bits x e=validityPenalty (constraint 0) (x 0)+validityPenalty (constraint 1) (x 1) := by
  have left:=side_value (bits (Fin.natAdd 2 (0 : Fin 2))) 0 x e (constraint 0) (ha 0) (he 0)
  have right:=side_value (bits (Fin.natAdd 2 (1 : Fin 2))) 1 x e (constraint 1) (ha 1) (he 1)
  simpa only [value,tasks,List.map_append,List.sum_append,List.map_ofFn,Function.comp_def,
    row,CloseoutRowsOriginalTemplates.value,List.map_ofFn] using congrArg₂ (·+·) left right

theorem moment_value (bits : Fin 4→Bool) (x e : Fin 2→ℝ) : value .moment bits x e=(x 0)^2 := by
  simp [value,tasks,row,plain,Row.value,pow_two]

theorem clause_value (bits : Fin 4→Bool) (x e : Fin 2→ℝ) :
    value .clause bits x e=clauseValue (bits 0) (bits 1) (x 0) (x 1) := by
  simpa only [value,tasks,List.map_ofFn,Function.comp_def,row,CloseoutRowsOriginalTemplates.value]
    using clause_slots_value (bits 0) (bits 1) x e

theorem normalization (phase : Phase) (clauseBits : ℕ) (terms : Fin (2^clauseBits)→ℝ) :
    (∑ i,terms i)/(denominator phase clauseBits : ℝ)=
      (𝔼 i,terms i)/(divisor phase : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fin,denominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,div_div]
  rw [mul_comm]

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
