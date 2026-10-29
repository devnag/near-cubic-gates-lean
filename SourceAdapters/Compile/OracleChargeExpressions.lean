import SourceAdapters.Compile.OracleQueryAddress

/-!
proof of `thm:short-pcp-ours`, Step 4: gate-level charging of every framed query. A decoded m-bit
query costs 2m+2, including its terminator and the oracle transition. The
remaining unary one-hot budget shifts by exactly that amount; an insufficient
budget produces all-zero clock wires. Prefix flags are shared live wires.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def chargeBits (width cap : ℕ) := width+(cap+1)

def chargeEncoding (width cap : ℕ) (word : List Bool) (remaining : Fin (cap+1)) :
    BitInput (chargeBits width cap) :=
  Fin.addCases (fun count : Fin width => framePrefix count.val word)
    (fun budget : Fin (cap+1) => decide (remaining=budget))

def queryRemainingExpression (width cap : ℕ) (target : Fin (cap+1)) :
    BoolExpr (chargeBits width cap) :=
  anyExpression (List.ofFn fun count : Fin width =>
    .and (.input (count.castAdd (cap+1)))
      (if h : target.val+2*count.val+2<cap+1 then
        .input ((⟨target.val+2*count.val+2,h⟩ : Fin (cap+1)).natAdd width)
       else .const false))

theorem queryRemainingExpression_true (width cap : ℕ) (target remaining : Fin (cap+1))
    (word : List Bool) :
    (queryRemainingExpression width cap target).eval (chargeEncoding width cap word remaining)=true ↔
      ∃ count : Fin width, framePrefix count.val word=true ∧
        remaining.val=target.val+2*count.val+2 := by
  simp only [queryRemainingExpression,anyExpression_true,List.mem_ofFn,exists_exists_eq_and]
  apply exists_congr
  intro count
  simp only [BoolExpr.eval,chargeEncoding,Fin.addCases_left,Bool.and_eq_true]
  by_cases h : target.val+2*count.val+2<cap+1
  · simp only [h,↓reduceDIte,BoolExpr.eval,chargeEncoding,Fin.addCases_right,decide_eq_true_eq,Fin.ext_iff]
  · simp only [h,↓reduceDIte,BoolExpr.eval,Bool.false_eq_true,and_false]
    constructor
    · intro hf; exact hf.elim
    · rintro ⟨_,he⟩
      have hr := remaining.isLt
      omega

theorem queryRemainingExpression_eval (width cap : ℕ) (target remaining : Fin (cap+1))
    (bits padding : List Bool) (hw : (RepairOrdinary.frame bits++padding).length ≤ width) :
    (queryRemainingExpression width cap target).eval
      (chargeEncoding width cap (RepairOrdinary.frame bits++padding) remaining)=
      decide (2*bits.length+2 ≤ remaining.val ∧ remaining.val-(2*bits.length+2)=target.val) := by
  apply Bool.eq_iff_iff.mpr
  rw [queryRemainingExpression_true]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨count,hc,hr⟩
    have he := framePrefix_unique hc (framePrefix_append bits padding)
    omega
  · rintro ⟨hc,hr⟩
    exact ⟨⟨bits.length,framePrefix_count_bound (framePrefix_append bits padding) hw⟩,
      framePrefix_append bits padding,by change remaining.val=target.val+2*bits.length+2; omega⟩

theorem queryRemainingExpression_operations (width cap : ℕ) (target : Fin (cap+1)) :
    expressionOperations (queryRemainingExpression width cap target) ≤ 3*width+1 := by
  have h := anyExpression_operations (n := chargeBits width cap)
    (List.ofFn fun count : Fin width =>
      BoolExpr.and (.input (count.castAdd (cap+1)))
        (if h : target.val+2*count.val+2<cap+1 then
          .input ((⟨target.val+2*count.val+2,h⟩ : Fin (cap+1)).natAdd width)
         else .const false)) 2 (by
      intro e he
      obtain ⟨count,rfl⟩ := List.mem_ofFn.mp he
      simp only [expressionOperations]
      split <;> simp [expressionOperations])
  change expressionOperations (queryRemainingExpression width cap target) ≤ _ at h
  simpa only [List.length_ofFn,show 2+1=3 by rfl,Nat.mul_comm] using h

def queryAffordableExpression (width cap : ℕ) : BoolExpr (chargeBits width cap) :=
  anyExpression (List.ofFn fun target : Fin (cap+1) => queryRemainingExpression width cap target)

theorem queryAffordableExpression_eval (width cap : ℕ) (remaining : Fin (cap+1))
    (bits padding : List Bool) (hw : (RepairOrdinary.frame bits++padding).length ≤ width) :
    (queryAffordableExpression width cap).eval
      (chargeEncoding width cap (RepairOrdinary.frame bits++padding) remaining)=
      decide (2*bits.length+2 ≤ remaining.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [queryAffordableExpression,anyExpression_true,List.mem_ofFn,exists_exists_eq_and,
    queryRemainingExpression_eval _ _ _ _ _ _ hw,decide_eq_true_eq]
  constructor
  · rintro ⟨target,hc,_⟩; exact hc
  · intro hc
    exact ⟨⟨remaining.val-(2*bits.length+2),by have := remaining.isLt; omega⟩,hc,rfl⟩

end NearCubicGates.Adapters.Compile.OracleExecution
