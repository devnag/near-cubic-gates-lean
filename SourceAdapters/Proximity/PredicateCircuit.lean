import Proof.Foundations.BooleanDAGBuilder
import Proof.Foundations.TseitinCNF
import Mathlib.Tactic

/-!
Q02, `app:sources`, "Uniform three-query PCPP and code interfaces" and CW19 Appendix A, p. 19:38: a predicate on the fixed number
of queried bits has a circuit of size depending only on that query count.
The construction is an explicit disjunctive normal form, compiled through the
released append-only DAG API. The bounds are uniform in the truth table.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires

inductive QueryFormula (n : ℕ) where
  | constant : Bool → QueryFormula n
  | inputVar : Fin n → QueryFormula n
  | negation : QueryFormula n → QueryFormula n
  | conjunction : QueryFormula n → QueryFormula n → QueryFormula n
  | disjunction : QueryFormula n → QueryFormula n → QueryFormula n

namespace QueryFormula

def eval {n : ℕ} (input : BitInput n) : QueryFormula n → Bool
  | .constant b => b
  | .inputVar i => input i
  | .negation a => !(a.eval input)
  | .conjunction a b => a.eval input && b.eval input
  | .disjunction a b => a.eval input || b.eval input

def size {n : ℕ} : QueryFormula n → ℕ
  | .constant _ => 1
  | .inputVar _ => 1
  | .negation a => a.size + 1
  | .conjunction a b => a.size + b.size + 1
  | .disjunction a b => a.size + b.size + 1

structure Compiled {n : ℕ} (prior : BooleanDAGBuilder n) where
  final : BooleanDAGBuilder n
  extension : BooleanDAGExtension prior final
  output : Fin final.nodes.length

def compile {n : ℕ} : (F : QueryFormula n) → (prior : BooleanDAGBuilder n) → Compiled prior
  | .constant b, prior =>
      ⟨prior.appendNode (.const b) trivial,
        BooleanDAGExtension.single prior (.const b) trivial,
        prior.newest (.const b) trivial⟩
  | .inputVar i, prior =>
      ⟨prior.appendNode (.input i) trivial,
        BooleanDAGExtension.single prior (.input i) trivial,
        prior.newest (.input i) trivial⟩
  | .negation a, prior =>
      let left := a.compile prior
      ⟨left.final.appendNode (.not left.output.val) left.output.isLt,
        left.extension.trans (BooleanDAGExtension.single left.final
          (.not left.output.val) left.output.isLt),
        left.final.newest (.not left.output.val) left.output.isLt⟩
  | .conjunction a b, prior =>
      let left := a.compile prior
      let right := b.compile left.final
      let l := right.extension.lift left.output
      let wf := And.intro l.isLt right.output.isLt
      ⟨right.final.appendNode (.and l.val right.output.val) wf,
        (left.extension.trans right.extension).trans
          (BooleanDAGExtension.single right.final (.and l.val right.output.val) wf),
        right.final.newest (.and l.val right.output.val) wf⟩
  | .disjunction a b, prior =>
      let left := a.compile prior
      let right := b.compile left.final
      let l := right.extension.lift left.output
      let wf := And.intro l.isLt right.output.isLt
      ⟨right.final.appendNode (.or l.val right.output.val) wf,
        (left.extension.trans right.extension).trans
          (BooleanDAGExtension.single right.final (.or l.val right.output.val) wf),
        right.final.newest (.or l.val right.output.val) wf⟩

theorem compile_length {n : ℕ} (F : QueryFormula n) (prior : BooleanDAGBuilder n) :
    (F.compile prior).final.nodes.length = prior.nodes.length + F.size := by
  induction F generalizing prior with
  | constant b => simp [compile, size]
  | inputVar i => simp [compile, size]
  | negation a ih => simp [compile, size, ih, Nat.add_assoc]
  | conjunction a b iha ihb => simp [compile, size, iha, ihb, Nat.add_assoc]
  | disjunction a b iha ihb => simp [compile, size, iha, ihb, Nat.add_assoc]

theorem compile_eval {n : ℕ} (F : QueryFormula n) (prior : BooleanDAGBuilder n)
    (input : BitInput n) :
    ((F.compile prior).final.values input)[(F.compile prior).output.val]? =
      some (F.eval input) := by
  induction F generalizing prior with
  | constant b => exact prior.appendNode_newest (.const b) trivial input
  | inputVar i => exact prior.appendNode_newest (.input i) trivial input
  | negation a ih =>
      simp only [compile, BooleanDAGBuilder.appendNode_newest, BooleanNode.eval, eval, ih,
        Option.getD_some]
  | conjunction a b iha ihb =>
      simp only [compile, BooleanDAGBuilder.appendNode_newest, BooleanNode.eval, eval,
        BooleanDAGExtension.wireValue_lift, iha, ihb, Option.getD_some]
  | disjunction a b iha ihb =>
      simp only [compile, BooleanDAGBuilder.appendNode_newest, BooleanNode.eval, eval,
        BooleanDAGExtension.wireValue_lift, iha, ihb, Option.getD_some]

def circuit {n : ℕ} (F : QueryFormula n) : BooleanCircuit n :=
  let result := F.compile (BooleanDAGBuilder.empty n)
  result.final.finish result.output

theorem circuit_size {n : ℕ} (F : QueryFormula n) : F.circuit.size = F.size := by
  simp [circuit, compile_length, BooleanDAGBuilder.empty]

theorem circuit_eval {n : ℕ} (F : QueryFormula n) (input : BitInput n) :
    F.circuit.eval input = F.eval input := by
  change (getElem? ((F.compile (BooleanDAGBuilder.empty n)).final.values input)
    (F.compile (BooleanDAGBuilder.empty n)).output.val).getD false = F.eval input
  rw [compile_eval]
  rfl

def literal {n : ℕ} (assignment : BitInput n) (i : Fin n) : QueryFormula n :=
  if assignment i then .inputVar i else .negation (.inputVar i)

theorem literal_eval {n : ℕ} (assignment input : BitInput n) (i : Fin n) :
    (literal assignment i).eval input = decide (input i = assignment i) := by
  cases ha : assignment i <;> cases hx : input i <;> simp [literal, eval, ha, hx]

theorem literal_size {n : ℕ} (assignment : BitInput n) (i : Fin n) :
    (literal assignment i).size ≤ 2 := by
  cases ha : assignment i <;> simp [literal, size, ha]

def minterm {n : ℕ} (assignment : BitInput n) : List (Fin n) → QueryFormula n
  | [] => .constant true
  | i :: rest => .conjunction (literal assignment i) (minterm assignment rest)

theorem minterm_eval {n : ℕ} (assignment input : BitInput n) (indices : List (Fin n)) :
    (minterm assignment indices).eval input =
      indices.all (fun i => decide (input i = assignment i)) := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [minterm, eval, literal_eval, ih]

theorem minterm_size {n : ℕ} (assignment : BitInput n) (indices : List (Fin n)) :
    (minterm assignment indices).size ≤ 3 * indices.length + 1 := by
  induction indices with
  | nil => simp [minterm, size]
  | cons i rest ih =>
      have h := literal_size assignment i
      simp only [minterm, size, List.length_cons]
      omega

theorem full_minterm_eval {n : ℕ} (assignment input : BitInput n) :
    (minterm assignment (List.finRange n)).eval input = decide (input = assignment) := by
  rw [minterm_eval]
  apply Bool.eq_iff_iff.mpr
  simp [List.all_eq_true, funext_iff]

def disjuncts {n : ℕ} (predicate : BitInput n → Bool) : List (BitInput n) → QueryFormula n
  | [] => .constant false
  | assignment :: rest =>
      .disjunction (if predicate assignment then minterm assignment (List.finRange n)
        else .constant false) (disjuncts predicate rest)

theorem disjuncts_eval {n : ℕ} (predicate : BitInput n → Bool)
    (assignments : List (BitInput n)) (input : BitInput n) :
    (disjuncts predicate assignments).eval input =
      assignments.any (fun assignment => predicate assignment && decide (input = assignment)) := by
  induction assignments with
  | nil => rfl
  | cons assignment rest ih =>
      cases hp : predicate assignment <;>
        simp [disjuncts, eval, hp, full_minterm_eval, ih]

theorem disjuncts_size {n : ℕ} (predicate : BitInput n → Bool)
    (assignments : List (BitInput n)) :
    (disjuncts predicate assignments).size ≤ (3 * n + 2) * assignments.length + 1 := by
  induction assignments with
  | nil => simp [disjuncts, size]
  | cons assignment rest ih =>
      have h := minterm_size assignment (List.finRange n)
      simp only [List.length_finRange] at h
      cases hp : predicate assignment <;>
        simp only [disjuncts, hp, Bool.false_eq_true, ↓reduceIte, size, List.length_cons]
      all_goals nlinarith

def assignments (n : ℕ) : List (BitInput n) :=
  List.ofFn fun code : Fin (2 ^ n) => fun i : Fin n => code.val.testBit i.val

theorem mem_assignments {n : ℕ} (input : BitInput n) : input ∈ assignments n := by
  apply List.mem_ofFn.mpr
  refine ⟨⟨TseitinCNF.bitAssignmentCode input, TseitinCNF.bitAssignmentCode_lt_two_pow input⟩, ?_⟩
  funext i
  exact TseitinCNF.bitAssignmentCode_testBit input i

def truthTable {n : ℕ} (predicate : BitInput n → Bool) : QueryFormula n :=
  disjuncts predicate (assignments n)

theorem truthTable_eval {n : ℕ} (predicate : BitInput n → Bool) (input : BitInput n) :
    (truthTable predicate).eval input = predicate input := by
  rw [truthTable, disjuncts_eval]
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true, mem_assignments]

theorem truthTable_size {n : ℕ} (predicate : BitInput n → Bool) :
    (truthTable predicate).size ≤ (3 * n + 2) * 2 ^ n + 1 := by
  simpa [truthTable, assignments] using disjuncts_size predicate (assignments n)

end QueryFormula

/-- `app:sources`, "Uniform three-query PCPP and code interfaces" and Appendix A: explicit query-count-uniform decision circuit. -/
def predicateCircuit {q : ℕ} (predicate : BitInput q → Bool) : BooleanCircuit q :=
  (QueryFormula.truthTable predicate).circuit

theorem predicateCircuit_eval {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q) :
    (predicateCircuit predicate).eval input = predicate input := by
  simp [predicateCircuit, QueryFormula.circuit_eval, QueryFormula.truthTable_eval]

theorem predicateCircuit_size {q : ℕ} (predicate : BitInput q → Bool) :
    (predicateCircuit predicate).size ≤ (3 * q + 2) * 2 ^ q + 1 := by
  simpa [predicateCircuit, QueryFormula.circuit_size] using QueryFormula.truthTable_size predicate

end NearCubicGates.Adapters.Proximity
