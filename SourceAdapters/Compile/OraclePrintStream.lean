import SourceAdapters.Compile.OraclePrintTemplate

/-!
# Vectors of expressions on the token machine

proof of `thm:short-pcp-ours`: the circuit is the input gates, the initial formulas, `fuel` rounds (the query addresses, one oracle
gate, the transition formulas) and the verdict, all compiled on shared wires (`requestStream`). The printer
compiles each vector of formulas member by member, moving each member's output wire off the stack into the next
wire map. `PS.vec` is that step on the token machine; `vec_stream`: with the members' postfix tokens it emits exactly
`vectorStream` and collects exactly its output wires. `inputsStream_eq` describes the input gates.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.FinitePredicateCircuit
open NearCubicGates.Adapters.Compile.OracleExpressions (wireStream vectorStream inputsStream)

set_option autoImplicit false

variable {n arity : ℕ}

/-- Drop the top of the stack. -/
def PS.drop1 (S : PS n arity) : PS n arity := ⟨S.cnt, S.stk.tail, S.nodes⟩

/-- A vector of members: run each member's tokens and move its output wire to the output list. -/
def PS.vec (w : List ℕ) (tf : ℕ → List Tok) : ℕ → PS n arity → PS n arity × List ℕ
  | 0, S => (S, [])
  | k + 1, S =>
      let S1 := S.run w (tf 0)
      let q := PS.vec w (fun i => tf (i + 1)) k S1.drop1
      (q.1, S1.stk.headD 0 :: q.2)

theorem PS.vec_cons (w : List ℕ) (tf : ℕ → List Tok) (k : ℕ) (S : PS n arity) :
    PS.vec w tf (k + 1) S = ((PS.vec w (fun i => tf (i + 1)) k (S.run w (tf 0)).drop1).1,
      (S.run w (tf 0)).stk.headD 0 :: (PS.vec w (fun i => tf (i + 1)) k (S.run w (tf 0)).drop1).2) := rfl

/-- The vector, member by member from the front (the loop invariant of the cell program). -/
theorem PS.vec_succ (w : List ℕ) (k : ℕ) : ∀ (tf : ℕ → List Tok) (S : PS n arity),
    PS.vec w tf (k + 1) S = (((PS.vec w tf k S).1.run w (tf k)).drop1,
      (PS.vec w tf k S).2 ++ [((PS.vec w tf k S).1.run w (tf k)).stk.headD 0]) := by
  induction k with
  | zero => intro tf S; rfl
  | succ k ih =>
      intro tf S
      rw [PS.vec_cons (k := k + 1), ih (fun i => tf (i + 1)) (S.run w (tf 0)).drop1, PS.vec_cons (k := k)]
      simp

/-- **A vector of expressions emits exactly `vectorStream`** and collects its output wires. -/
theorem vec_stream {width : ℕ} (w : List ℕ) (ρ : Fin width → ℕ) (count : ℕ) :
    ∀ (exprs : Fin count → BoolExpr width) (tf : ℕ → List Tok) (S : PS n arity),
      (∀ j : Fin count, tf j.val = postR ρ (exprs j)) →
      (PS.vec w tf count S).1 =
          ⟨S.cnt + (vectorStream (n := n) (arity := arity) S.cnt (fun i => w.getD (ρ i) 0) count exprs).1.length,
            S.stk, S.nodes ++ (vectorStream (n := n) (arity := arity) S.cnt (fun i => w.getD (ρ i) 0) count exprs).1⟩ ∧
        (PS.vec w tf count S).2 =
          List.ofFn (vectorStream (n := n) (arity := arity) S.cnt (fun i => w.getD (ρ i) 0) count exprs).2 := by
  induction count with
  | zero => intro exprs tf S _; refine ⟨?_, ?_⟩ <;> simp [PS.vec, vectorStream]
  | succ k ih =>
      intro exprs tf S h
      have h0 : tf 0 = postR ρ (exprs 0) := h 0
      obtain ⟨i1, i2⟩ := ih (fun i => exprs i.succ) (fun i => tf (i + 1))
        (S.run w (tf 0)).drop1 (fun j => h j.succ)
      simp only [PS.vec]
      rw [i1, i2]
      rw [h0, run_postR]
      simp only [PS.drop1, vectorStream, List.length_append, List.append_assoc, List.headD_cons, List.tail_cons,
        List.ofFn_succ, Fin.cases_zero, Fin.cases_succ]
      simp [Nat.add_assoc]

/-- The input gates: `.input i` for every seed bit, at indices `base, base + 1, …`. -/
theorem inputsStream_eq (count : ℕ) : ∀ (base : ℕ) (indices : Fin count → Fin n),
    (inputsStream (arity := arity) base count indices).1 = List.ofFn (fun i => .input (indices i)) ∧
      ∀ i : Fin count, (inputsStream (arity := arity) base count indices).2 i = base + i.val := by
  induction count with
  | zero => intro base indices; exact ⟨rfl, fun i => i.elim0⟩
  | succ k ih =>
      intro base indices
      obtain ⟨i1, i2⟩ := ih (base + 1) (fun i => indices i.succ)
      refine ⟨by simp only [inputsStream, List.ofFn_succ, i1], fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [inputsStream]
      · simp only [inputsStream, Fin.cases_succ, i2 j, Fin.val_succ]; omega

end NearCubicGates.Adapters.Compile.OraclePrint
