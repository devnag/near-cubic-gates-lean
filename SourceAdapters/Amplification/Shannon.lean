import Proof.Gates.Outer.CircuitEval

/-!
# A03: Shannon expansion in the node-count model — every `n`-input function has a circuit of `6·2^n − 5` nodes

 ("Full-range amplification interface"): "Every `n`-input function has a circuit with fewer than
`U(n) = 2^{n+3}` nodes. Indeed Shannon expansion combines two `(n−1)`-input circuits as
`(x ∧ f_1) ∨ (¬x ∧ f_0)`, adding at most five nodes. Thus `B(0) = 1` and `B(n) ≤ 2B(n−1) + 5` give
`B(n) ≤ 6·2^n − 5 < U(n)`."

The recurrence gives a bound proportional to `2^n`, with every DAG node counted.

Construction (`shanAt N b n F`): the node list for `F` expanded on the variables `n−1, …, 0`, placed at absolute
position `b` of an `N`-input circuit: `n = 0` is one constant node; `n + 1` is the list for `x_n := 1`, the list for
`x_n := 0`, then the five nodes `x_n`, `¬x_n`, `x_n ∧ f_1`, `¬x_n ∧ f_0`, `∨`. Children are absolute addresses
below their node (`shanAt_wellFormed`); the length is `6·2^n − 5` (`shanAt_length`); the last node computes `F` on
the input with the variables `≥ n` cleared (`shanAt_eval`). `hasCircuitOfSize_shannon` packages it for
`HasCircuitOfSize`, and `shannon_lt_U`: `6·2^n − 5 < 2^(n+3)`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma39
open NearCubicGates.Close.Outer (pushEval foldl_pushEval_size foldl_pushEval_prefix)

variable {N : ℕ}

/-- The input with the variables `≥ n` cleared. -/
def maskIn (n : ℕ) (x : BitInput N) : BitInput N := fun i => if i.val < n then x i else false

/-- The number of nodes `B(n) = 6·2^n − 5`, by its recursion. -/
def shanLen : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * shanLen n + 5

theorem shanLen_eq (n : ℕ) : shanLen n + 5 = 6 * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shanLen, pow_succ]; omega

theorem shanLen_pos (n : ℕ) : 1 ≤ shanLen n := by cases n <;> simp [shanLen]

/-- The Shannon node list for `F` on the variables `< n`, at absolute position `b`. -/
def shanAt (N : ℕ) (b : ℕ) : (n : ℕ) → n ≤ N → (BitInput N → Bool) → List (BooleanNode N)
  | 0, _, F => [.const (F fun _ => false)]
  | n + 1, hn, F =>
      let v : Fin N := ⟨n, by omega⟩
      let base := b + 2 * shanLen n
      shanAt N b n (by omega) (fun x => F (Function.update x v true)) ++
        shanAt N (b + shanLen n) n (by omega) (fun x => F (Function.update x v false)) ++
        [.input v, .not base, .and base (b + shanLen n - 1), .and (base + 1) (base - 1), .or (base + 2) (base + 3)]

theorem shanAt_length (b : ℕ) : ∀ (n : ℕ) (hn : n ≤ N) (F : BitInput N → Bool), (shanAt N b n hn F).length = shanLen n
  | 0, _, _ => rfl
  | n + 1, hn, F => by
      simp only [shanAt, List.length_append, List.length_cons, List.length_nil, shanAt_length, shanLen]
      omega

/-- Every node of `L`, placed from absolute position `b` on, has its children before it. -/
def AllWF (b : ℕ) (L : List (BooleanNode N)) : Prop := ∀ (j : ℕ) (hj : j < L.length), (L[j]).WellFormedAt (b + j)

theorem AllWF.append {b : ℕ} {L1 L2 : List (BooleanNode N)} (h1 : AllWF b L1) (h2 : AllWF (b + L1.length) L2) :
    AllWF b (L1 ++ L2) := by
  intro j hj
  by_cases h : j < L1.length
  · rw [List.getElem_append_left h]; exact h1 j h
  · rw [List.getElem_append_right (by omega)]
    have hj2 : j - L1.length < L2.length := by simp at hj; omega
    have := h2 (j - L1.length) hj2
    rwa [show b + L1.length + (j - L1.length) = b + j by omega] at this

/-- Every child precedes its node, at absolute positions. -/
theorem shanAt_wellFormed : ∀ (b n : ℕ) (hn : n ≤ N) (F : BitInput N → Bool), AllWF b (shanAt N b n hn F)
  | b, 0, _, F => by
      intro j hj
      simp only [shanAt, List.length_cons, List.length_nil] at hj
      have : j = 0 := by omega
      subst this; simp [shanAt, BooleanNode.WellFormedAt]
  | b, n + 1, hn, F => by
      have hp := shanLen_pos n
      simp only [shanAt]
      refine AllWF.append (AllWF.append (shanAt_wellFormed b n (by omega) _) ?_) ?_
      · rw [shanAt_length]; exact shanAt_wellFormed (b + shanLen n) n (by omega) _
      · rw [List.length_append, shanAt_length, shanAt_length]
        intro j hj
        simp only [List.length_cons, List.length_nil] at hj
        interval_cases j <;> simp [BooleanNode.WellFormedAt] <;> omega

theorem getD_push_lt (P : Array Bool) (v : Bool) (i : ℕ) (hi : i < P.size) :
    (P.push v)[i]?.getD false = P[i]?.getD false := by
  rw [Array.getElem?_push, if_neg (by omega)]

theorem getD_push_eq (P : Array Bool) (v : Bool) : (P.push v)[P.size]?.getD false = v := by
  simp

theorem update_mask_true (n : ℕ) (hn : n + 1 ≤ N) (x : BitInput N) (hx : x ⟨n, by omega⟩ = true) :
    Function.update (maskIn n x) ⟨n, by omega⟩ true = maskIn (n + 1) x := by
  funext i
  by_cases hi : i = ⟨n, by omega⟩
  · subst hi; simp [maskIn, hx]
  · rw [Function.update_of_ne hi]
    have : i.val ≠ n := fun h => hi (Fin.ext h)
    simp only [maskIn]
    by_cases h : i.val < n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

theorem update_mask_false (n : ℕ) (hn : n + 1 ≤ N) (x : BitInput N) (hx : x ⟨n, by omega⟩ = false) :
    Function.update (maskIn n x) ⟨n, by omega⟩ false = maskIn (n + 1) x := by
  funext i
  by_cases hi : i = ⟨n, by omega⟩
  · subst hi; simp [maskIn, hx]
  · rw [Function.update_of_ne hi]
    have : i.val ≠ n := fun h => hi (Fin.ext h)
    simp only [maskIn]
    by_cases h : i.val < n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]

/-- The five combining nodes after a prefix `Q`: the last one is `(x_v ∧ Q[i1]) ∨ (¬x_v ∧ Q[i0])`. -/
theorem tail_eval (x : BitInput N) (Q : Array Bool) (v : Fin N) (i1 i0 : ℕ) (h1 : i1 < Q.size) (h0 : i0 < Q.size) :
    (([.input v, .not Q.size, .and Q.size i1, .and (Q.size + 1) i0, .or (Q.size + 2) (Q.size + 3)] :
        List (BooleanNode N)).foldl (pushEval x) Q)[Q.size + 4]?.getD false =
      ((x v && Q[i1]?.getD false) || (!x v && Q[i0]?.getD false)) := by
  simp only [List.foldl_cons, List.foldl_nil, pushEval, BooleanNode.eval]
  simp only [Array.getElem?_push, Array.size_push]
  simp only [show Q.size + 4 = Q.size + 1 + 1 + 1 + 1 by omega, if_true,
    show Q.size + 2 = Q.size + 1 + 1 by omega, show Q.size + 3 = Q.size + 1 + 1 + 1 by omega,
    show ¬ (Q.size + 1 + 1 = Q.size + 1 + 1 + 1) by omega,
    show ¬ (Q.size + 1 = Q.size + 1 + 1) by omega, show ¬ (Q.size = Q.size + 1) by omega,
    show ¬ (i1 = Q.size) by omega, show ¬ (i0 = Q.size) by omega, show ¬ (i0 = Q.size + 1) by omega,
    if_false, Option.getD_some]
  simp [show i1 ≠ Q.size + 1 by omega, show i0 ≠ Q.size + 1 + 1 by omega]

/-- **Evaluation**: run after a prefix of `b` values, the last node of `shanAt` computes `F` on the masked input. -/
theorem shanAt_eval (x : BitInput N) : ∀ (n : ℕ) (hn : n ≤ N) (F : BitInput N → Bool) (P : Array Bool),
    ((shanAt N P.size n hn F).foldl (pushEval x) P)[P.size + shanLen n - 1]?.getD false = F (maskIn n x)
  | 0, _, F, P => by
      simp only [shanAt, List.foldl_cons, List.foldl_nil, shanLen, Nat.add_sub_cancel]
      rw [pushEval, getD_push_eq]
      simp only [BooleanNode.eval]
      congr 1
  | n + 1, hn, F, P => by
      have hp := shanLen_pos n
      simp only [shanAt]
      rw [List.foldl_append, List.foldl_append]
      have hs1 := foldl_pushEval_size x (shanAt N P.size n (by omega) (fun y => F (Function.update y ⟨n, by omega⟩ true))) P
      rw [shanAt_length] at hs1
      have e1 := shanAt_eval x n (by omega) (fun y => F (Function.update y ⟨n, by omega⟩ true)) P
      set P1 := (shanAt N P.size n (by omega) (fun y => F (Function.update y ⟨n, by omega⟩ true))).foldl (pushEval x) P
        with hP1
      rw [show P.size + shanLen n = P1.size from hs1.symm]
      have hs2 := foldl_pushEval_size x (shanAt N P1.size n (by omega) (fun y => F (Function.update y ⟨n, by omega⟩ false))) P1
      rw [shanAt_length] at hs2
      have e0 := shanAt_eval x n (by omega) (fun y => F (Function.update y ⟨n, by omega⟩ false)) P1
      set P2 := (shanAt N P1.size n (by omega) (fun y => F (Function.update y ⟨n, by omega⟩ false))).foldl (pushEval x) P1
        with hP2
      have e1' : P2[P1.size - 1]?.getD false = F (Function.update (maskIn n x) ⟨n, by omega⟩ true) := by
        rw [hP2, foldl_pushEval_prefix x _ P1 _ (by omega), show P1.size - 1 = P.size + shanLen n - 1 by omega]
        exact e1
      have e0' : P2[P2.size - 1]?.getD false = F (Function.update (maskIn n x) ⟨n, by omega⟩ false) := by
        rw [show P2.size - 1 = P1.size + shanLen n - 1 by omega]; exact e0
      have hb2 : P.size + 2 * shanLen n = P2.size := by omega
      rw [hb2, show P.size + shanLen (n + 1) - 1 = P2.size + 4 by simp only [shanLen]; omega]
      rw [tail_eval x P2 ⟨n, by omega⟩ _ _ (by omega) (by omega), e1', e0']
      cases hx : x ⟨n, by omega⟩
      · simp [update_mask_false n hn x hx]
      · simp [update_mask_true n hn x hx]

/-- The Shannon circuit of an `n`-input function. -/
def shannonCircuit {n : ℕ} (f : BoolFunction n) : BooleanCircuit n where
  nodes := shanAt n 0 n le_rfl f
  output := ⟨shanLen n - 1, by rw [shanAt_length]; have := shanLen_pos n; omega⟩
  wellFormed := fun idx => by
    have := shanAt_wellFormed 0 n le_rfl f idx.val idx.isLt
    rw [Nat.zero_add] at this
    rw [List.get_eq_getElem]; exact this

theorem maskIn_self {n : ℕ} (x : BitInput n) : maskIn n x = x := by
  funext i; simp [maskIn, i.isLt]

theorem shannonCircuit_size {n : ℕ} (f : BoolFunction n) : (shannonCircuit f).size = 6 * 2 ^ n - 5 := by
  have := shanLen_eq n
  simp only [shannonCircuit, BooleanCircuit.size, shanAt_length]
  omega

theorem shannonCircuit_eval {n : ℕ} (f : BoolFunction n) (x : BitInput n) : (shannonCircuit f).eval x = f x := by
  have h := shanAt_eval x n le_rfl f #[]
  simp only [Array.size_empty, Nat.zero_add] at h
  rw [maskIn_self] at h
  exact h

/-- **A03, Shannon**: every `n`-input function has a circuit of at most `6·2^n − 5` nodes. -/
theorem hasCircuitOfSize_shannon {n : ℕ} (f : BoolFunction n) : HasCircuitOfSize f (6 * 2 ^ n - 5) :=
  ⟨shannonCircuit f, (shannonCircuit_size f).le, shannonCircuit_eval f⟩

/-- `6·2^n − 5 < U(n) = 2^(n+3)`. -/
theorem shannon_lt_U (n : ℕ) : 6 * 2 ^ n - 5 < 2 ^ (n + 3) := by
  have : 2 ^ (n + 3) = 8 * 2 ^ n := by rw [pow_add]; ring
  have := Nat.one_le_two_pow (n := n)
  omega

/-- **The `S(n) ≥ U(n)` regime** (`app:sources`, "Full-range amplification interface"): no function satisfies the worst-case hardness premise. -/
theorem hasCircuitOfSize_of_U_le {n : ℕ} (f : BoolFunction n) (s : ℕ) (hs : 2 ^ (n + 3) ≤ s) :
    HasCircuitOfSize f s := by
  obtain ⟨C, hC, hev⟩ := hasCircuitOfSize_shannon f
  exact ⟨C, by have := shannon_lt_U n; omega, hev⟩

end NearCubicGates.Adapters.Amplification
