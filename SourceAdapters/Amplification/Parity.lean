import NineInputs

/-!
# A03/A04: the small-size regime — parity, and the trivial sizes `0`

 `app:sources`, "Full-range amplification interface": "If `S(n) = 0`, use a constant function: the target size is
zero and no circuit has zero nodes. If `1 ≤ S(n) ≤ n^c`, use parity on `n + 1` bits. A circuit with at most
`S(n)^{1/c} ≤ n` nodes omits an input, so pairing assignments that differ only in that input gives agreement exactly
`1/2 < 1/2 + S(n)^{-1/c}`." and `app:sources`, "Full-range amplification interface": "At each of the finitely many lengths `n < n_0` with `S(n) > 0`, output
parity on `S(n) + 1` bits instead. Since `S(n)^{1/c} ≤ S(n)`, the same missing-input argument gives hardness."

The missing-input argument pairs assignments that differ at an unread input;
each pair has exactly one parity agreement.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma39


/-- Every `BooleanCircuit` has at least one node (its output is a `Fin nodes.length`). -/
theorem circuit_size_pos {n : ℕ} (C : BooleanCircuit n) : 1 ≤ C.size := by
  have := C.output.isLt
  unfold BooleanCircuit.size
  omega

/-- `S n = 0`: the clause `CannotBeApproximated g (0^{-1/c}) (0^{1/c})` is vacuous (`0^{1/c} = 0` in
`Real.rpow`, and no circuit has `0` nodes). -/
theorem cannotBeApproximated_at_size_zero {m : ℕ} (g : BoolFunction m) (c : ℝ) (hc : 1 ≤ c) :
    CannotBeApproximated g (((0 : ℕ) : ℝ) ^ (-(1 : ℝ) / c)) (((0 : ℕ) : ℝ) ^ ((1 : ℝ) / c)) := by
  intro C hC
  have h0 : ((0 : ℕ) : ℝ) ^ ((1 : ℝ) / c) = 0 := by
    rw [Nat.cast_zero]
    exact Real.zero_rpow (by have : (0 : ℝ) < 1 / c := by positivity
                             exact ne_of_gt this)
  rw [h0] at hC
  have h1 : (1 : ℝ) ≤ (C.size : ℝ) := by exact_mod_cast circuit_size_pos C
  linarith

/-! ### Parity: a circuit with fewer nodes than variables agrees with it on exactly half of the inputs -/

/-- The input index a node reads, if it is an input node. -/
def inputIndex {n : ℕ} : BooleanNode n → Option (Fin n)
  | .input j => some j
  | _ => none

theorem node_eval_eq {n : ℕ} (i : Fin n) (x y : BitInput n) (hxy : ∀ j, j ≠ i → x j = y j)
    (nd : BooleanNode n) (hnd : inputIndex nd ≠ some i) (prior : Array Bool) :
    nd.eval x prior = nd.eval y prior := by
  match nd, hnd with
  | .const _, _ => rfl
  | .input j, h =>
      simp only [BooleanNode.eval]
      exact hxy j (fun e => h (by rw [e]; rfl))
  | .not _, _ => rfl
  | .and _ _, _ => rfl
  | .or _ _, _ => rfl

theorem foldl_eq {n : ℕ} (i : Fin n) (x y : BitInput n) (hxy : ∀ j, j ≠ i → x j = y j) :
    ∀ (l : List (BooleanNode n)) (prior : Array Bool), (∀ nd ∈ l, inputIndex nd ≠ some i) →
      l.foldl (fun prior node => prior.push (node.eval x prior)) prior =
        l.foldl (fun prior node => prior.push (node.eval y prior)) prior
  | [], _, _ => rfl
  | nd :: l, prior, h => by
      simp only [List.foldl_cons]
      rw [node_eval_eq i x y hxy nd (h nd List.mem_cons_self) prior]
      exact foldl_eq i x y hxy l _ (fun nd' hm => h nd' (List.mem_cons_of_mem _ hm))

theorem eval_eq_of_missing {n : ℕ} (C : BooleanCircuit n) (i : Fin n)
    (hi : ∀ nd ∈ C.nodes, inputIndex nd ≠ some i) (x y : BitInput n) (hxy : ∀ j, j ≠ i → x j = y j) :
    C.eval x = C.eval y := by
  unfold BooleanCircuit.eval BooleanCircuit.values
  rw [foldl_eq i x y hxy C.nodes #[] hi]

/-- A circuit with fewer nodes than variables has no input node for some variable. -/
theorem exists_missing {n : ℕ} (C : BooleanCircuit n) (h : C.size < n) :
    ∃ i : Fin n, ∀ nd ∈ C.nodes, inputIndex nd ≠ some i := by
  classical
  have hS : ((C.nodes.filterMap inputIndex).toFinset).card < (Finset.univ : Finset (Fin n)).card := by
    calc ((C.nodes.filterMap inputIndex).toFinset).card ≤ (C.nodes.filterMap inputIndex).length :=
          List.toFinset_card_le _
      _ ≤ C.nodes.length := List.length_filterMap_le _ _
      _ < n := h
      _ = (Finset.univ : Finset (Fin n)).card := by simp
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hS
  refine ⟨i, fun nd hnd heq => hi ?_⟩
  rw [List.mem_toFinset, List.mem_filterMap]
  exact ⟨nd, hnd, heq⟩

/-- A bit as an element of `ZMod 2`. -/
def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bitZ_not (b : Bool) : bitZ (!b) = bitZ b + 1 := by
  cases b <;> decide

/-- Parity on `m` bits. -/
def par (m : ℕ) : BoolFunction m := fun x => decide ((∑ j, bitZ (x j)) = 1)

/-- Flip bit `i`. -/
def flipAt {m : ℕ} (i : Fin m) (x : BitInput m) : BitInput m := Function.update x i (!x i)

theorem flipAt_flipAt {m : ℕ} (i : Fin m) (x : BitInput m) : flipAt i (flipAt i x) = x := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [flipAt]
  · simp [flipAt, Function.update_of_ne hj]

theorem sum_flipAt {m : ℕ} (i : Fin m) (x : BitInput m) :
    (∑ j, bitZ (flipAt i x j)) = (∑ j, bitZ (x j)) + 1 := by
  classical
  have h1 : (∑ j, bitZ (flipAt i x j)) = ∑ j, Function.update (fun k => bitZ (x k)) i (bitZ (!x i)) j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold flipAt
    exact Function.apply_update (fun _ b => bitZ b) x i (!x i) j
  rw [h1, Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) (fun k => bitZ (x k)), bitZ_not]
  ring

theorem par_flipAt {m : ℕ} (i : Fin m) (x : BitInput m) : par m (flipAt i x) = !par m x := by
  unfold par
  rw [sum_flipAt]
  generalize (∑ j, bitZ (x j)) = s
  revert s
  decide

/-- The agreement count of parity with a circuit of fewer than `m` nodes is exactly `2^{m-1}`. -/
theorem parity_agreement {m : ℕ} (C : BooleanCircuit m) (h : C.size < m) :
    2 * (Finset.univ.filter fun x => C.eval x = par m x).card = 2 ^ m := by
  classical
  obtain ⟨i, hi⟩ := exists_missing C h
  have hflip : ∀ x, C.eval (flipAt i x) = C.eval x := fun x =>
    eval_eq_of_missing C i hi _ _ (fun j hj => by simp [flipAt, Function.update_of_ne hj])
  have hAB : (Finset.univ.filter fun x => C.eval x = par m x).card =
      (Finset.univ.filter fun x => ¬ (C.eval x = par m x)).card := by
    refine Finset.card_nbij' (flipAt i) (flipAt i) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      rw [hflip, par_flipAt, hx]
      cases par m x <;> decide
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      rw [hflip, par_flipAt]
      revert hx
      cases C.eval x <;> cases par m x <;> decide
    · intro x _
      exact flipAt_flipAt i x
    · intro x _
      exact flipAt_flipAt i x
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BitInput m)))
    (fun x => C.eval x = par m x)
  have huniv : (Finset.univ : Finset (BitInput m)).card = 2 ^ m := by simp [Finset.card_univ]
  omega

/-- Parity on `m` bits cannot be `(1/2 + ε)`-approximated (any `ε > 0`) by circuits of size `s < m`. -/
theorem parity_cannotBeApproximated (m : ℕ) (ε s : ℝ) (hε : 0 < ε) (hs : s < m) :
    CannotBeApproximated (par m) ε s := by
  intro C hC
  have hsize : C.size < m := by
    have : (C.size : ℝ) < m := lt_of_le_of_lt hC hs
    exact_mod_cast this
  have h := parity_agreement C hsize
  have hR : (2 : ℝ) * ((Finset.univ.filter fun x => C.eval x = par m x).card : ℝ) = 2 ^ m := by
    exact_mod_cast h
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  nlinarith [mul_pos hε hp]

end NearCubicGates.Adapters.Amplification
