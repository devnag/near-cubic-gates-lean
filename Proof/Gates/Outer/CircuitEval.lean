import Proof.Gates.Outer.Circuit

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires NearCubicWires.Bindings.MW20

variable {q ℓ : ℕ}

/-- One evaluation step of a Boolean DAG (the step of `BooleanCircuit.values`). -/
def pushEval {n : ℕ} (r : BitInput n) (prior : Array Bool) (node : BooleanNode n) : Array Bool :=
  prior.push (node.eval r prior)

theorem foldl_pushEval_size {n : ℕ} (r : BitInput n) :
    ∀ (ds : List (BooleanNode n)) (P : Array Bool), (ds.foldl (pushEval r) P).size = P.size + ds.length
  | [], P => by simp
  | d :: ds, P => by
      simp only [List.foldl_cons, List.length_cons]
      rw [foldl_pushEval_size r ds]
      simp [pushEval]
      omega

theorem foldl_pushEval_prefix {n : ℕ} (r : BitInput n) :
    ∀ (ds : List (BooleanNode n)) (P : Array Bool) (p : ℕ), p < P.size →
      (ds.foldl (pushEval r) P)[p]? = P[p]?
  | [], P, p, _ => by simp
  | d :: ds, P, p, hp => by
      simp only [List.foldl_cons]
      rw [foldl_pushEval_prefix r ds _ p (by simp [pushEval]; omega)]
      simp [pushEval, Array.getElem?_push, show p ≠ P.size by omega]

/-- The value read through a copy reference agrees with `B`'s own read. -/
theorem copyRef_val (off t c : ℕ) (P Q : Array Bool) (_hP : P.size = off + t) (hQ : Q.size = t)
    (hz : P[0]? = some false) (hagree : ∀ u < t, P[off + u]? = Q[u]?) :
    (P[copyRef off t c]?.getD false) = (Q[c]?.getD false) := by
  unfold copyRef
  by_cases hc : c < t
  · rw [if_pos hc, hagree c hc]
  · rw [if_neg hc, hz, Array.getElem?_eq_none (by omega)]
    rfl

/-- The wiring of `B`'s inputs inside the copy. -/
def WiredInput (P : Array Bool) (wires : List ℕ) (binput : BitInput q) : Prop :=
  ∀ j : Fin q, (if j.val < wires.length then (P[wires.getD j.val 0]?.getD false) else false) = binput j

theorem copyNode_eval (off : ℕ) (wires : List ℕ) (t : ℕ) (nd : BooleanNode q) (r : BitInput q)
    (binput : BitInput q) (P Q : Array Bool) (hP : P.size = off + t) (hQ : Q.size = t)
    (hz : P[0]? = some false) (hagree : ∀ u < t, P[off + u]? = Q[u]?) (hw : WiredInput P wires binput) :
    (copyNode off wires t nd).eval r P = nd.eval binput Q := by
  have hv := fun c => copyRef_val off t c P Q hP hQ hz hagree
  cases nd with
  | const b => rfl
  | input j =>
      have := hw j
      show (if j.val < wires.length then BooleanNode.or (wires.getD j.val 0) (wires.getD j.val 0)
        else BooleanNode.const false).eval r P = binput j
      by_cases hj : j.val < wires.length
      · rw [if_pos hj] at this ⊢
        simp only [BooleanNode.eval, Bool.or_self]
        exact this
      · rw [if_neg hj] at this ⊢
        exact this
  | not c => simp only [copyNode, BooleanNode.eval, hv]
  | and l r' => simp only [copyNode, BooleanNode.eval, hv]
  | or l r' => simp only [copyNode, BooleanNode.eval, hv]

theorem wiredInput_mono (P P' : Array Bool) (wires : List ℕ) (binput : BitInput q) (off : ℕ)
    (hwires : ∀ x ∈ wires, x < off) (hle : off ≤ P.size) (hpre : ∀ p < P.size, P'[p]? = P[p]?)
    (hw : WiredInput P wires binput) : WiredInput P' wires binput := by
  intro j
  rw [← hw j]
  split
  · rename_i hj
    have hx : wires.getD j.val 0 < off := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact hwires _ (List.getElem_mem hj)
    rw [hpre _ (by omega)]
  · rfl

/-- The copy of `B` computes `B`'s node values at the offset. -/
theorem copy_fold (off : ℕ) (wires : List ℕ) (r binput : BitInput q) (hoff : 1 ≤ off)
    (hwires : ∀ x ∈ wires, x < off) :
    ∀ (bs : List (BooleanNode q)) (t : ℕ) (P Q : Array Bool), P.size = off + t → Q.size = t →
      P[0]? = some false → (∀ u < t, P[off + u]? = Q[u]?) → WiredInput P wires binput →
      ∀ u < t + bs.length,
        ((copyNodesFrom off wires t bs).foldl (pushEval r) P)[off + u]? = (bs.foldl (pushEval binput) Q)[u]?
  | [], t, P, Q, _, _, _, hagree, _, u, hu => by
      simp only [copyNodesFrom, List.foldl_nil]
      exact hagree u (by simpa using hu)
  | nd :: rest, t, P, Q, hP, hQ, hz, hagree, hw, u, hu => by
      simp only [copyNodesFrom, List.foldl_cons]
      have hnode := copyNode_eval off wires t nd r binput P Q hP hQ hz hagree hw
      refine copy_fold off wires r binput hoff hwires rest (t + 1) _ _ ?_ ?_ ?_ ?_ ?_ u ?_
      · simp only [pushEval, Array.size_push, hP]; omega
      · simp [pushEval, hQ]
      · simp only [pushEval]
        rw [Array.getElem?_push, if_neg (by omega)]
        exact hz
      · intro v hv
        simp only [pushEval, Array.getElem?_push]
        by_cases hvt : v < t
        · rw [if_neg (by omega), if_neg (by omega)]
          exact hagree v hvt
        · rw [if_pos (by omega), if_pos (by omega), hnode]
      · exact wiredInput_mono P _ wires binput off hwires (by omega)
          (fun p hp => by simp only [pushEval]; rw [Array.getElem?_push, if_neg (by omega)]) hw
      · simpa [Nat.add_assoc, Nat.add_comm 1] using hu

/-- `B.values` is the fold of `pushEval`. -/
theorem values_eq_fold {n : ℕ} (B : BooleanCircuit n) (input : BitInput n) :
    B.values input = B.nodes.foldl (pushEval input) #[] := rfl

/-- `C^O.values` is a fold too. -/
def oPush (O : BitInput ℓ → Bool) (rC : BitInput ℓ) (prior : Array Bool) (nd : OracleNode ℓ ℓ) : Array Bool :=
  prior.push (nd.eval O rC prior)

/-- The invariant of the main fold: the image of every node of `C` carries `C`'s value; the zero wire is `false`. -/
structure SubstInv (r : BitInput q) (CV : Array Bool) (acc : List (BooleanNode q) × List ℕ) : Prop where
  ok : BuildOK acc
  zero : (acc.1.foldl (pushEval r) #[])[0]? = some false
  sizeMap : acc.2.length = CV.size
  agree : ∀ c, ((acc.1.foldl (pushEval r) #[])[ref acc.2 c]?.getD false) = (CV[c]?.getD false)

theorem fold_append {n : ℕ} (r : BitInput n) (ds more : List (BooleanNode n)) :
    (ds ++ more).foldl (pushEval r) #[] = more.foldl (pushEval r) (ds.foldl (pushEval r) #[]) := by
  simp [List.foldl_append]

theorem ref_append_lt (map : List ℕ) (x c : ℕ) (hc : c < map.length) : ref (map ++ [x]) c = ref map c := by
  unfold ref
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hc]

theorem ref_append_eq (map : List ℕ) (x : ℕ) : ref (map ++ [x]) map.length = x := by
  unfold ref
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem ref_append_gt (map : List ℕ) (x c : ℕ) (hc : map.length + 1 ≤ c) : ref (map ++ [x]) c = 0 := by
  unfold ref
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  rfl

/-- Re-establish the invariant after appending `more` and recording `x`, given the value of the image. -/
theorem substInv_extend (r : BitInput q) (CV : Array Bool) (acc : List (BooleanNode q) × List ℕ)
    (h : SubstInv r CV acc) (more : List (BooleanNode q)) (x : ℕ) (b : Bool)
    (hok : BuildOK (acc.1 ++ more, acc.2 ++ [x]))
    (hx : (((acc.1 ++ more).foldl (pushEval r) #[])[x]?.getD false) = b) :
    SubstInv r (CV.push b) (acc.1 ++ more, acc.2 ++ [x]) := by
  have hsize : (acc.1.foldl (pushEval r) #[]).size = acc.1.length := by
    simp [foldl_pushEval_size]
  have hpre : ∀ p < acc.1.length,
      ((acc.1 ++ more).foldl (pushEval r) #[])[p]? = (acc.1.foldl (pushEval r) #[])[p]? := by
    intro p hp
    rw [fold_append]
    exact foldl_pushEval_prefix r more _ p (by omega)
  have h1 := h.ok.1
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hpre 0 (by omega)]
    exact h.zero
  · simp [h.sizeMap]
  · intro c
    rcases Nat.lt_trichotomy c acc.2.length with hc | hc | hc
    · rw [ref_append_lt _ _ _ hc, hpre _ (ref_lt h.ok.2.2 h1 c), h.agree c, Array.getElem?_push,
        if_neg (by rw [← h.sizeMap]; omega)]
    · subst hc
      rw [ref_append_eq, hx, Array.getElem?_push, if_pos h.sizeMap]
      rfl
    · rw [ref_append_gt _ _ _ (by omega), hpre 0 (by omega), h.zero, Array.getElem?_eq_none]
      · rfl
      · simp; rw [← h.sizeMap]; omega

theorem substStep_inv (B : BooleanCircuit q) (r : BitInput q) (CV : Array Bool)
    (acc : List (BooleanNode q) × List ℕ) (h : SubstInv r CV acc) (nd : OracleNode ℓ ℓ) :
    SubstInv r (oPush (fun a => B.eval (padQuery a)) (truncInput r) CV nd) (substStep B acc nd) := by
  have hsize : (acc.1.foldl (pushEval r) #[]).size = acc.1.length := by
    simp [foldl_pushEval_size]
  have hok := substStepG_ok B inputMapD [] inputMapD_wellFormed acc nd h.ok (by simp)
  -- one appended node: its value is the node's evaluation on the old array
  have single : ∀ (node : BooleanNode q) (b : Bool), node.eval r (acc.1.foldl (pushEval r) #[]) = b →
      BuildOK (acc.1 ++ [node], acc.2 ++ [acc.1.length]) →
      SubstInv r (CV.push b) (acc.1 ++ [node], acc.2 ++ [acc.1.length]) := by
    intro node b hb hok'
    apply substInv_extend r CV acc h [node] acc.1.length b hok'
    rw [fold_append]
    simp only [List.foldl_cons, List.foldl_nil, pushEval]
    rw [Array.getElem?_push, if_pos hsize.symm]
    simpa using hb
  cases nd with
  | const b => exact single _ _ rfl hok
  | input i =>
      apply single _ _ _ hok
      show (inputMapD i).eval r _ = truncInput r i
      unfold inputMapD truncInput
      split <;> rfl
  | not c =>
      apply single _ _ _ hok
      simp only [BooleanNode.eval, OracleNode.eval, h.agree]
  | and a b =>
      apply single _ _ _ hok
      simp only [BooleanNode.eval, OracleNode.eval, h.agree]
  | or a b =>
      apply single _ _ _ hok
      simp only [BooleanNode.eval, OracleNode.eval, h.agree]
  | oracle args =>
      let P := acc.1.foldl (pushEval r) #[]
      let wires := (List.ofFn fun j => ref acc.2 (args j)) ++ []
      let a : BitInput ℓ := fun j => CV[args j]?.getD false
      have h1 := h.ok.1
      have hwires : ∀ x ∈ wires, x < acc.1.length := by
        intro x hx
        simp only [wires, List.append_nil, List.mem_ofFn] at hx
        obtain ⟨j, rfl⟩ := hx
        exact ref_lt h.ok.2.2 h1 _
      have hw : WiredInput P wires (padQuery (q := q) a) := by
        intro j
        unfold padQuery
        by_cases hj : j.val < ℓ
        · have hl : j.val < wires.length := by simp [wires, hj]
          rw [if_pos hl, dif_pos hj]
          have hg : wires.getD j.val 0 = ref acc.2 (args ⟨j.val, hj⟩) := by
            simp [wires, List.getD_eq_getElem?_getD, hj]
          rw [hg, h.agree]
        · have hl : ¬ j.val < wires.length := by simp [wires, hj]
          rw [if_neg hl, dif_neg hj]
      have hcopy := copy_fold acc.1.length wires r (padQuery (q := q) a) h1 hwires B.nodes 0 P #[]
        (by simp [P, hsize]) rfl h.zero (fun u hu => absurd hu (by omega)) hw
      apply substInv_extend r CV acc h _ (acc.1.length + B.output.val) _ hok
      rw [fold_append, hcopy B.output.val (by simp)]
      show ((B.values (padQuery a))[B.output.val]?.getD false) = OracleNode.eval _ _ _ (.oracle args)
      rfl

theorem subst_fold_inv (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) (r : BitInput q) :
    SubstInv r (C.values (fun a => B.eval (padQuery a)) (truncInput r)) (substBuild C B) := by
  unfold substBuild substBuildG OracleCircuit.values
  have base : SubstInv r #[] (([BooleanNode.const false], []) : List (BooleanNode q) × List ℕ) := by
    refine ⟨?_, ?_, by simp, ?_⟩
    · refine ⟨by simp, ?_, by simp⟩
      intro p hp
      simp only [List.length_singleton] at hp
      have : p = 0 := by omega
      subst this
      trivial
    · rfl
    · intro c
      simp [ref, pushEval, BooleanNode.eval]
  generalize hacc : (([BooleanNode.const false], []) : List (BooleanNode q) × List ℕ) = acc0 at base
  generalize hCV : (#[] : Array Bool) = CV0 at base
  clear hacc hCV
  induction C.nodes generalizing acc0 CV0 with
  | nil => simpa using base
  | cons nd rest ih =>
      simp only [List.foldl_cons]
      exact ih _ _ (substStep_inv B r CV0 acc0 base nd)

/-- **The semantics of `D` before padding.** `D(r) = ¬C^{O}(r|_ℓ)` with `O(a) = B(a, 0^{q−ℓ})`. -/
theorem subst_eval (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) (r : BitInput q) :
    (substCircuit C B).eval r = !(C.eval (fun a => B.eval (padQuery a)) (truncInput r)) := by
  have hinv := subst_fold_inv C B r
  have hsize : ((substBuild C B).1.foldl (pushEval r) #[]).size = (substBuild C B).1.length := by
    simp [foldl_pushEval_size]
  unfold BooleanCircuit.eval OracleCircuit.eval
  rw [values_eq_fold]
  show ((substNodes C B).foldl (pushEval r) #[])[(substBuild C B).1.length]?.getD false = _
  unfold substNodes
  rw [fold_append]
  simp only [List.foldl_cons, List.foldl_nil, pushEval]
  rw [Array.getElem?_push, if_pos hsize.symm]
  simp only [Option.getD_some, BooleanNode.eval]
  rw [hinv.agree]
  rfl

end NearCubicGates.Close.Outer
