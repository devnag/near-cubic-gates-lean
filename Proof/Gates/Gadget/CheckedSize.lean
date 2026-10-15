import Proof.Gates.Gadget.Checked

/-!
# The size of the checked circuit — paper v2 line 2101 ("a polynomial-size list of three-literal clauses")

Exact node counts of the circuit-kit builders, and `(checkedCircuit E D).m ≤ D.m + L(8 + 5q) + q + L` with
`q = D.n`, `L = E.length q`: the checks add one parity chain (at most `q` XORs of five nodes) and five more nodes per
code bit, and the padding adds at most the arity.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires NearCubicGates.PublishedSources.PCPP NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary NearCubicWires.Bindings.CLW20Lemma311

variable {n : ℕ}

@[simp] theorem Ext.one_length (b0 : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt b0.nodes.length) : (Ext.one b0 node hnode).b.nodes.length = b0.nodes.length + 1 := by
  simp [Ext.one]

@[simp] theorem Ext.trans_length {b0 : BooleanDAGBuilder n} (e : Ext b0) (e' : Ext e.b) :
    (e.trans e').b.nodes.length = e'.b.nodes.length := rfl

theorem addXor_length (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addXor b0 hr hs hlt).ext.b.nodes.length = b0.nodes.length + 4 := by
  simp [addXor, addOr, addAnd, addNot]

theorem addAnd_length (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addAnd b0 hr hs hlt).ext.b.nodes.length = b0.nodes.length + 1 := by
  simp [addAnd]

theorem addParityFrom_length (b0 : BooleanDAGBuilder n) (l : List (Fin n)) {r : ℕ} {acc : BitInput n → Bool}
    (hr : Computes b0 r acc) : (addParityFrom b0 l hr).ext.b.nodes.length = b0.nodes.length + 5 * l.length := by
  induction l generalizing b0 r acc with
  | nil => simp [addParityFrom]
  | cons i rest ih =>
    simp only [addParityFrom, Ext.trans_length]
    rw [ih, addXor_length]
    simp [addInput, List.length_cons]
    ring

theorem addParity_length (b0 : BooleanDAGBuilder n) (l : List (Fin n)) :
    (addParity b0 l).ext.b.nodes.length = b0.nodes.length + 1 + 5 * l.length := by
  simp only [addParity, Ext.trans_length]
  rw [addParityFrom_length]
  simp [addConst]

theorem canonList_length_le {q : ℕ} (S : Finset (Fin q)) : (canonList S).length ≤ q := by
  unfold canonList
  exact (List.length_filter_le _ _).trans (by simp)

section
variable (E : LinearCodeFamily) (q : ℕ)

theorem addCheck_length (b0 : BooleanDAGBuilder (q + E.length q)) (j : Fin (E.length q)) :
    (addCheck E q b0 j).ext.b.nodes.length ≤ b0.nodes.length + 7 + 5 * q := by
  simp only [addCheck, Ext.trans_length]
  rw [addNot.eq_def]
  simp only [Ext.one_length]
  rw [addXor_length]
  simp only [addInput, Ext.one_length]
  rw [addParity_length]
  have := canonList_length_le (E.support q j)
  simp only [List.length_map]
  omega

theorem addChecks_length (b0 : BooleanDAGBuilder (q + E.length q)) (js : List (Fin (E.length q)))
    {r : ℕ} {base : BitInput (q + E.length q) → Bool} (hr : Computes b0 r base) :
    (addChecks E q b0 js hr).ext.b.nodes.length ≤ b0.nodes.length + js.length * (8 + 5 * q) := by
  induction js generalizing b0 r base with
  | nil => simp [addChecks]
  | cons j rest ih =>
    simp only [addChecks, Ext.trans_length]
    refine (ih _ _).trans ?_
    rw [Ext.trans_length, addAnd_length]
    have := addCheck_length E q b0 j
    have hm : (rest.length + 1) * (8 + 5 * q) = rest.length * (8 + 5 * q) + (8 + 5 * q) := by ring
    simp only [List.length_cons]
    omega

end

theorem liftBuilder_length {q L : ℕ} (D : BooleanCircuit q) : (liftBuilder (L := L) D).nodes.length = D.size := by
  simp [liftBuilder, BooleanCircuit.size]

/-- The checked circuit has at most `D.m + L(8 + 5q) + q + L` nodes. -/
theorem checkedCircuit_m (E : LinearCodeFamily) (D : Circuit) :
    (checkedCircuit E D).m ≤ D.m + E.length D.n * (8 + 5 * D.n) + (D.n + E.length D.n) := by
  unfold checkedCircuit Circuit.m
  simp only
  refine (BooleanCircuit.padToArity_size_le _).trans ?_
  have h := addChecks_length E D.n (liftBuilder D.D) (List.finRange (E.length D.n)) (liftBuilder_output D.D)
  rw [liftBuilder_length, List.length_finRange] at h
  simp only [BooleanCircuit.size, BooleanDAGBuilder.finish] at h ⊢
  omega

end NearCubicGates.Close.Gadget
