import Proof.Gates.Gadget.CheckedSize

set_option autoImplicit false

namespace NearCubicGates.Close.Gadget

open NearCubicWires NearCubicGates.PublishedSources.PCPP NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary NearCubicWires.Bindings.CLW20Lemma311

variable {n : ℕ}

/-! ## One-node builders -/

@[simp] theorem addInput_nodes (b0 : BooleanDAGBuilder n) (i : Fin n) :
    (addInput b0 i).ext.b.nodes = b0.nodes ++ [.input i] := by simp [addInput, Ext.one]
@[simp] theorem addInput_out (b0 : BooleanDAGBuilder n) (i : Fin n) : (addInput b0 i).out = b0.nodes.length := rfl
@[simp] theorem addConst_nodes (b0 : BooleanDAGBuilder n) (v : Bool) :
    (addConst b0 v).ext.b.nodes = b0.nodes ++ [.const v] := by simp [addConst, Ext.one]
@[simp] theorem addConst_out (b0 : BooleanDAGBuilder n) (v : Bool) : (addConst b0 v).out = b0.nodes.length := rfl
@[simp] theorem addNot_nodes (b0 : BooleanDAGBuilder n) {r : ℕ} {f : BitInput n → Bool} (hr : Computes b0 r f)
    (hlt : r < b0.nodes.length) : (addNot b0 hr hlt).ext.b.nodes = b0.nodes ++ [.not r] := by simp [addNot, Ext.one]
@[simp] theorem addNot_out (b0 : BooleanDAGBuilder n) {r : ℕ} {f : BitInput n → Bool} (hr : Computes b0 r f)
    (hlt : r < b0.nodes.length) : (addNot b0 hr hlt).out = b0.nodes.length := rfl
@[simp] theorem addAnd_nodes (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addAnd b0 hr hs hlt).ext.b.nodes = b0.nodes ++ [.and r s] := by simp [addAnd, Ext.one]
@[simp] theorem addAnd_out (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addAnd b0 hr hs hlt).out = b0.nodes.length := rfl
@[simp] theorem addOr_nodes (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addOr b0 hr hs hlt).ext.b.nodes = b0.nodes ++ [.or r s] := by simp [addOr, Ext.one]
@[simp] theorem addOr_out (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addOr b0 hr hs hlt).out = b0.nodes.length := rfl

/-- The nodes `addXor` appends at index `k` for children `r, s`. -/
def xorNodes (k r s : ℕ) : List (BooleanNode n) := [.or r s, .and r s, .not (k + 1), .and k (k + 2)]

@[simp] theorem addXor_nodes (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addXor b0 hr hs hlt).ext.b.nodes = b0.nodes ++ xorNodes b0.nodes.length r s := by
  simp [addXor, xorNodes]

@[simp] theorem addXor_out (b0 : BooleanDAGBuilder n) {r s : ℕ} {f g : BitInput n → Bool} (hr : Computes b0 r f)
    (hs : Computes b0 s g) (hlt : r < b0.nodes.length ∧ s < b0.nodes.length) :
    (addXor b0 hr hs hlt).out = b0.nodes.length + 3 := by
  simp [addXor]

/-! ## Parity chains -/

/-- The nodes of a parity chain from index `k` with accumulator node `r`, and its output node. -/
def parityFromNodes : ℕ → List (Fin n) → ℕ → List (BooleanNode n) × ℕ
  | _, [], r => ([], r)
  | k, i :: rest, r =>
    let t := parityFromNodes (k + 5) rest (k + 4)
    ([.input i] ++ xorNodes (k + 1) r k ++ t.1, t.2)

theorem addParityFrom_nodes (b0 : BooleanDAGBuilder n) (l : List (Fin n)) {r : ℕ} {acc : BitInput n → Bool}
    (hr : Computes b0 r acc) :
    (addParityFrom b0 l hr).ext.b.nodes = b0.nodes ++ (parityFromNodes b0.nodes.length l r).1 ∧
      (addParityFrom b0 l hr).out = (parityFromNodes b0.nodes.length l r).2 := by
  induction l generalizing b0 r acc with
  | nil => simp [addParityFrom, parityFromNodes]
  | cons i rest ih =>
    simp only [addParityFrom, Ext.trans_b]
    rw [(ih _ _).1, (ih _ _).2]
    simp [parityFromNodes, xorNodes, Nat.add_assoc]

/-- The nodes of `addParity` from index `k`. -/
def parityNodes (k : ℕ) (l : List (Fin n)) : List (BooleanNode n) × ℕ :=
  ([.const false] ++ (parityFromNodes (k + 1) l k).1, (parityFromNodes (k + 1) l k).2)

theorem addParity_nodes (b0 : BooleanDAGBuilder n) (l : List (Fin n)) :
    (addParity b0 l).ext.b.nodes = b0.nodes ++ (parityNodes b0.nodes.length l).1 ∧
      (addParity b0 l).out = (parityNodes b0.nodes.length l).2 := by
  simp only [addParity, Ext.trans_b]
  rw [(addParityFrom_nodes _ l _).1, (addParityFrom_nodes _ l _).2]
  simp [parityNodes]

/-! ## Checks -/

section Checks
variable (E : LinearCodeFamily) (q : ℕ)

/-- The nodes of one check from index `k`. -/
def checkNodes (k : ℕ) (j : Fin (E.length q)) : List (BooleanNode (q + E.length q)) × ℕ :=
  let p := parityNodes k ((canonList (E.support q j)).map (Fin.castAdd (E.length q)))
  let k1 := k + p.1.length
  (p.1 ++ [.input (Fin.natAdd q j)] ++ xorNodes (k1 + 1) k1 p.2 ++ [.not (k1 + 4)], k1 + 5)

theorem addCheck_nodes (b0 : BooleanDAGBuilder (q + E.length q)) (j : Fin (E.length q)) :
    (addCheck E q b0 j).ext.b.nodes = b0.nodes ++ (checkNodes E q b0.nodes.length j).1 ∧
      (addCheck E q b0 j).out = (checkNodes E q b0.nodes.length j).2 := by
  simp only [addCheck, Ext.trans_b]
  have hp := addParity_nodes b0 ((canonList (E.support q j)).map (Fin.castAdd (E.length q)))
  simp only [addNot_nodes, addNot_out, addXor_nodes, addXor_out, addInput_nodes, addInput_out]
  rw [hp.1, hp.2]
  simp [checkNodes, xorNodes, Nat.add_assoc]

/-- The nodes of all checks in `js` from index `k`, conjoined onto the node `r`. -/
def checksNodes : ℕ → List (Fin (E.length q)) → ℕ → List (BooleanNode (q + E.length q)) × ℕ
  | _, [], r => ([], r)
  | k, j :: rest, r =>
    let c := checkNodes E q k j
    let k2 := k + c.1.length
    let t := checksNodes (k2 + 1) rest k2
    (c.1 ++ [.and r c.2] ++ t.1, t.2)

theorem addChecks_nodes (b0 : BooleanDAGBuilder (q + E.length q)) (js : List (Fin (E.length q)))
    {r : ℕ} {base : BitInput (q + E.length q) → Bool} (hr : Computes b0 r base) :
    (addChecks E q b0 js hr).ext.b.nodes = b0.nodes ++ (checksNodes E q b0.nodes.length js r).1 ∧
      (addChecks E q b0 js hr).out = (checksNodes E q b0.nodes.length js r).2 := by
  induction js generalizing b0 r base with
  | nil => simp [addChecks, checksNodes]
  | cons j rest ih =>
    simp only [addChecks, Ext.trans_b]
    rw [(ih _ _).1, (ih _ _).2]
    simp only [addAnd_nodes, addAnd_out]
    rw [(addCheck_nodes E q b0 j).1, (addCheck_nodes E q b0 j).2]
    simp [checksNodes, Nat.add_assoc]

end Checks

/-- The node list of the checked circuit before padding, and its output node. -/
def checkedRaw (E : LinearCodeFamily) (D : Circuit) : List (BooleanNode (D.n + E.length D.n)) × ℕ :=
  let c := checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val
  (D.D.nodes.map liftNode ++ c.1, c.2)

/-- **The checked circuit in closed form.** -/
theorem checkedCircuit_nodes (E : LinearCodeFamily) (D : Circuit) :
    (checkedCircuit E D).D.nodes = (checkedRaw E D).1 ++
      List.replicate ((D.n + E.length D.n) - (checkedRaw E D).1.length) (.const false) ∧
      (checkedCircuit E D).D.output.val = (checkedRaw E D).2 := by
  have h := addChecks_nodes E D.n (liftBuilder D.D) (List.finRange (E.length D.n)) (liftBuilder_output D.D)
  rw [liftBuilder_length] at h
  have hl : (liftBuilder (L := E.length D.n) D.D).nodes = D.D.nodes.map liftNode := rfl
  rw [hl] at h
  unfold checkedCircuit BooleanCircuit.padToArity BooleanCircuit.padSize
  simp only [BooleanDAGBuilder.finish, BooleanCircuit.toBuilder, BooleanDAGBuilder.appendFalse_nodes,
    BooleanDAGExtension.lift_val, BooleanCircuit.size]
  rw [h.1, h.2]
  exact ⟨rfl, rfl⟩

end NearCubicGates.Close.Gadget
