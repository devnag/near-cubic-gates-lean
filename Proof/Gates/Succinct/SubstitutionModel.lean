import Proof.Gates.Outer.Circuit
import Proof.Foundations.BooleanCircuitSizePadding
import Proof.PCP.PCPPNativeRequestSchema

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.Bindings.MW20 NearCubicGates.Close.Outer

variable {q ℓ : ℕ}

/-- Is the node an oracle gate. -/
def isO : OracleNode ℓ ℓ → Bool
  | .oracle _ => true
  | _ => false

section
variable (B : BooleanCircuit q) (C : OracleCircuit ℓ ℓ)

/-- The fold of the substitution over the first `i` nodes of `C` (`sec:gadget-machine`, `D_B`). -/
def accI (i : ℕ) : List (BooleanNode q) × List ℕ :=
  (C.nodes.take i).foldl (substStepG B inputMapD []) ([.const false], [])

/-- The number of oracle gates among the first `i` nodes of `C`. -/
def kOf (i : ℕ) : ℕ := (C.nodes.take i).countP (fun nd => isO nd)

/-- The oracle flags of `C`'s nodes (the machine's flag tape). -/
def ofl : List Bool := C.nodes.map isO

/-- Is node `c` an oracle gate (`false` out of range). -/
def nodeO (c : ℕ) : Bool := (ofl C).getD c false

/-- The image of node `c` of `C` in `D_B`. -/
def posM (c : ℕ) : ℕ := (accI B C c).1.length + if nodeO C c then B.output.val else 0

theorem accI_zero : accI B C 0 = ([.const false], []) := by simp [accI]

theorem accI_succ (i : ℕ) (h : i < C.nodes.length) :
    accI B C (i + 1) = substStepG B inputMapD [] (accI B C i) C.nodes[i] := by
  unfold accI
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append]
  rfl

theorem kOf_succ (i : ℕ) (h : i < C.nodes.length) :
    kOf C (i + 1) = kOf C i + if isO C.nodes[i] then 1 else 0 := by
  unfold kOf
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.countP_append,
    List.countP_singleton]

theorem nodeO_lt (c : ℕ) (h : c < C.nodes.length) : nodeO C c = isO C.nodes[c] := by
  simp [nodeO, ofl, List.getD_eq_getElem?_getD, h]

theorem step_fst_len (acc : List (BooleanNode q) × List ℕ) (nd : OracleNode ℓ ℓ) :
    (substStepG B inputMapD [] acc nd).1.length = acc.1.length + if isO nd then B.nodes.length else 1 := by
  cases nd <;> simp [substStepG, isO, copyNodesFrom_length]

theorem step_snd (acc : List (BooleanNode q) × List ℕ) (nd : OracleNode ℓ ℓ) :
    (substStepG B inputMapD [] acc nd).2 = acc.2 ++ [acc.1.length + if isO nd then B.output.val else 0] := by
  cases nd <;> simp [substStepG, isO]

/-- **The size of the fold.** -/
theorem accI_fst_len : ∀ i, i ≤ C.nodes.length →
    (accI B C i).1.length + kOf C i = 1 + i + kOf C i * B.nodes.length
  | 0, _ => by simp [accI_zero, kOf]
  | i + 1, h => by
    have ih := accI_fst_len i (by omega)
    rw [accI_succ B C i (by omega), kOf_succ C i (by omega), step_fst_len]
    split_ifs with hO
    · simp only [Nat.add_mul, Nat.one_mul]; omega
    · simp only [Nat.add_zero]; omega

theorem accI_snd_len : ∀ i, i ≤ C.nodes.length → (accI B C i).2.length = i
  | 0, _ => by simp [accI_zero]
  | i + 1, h => by
    rw [accI_succ B C i (by omega), step_snd]
    simp [accI_snd_len i (by omega)]

/-- **The recorded images.** -/
theorem accI_snd_getD : ∀ i, i ≤ C.nodes.length → ∀ c, c < i → (accI B C i).2.getD c 0 = posM B C c
  | 0, _, c, hc => by omega
  | i + 1, h, c, hc => by
    rw [accI_succ B C i (by omega), step_snd]
    have hl := accI_snd_len B C i (by omega)
    rcases Nat.lt_or_ge c i with hci | hci
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact accI_snd_getD i (by omega) c hci
    · have hce : c = i := by omega
      subst hce
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
      simp [posM, nodeO_lt C c (by omega)]

/-- `ref` into the fold is `posM` on earlier nodes. -/
theorem ref_accI (i : ℕ) (h : i ≤ C.nodes.length) (c : ℕ) (hc : c < i) : ref (accI B C i).2 c = posM B C c :=
  accI_snd_getD B C i h c hc

/-- **The image formula** the machine evaluates: `1 + c + k_c·(n_B − 1) + [c oracle]·o_B`. -/
theorem posM_eq (c : ℕ) (h : c ≤ C.nodes.length) (hB : 1 ≤ B.nodes.length) :
    posM B C c = 1 + c + kOf C c * (B.nodes.length - 1) + if nodeO C c then B.output.val else 0 := by
  have hl := accI_fst_len B C c h
  unfold posM
  have e : kOf C c * B.nodes.length = kOf C c * (B.nodes.length - 1) + kOf C c := by
    obtain ⟨m, hm⟩ : ∃ m, B.nodes.length = m + 1 := ⟨B.nodes.length - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, Nat.mul_succ]
  omega

/-- The oracle count is the number of `true` flags before `c`. -/
theorem kOf_count (c : ℕ) : kOf C c = ((ofl C).take c).count true := by
  unfold kOf ofl
  rw [← List.map_take, List.count_eq_countP, List.countP_map]
  congr 1
  funext nd
  simp

end

/-! ## Copies of `B` -/

theorem copyNodesFrom_take (off : ℕ) (wires : List ℕ) :
    ∀ (s : ℕ) (l : List (BooleanNode q)) (t : ℕ) (ht : t < l.length),
      copyNodesFrom off wires s (l.take (t + 1)) =
        copyNodesFrom off wires s (l.take t) ++ [copyNode off wires (s + t) l[t]]
  | s, [], t, ht => by simp at ht
  | s, nd :: l, 0, _ => by simp [copyNodesFrom]
  | s, nd :: l, t + 1, ht => by
    have ih := copyNodesFrom_take off wires (s + 1) l t (by simpa using ht)
    simp only [List.take_succ_cons, copyNodesFrom, ih, List.cons_append, List.getElem_cons_succ,
      show s + (t + 1) = s + 1 + t by omega]

/-! ## The descriptor of `D_B` -/

theorem padSize_nodes' {n : ℕ} (c : BooleanCircuit n) (k : ℕ) :
    (c.padSize k).nodes = c.nodes ++ List.replicate k (.const false) := by
  simp only [BooleanCircuit.padSize, BooleanDAGBuilder.finish, BooleanDAGBuilder.appendFalse_nodes,
    BooleanCircuit.toBuilder]

theorem padSize_output' {n : ℕ} (c : BooleanCircuit n) (k : ℕ) : (c.padSize k).output.val = c.output.val := by
  simp only [BooleanCircuit.padSize, BooleanDAGBuilder.finish, BooleanDAGExtension.lift_val]

theorem substBuild_eq (B : BooleanCircuit q) (C : OracleCircuit ℓ ℓ) : substBuild C B = accI B C C.nodes.length := by
  simp [substBuild, substBuildG, accI]

/-- **The descriptor of `D_B`** (`sec:gadget-machine`): the arity `q`, the node count, the fold's nodes, the negation of
`C`'s output image, `q − (|fold| + 1)` constant padding nodes, and the output index `|fold|`. -/
theorem descriptor_D (B : BooleanCircuit q) (C : OracleCircuit ℓ ℓ) :
    PCPPNative.descriptor (substCircuit C B).padToArity =
      RepairRepresentation.natWord q ++
        RepairRepresentation.natWord ((accI B C C.nodes.length).1.length + 1 +
          (q - ((accI B C C.nodes.length).1.length + 1))) ++
        ((accI B C C.nodes.length).1 ++ [(BooleanNode.not (posM B C C.output.val) : BooleanNode q)] ++
          List.replicate (q - ((accI B C C.nodes.length).1.length + 1)) (BooleanNode.const false : BooleanNode q)).flatMap
            RepairOrdinary.PCPPRequestNodeSchema.native ++
        RepairRepresentation.natWord (accI B C C.nodes.length).1.length := by
  have hsz : (substCircuit C B).size = (accI B C C.nodes.length).1.length + 1 := by
    rw [substCircuit_size, substBuild_eq]
  have href : ref (accI B C C.nodes.length).2 C.output.val = posM B C C.output.val :=
    ref_accI B C _ le_rfl _ C.output.isLt
  rw [PCPPNative.descriptor_eq]
  unfold BooleanCircuit.padToArity
  rw [padSize_output', padSize_nodes', hsz]
  simp only [substCircuit, substNodes, substBuild_eq, href, List.length_append, List.length_replicate,
    List.length_singleton, List.append_assoc, Nat.add_assoc]

end NearCubicGates.Close.Succinct.SubstMachine
