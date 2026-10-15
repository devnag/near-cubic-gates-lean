import Proof.Gates.Gadget.CheckedNodes
import Proof.PCP.PCPPNativeRequestSchema

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.SourceInterfaces

theorem parityFromNodes_length {n : ℕ} : ∀ (k : ℕ) (l : List (Fin n)) (r : ℕ),
    (parityFromNodes k l r).1.length = 5 * l.length
  | _, [], _ => rfl
  | k, i :: rest, r => by
    simp only [parityFromNodes, List.length_append, List.length_cons, xorNodes, List.length_nil,
      parityFromNodes_length (k + 5) rest (k + 4)]
    ring

theorem parityFromNodes_append {n : ℕ} : ∀ (k : ℕ) (a b : List (Fin n)) (r : ℕ),
    parityFromNodes k (a ++ b) r = ((parityFromNodes k a r).1 ++
      (parityFromNodes (k + 5 * a.length) b (parityFromNodes k a r).2).1,
      (parityFromNodes (k + 5 * a.length) b (parityFromNodes k a r).2).2)
  | k, [], b, r => by simp [parityFromNodes]
  | k, i :: a, b, r => by
    simp only [List.cons_append, parityFromNodes, List.length_cons]
    rw [parityFromNodes_append (k + 5) a b (k + 4)]
    have e : k + 5 + 5 * a.length = k + 5 * (a.length + 1) := by ring
    rw [e]
    simp only [List.append_assoc]

theorem parityFromNodes_single {n : ℕ} (k : ℕ) (i : Fin n) (r : ℕ) :
    parityFromNodes k [i] r = ([.input i] ++ xorNodes (k + 1) r k, k + 4) := by
  simp [parityFromNodes]

section Checks
variable (E : LinearCodeFamily) (q : ℕ)

theorem checkNodes_length (k : ℕ) (j : Fin (E.length q)) :
    (checkNodes E q k j).1.length = 5 * (canonList (E.support q j)).length + 7 := by
  simp only [checkNodes, parityNodes, List.length_append, List.length_cons, List.length_nil, xorNodes,
    parityFromNodes_length, List.length_map]
  ring

theorem checksNodes_append : ∀ (k : ℕ) (a b : List (Fin (E.length q))) (r : ℕ),
    checksNodes E q k (a ++ b) r = ((checksNodes E q k a r).1 ++
      (checksNodes E q (k + (checksNodes E q k a r).1.length) b (checksNodes E q k a r).2).1,
      (checksNodes E q (k + (checksNodes E q k a r).1.length) b (checksNodes E q k a r).2).2)
  | k, [], b, r => by simp [checksNodes]
  | k, j :: a, b, r => by
    simp only [List.cons_append, checksNodes]
    rw [checksNodes_append (k + (checkNodes E q k j).1.length + 1) a b (k + (checkNodes E q k j).1.length)]
    have e : k + (checkNodes E q k j).1.length + 1 +
        (checksNodes E q (k + (checkNodes E q k j).1.length + 1) a (k + (checkNodes E q k j).1.length)).1.length =
        k + ((checkNodes E q k j).1 ++ [BooleanNode.and r (checkNodes E q k j).2] ++
          (checksNodes E q (k + (checkNodes E q k j).1.length + 1) a (k + (checkNodes E q k j).1.length)).1).length := by
      simp; ring
    rw [e]
    simp only [List.append_assoc]

theorem checksNodes_single (k : ℕ) (j : Fin (E.length q)) (r : ℕ) :
    checksNodes E q k [j] r = ((checkNodes E q k j).1 ++ [.and r (checkNodes E q k j).2],
      k + (checkNodes E q k j).1.length) := by
  simp [checksNodes]

theorem checksNodes_length_ge : ∀ (k : ℕ) (js : List (Fin (E.length q))) (r : ℕ),
    8 * js.length ≤ (checksNodes E q k js r).1.length
  | _, [], _ => by simp [checksNodes]
  | k, j :: rest, r => by
    have := checksNodes_length_ge (k + (checkNodes E q k j).1.length + 1) rest (k + (checkNodes E q k j).1.length)
    simp only [checksNodes, List.length_append, List.length_cons, List.length_nil, checkNodes_length] at this ⊢
    omega

end Checks

theorem take_succ_finRange (n i : ℕ) (hi : i < n) :
    (List.finRange n).take (i + 1) = (List.finRange n).take i ++ [⟨i, hi⟩] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hi)]
  simp

/-- Lifting the inputs keeps the native bytes. -/
theorem native_liftNode {q L : ℕ} (nd : BooleanNode q) :
    PCPPRequestNodeSchema.native (liftNode (L := L) nd) = PCPPRequestNodeSchema.native nd := by
  cases nd <;> rfl

/-- The checked circuit has no padding. -/
theorem checkedCircuit_pad (E : LinearCodeFamily) (D : Circuit) :
    (checkedCircuit E D).D.nodes = (checkedRaw E D).1 := by
  rw [(checkedCircuit_nodes E D).1]
  have h1 := checksNodes_length_ge E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val
  have h2 : D.n ≤ D.D.nodes.length := D.sizeAtLeast
  have h3 : (checkedRaw E D).1.length = D.D.nodes.length +
      (checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).1.length := by
    simp [checkedRaw]
  rw [List.length_finRange] at h1
  rw [show D.n + E.length D.n - (checkedRaw E D).1.length = 0 by omega, List.replicate_zero]
  exact List.append_nil _

theorem descriptor_of {N : ℕ} (c : BooleanCircuit N) (l : List (BooleanNode N)) (o : ℕ) (hl : c.nodes = l)
    (ho : c.output.val = o) :
    PCPPNative.descriptor c = natWord N ++ natWord l.length ++ l.flatMap PCPPRequestNodeSchema.native ++ natWord o := by
  subst hl; rw [PCPPNative.descriptor_eq, ho]

theorem checkedRaw_bytes (E : LinearCodeFamily) (D : Circuit) :
    (checkedRaw E D).1.flatMap PCPPRequestNodeSchema.native = D.D.nodes.flatMap PCPPRequestNodeSchema.native ++
      (checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).1.flatMap
        PCPPRequestNodeSchema.native := by
  simp only [checkedRaw, List.flatMap_append, List.flatMap_map]
  have hf : (fun nd : BooleanNode D.n => PCPPRequestNodeSchema.native (liftNode (L := E.length D.n) nd)) =
      (PCPPRequestNodeSchema.native : BooleanNode D.n → List Bool) := funext native_liftNode
  rw [hf]

theorem checkedRaw_length (E : LinearCodeFamily) (D : Circuit) :
    (checkedRaw E D).1.length = D.D.nodes.length +
      (checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).1.length := by
  simp [checkedRaw]

/-- **The checked circuit's native descriptor**, with the check nodes from index `m = |D|`. -/
theorem checkedDesc_eq (E : LinearCodeFamily) (D : Circuit) :
    PCPPNative.descriptor (checkedCircuit E D).D =
      natWord (D.n + E.length D.n) ++
      natWord (D.D.nodes.length +
        (checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).1.length) ++
      D.D.nodes.flatMap PCPPRequestNodeSchema.native ++
      (checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).1.flatMap
        PCPPRequestNodeSchema.native ++
      natWord (checksNodes E D.n D.D.nodes.length (List.finRange (E.length D.n)) D.D.output.val).2 := by
  rw [descriptor_of (checkedCircuit E D).D (checkedRaw E D).1 (checkedRaw E D).2 (checkedCircuit_pad E D)
    (checkedCircuit_nodes E D).2]
  calc _ = natWord (D.n + E.length D.n) ++ natWord (checkedRaw E D).1.length ++
        (checkedRaw E D).1.flatMap PCPPRequestNodeSchema.native ++ natWord (checkedRaw E D).2 := rfl
    _ = _ := by rw [checkedRaw_bytes, checkedRaw_length]; simp only [List.append_assoc]; rfl

end NearCubicGates.Close.CheckedPCPP
