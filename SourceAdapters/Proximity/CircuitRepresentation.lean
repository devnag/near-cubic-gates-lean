import NineInputs
import SourceAdapters.Proximity.Rational
import Proof.Foundations.OrdinaryMachine

/-!
Q01, `app:sources`, "Uniform three-query PCPP and code interfaces": the source uses the same mathematical topological circuit,
but a flat conventional word. This adapter preserves arity and evaluation and
proves a uniform quadratic upper bound on the source description length in
the target node count. Bit-time encoding/decoding remains Q04.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Published.CW19Proximity
open NearCubicGates.PublishedSources.PCPP

def sourceCircuit (C : Circuit) : SourceCircuit :=
  ⟨C.n, C.D, C.sizeAtLeast⟩

theorem sourceCircuit_eval (C : Circuit) (input : BitInput C.n) :
    (sourceCircuit C).circuit.eval input = C.D.eval input := rfl

theorem source_strict_far {delta : ℝ} {eta : ℚ} (hgap : (eta : ℝ) < delta)
    {C : Circuit} {input : BitInput C.n} (hfar : ProximityFar delta C input) :
    StrictlyFar eta (sourceCircuit C) input :=
  strict_far_of_far hgap hfar

theorem framed_nat_length_le {value bound : ℕ} (h : value ≤ bound) :
    (RepairOrdinary.frame value.bits).length ≤ 2 * bound + 1 := by
  rw [RepairOrdinary.frame_length, Nat.size_eq_bits_len]
  have : Nat.size value ≤ value := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

theorem sourceNode_length_le {n index bound : ℕ} (node : BooleanNode n)
    (hn : n ≤ bound) (hi : index ≤ bound) (hw : node.WellFormedAt index) :
    (sourceNodeWord node).length ≤ 5 * (bound + 1) := by
  cases node with
  | const b => simp [sourceNodeWord]; omega
  | input i =>
      have h := framed_nat_length_le (show i.val ≤ bound by omega)
      simp only [sourceNodeWord, List.length_append, List.length_cons, List.length_nil]
      omega
  | not child =>
      have hc : child ≤ bound := by simp only [BooleanNode.WellFormedAt] at hw; omega
      have h := framed_nat_length_le hc
      simp only [sourceNodeWord, List.length_append, List.length_cons, List.length_nil]
      omega
  | and left right =>
      have hl : left ≤ bound := by simp only [BooleanNode.WellFormedAt] at hw; omega
      have hr : right ≤ bound := by simp only [BooleanNode.WellFormedAt] at hw; omega
      have hleft := framed_nat_length_le hl
      have hright := framed_nat_length_le hr
      simp only [sourceNodeWord, List.length_append, List.length_cons, List.length_nil]
      omega
  | or left right =>
      have hl : left ≤ bound := by simp only [BooleanNode.WellFormedAt] at hw; omega
      have hr : right ≤ bound := by simp only [BooleanNode.WellFormedAt] at hw; omega
      have hleft := framed_nat_length_le hl
      have hright := framed_nat_length_le hr
      simp only [sourceNodeWord, List.length_append, List.length_cons, List.length_nil]
      omega

private theorem flatMap_length_le {α β : Type} (f : α → List β) (xs : List α)
    (bound : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ bound) :
    (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": every source description is polynomial in the circuit node count. -/
theorem source_word_length (C : SourceCircuit) :
    (sourceCircuitWord C).length ≤ 11 * (C.circuit.size + 1) ^ 2 := by
  have hn := framed_nat_length_le C.inputs_le_size
  have hm := framed_nat_length_le (Nat.le_refl C.circuit.nodes.length)
  have ho := framed_nat_length_le (Nat.le_of_lt C.circuit.output.isLt)
  have hnodes : ∀ node ∈ C.circuit.nodes,
      (sourceNodeWord node).length ≤ 5 * (C.circuit.size + 1) := by
    intro node hnode
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hnode
    exact sourceNode_length_le _ C.inputs_le_size (Nat.le_of_lt i.isLt) (C.circuit.wellFormed i)
  have hf := flatMap_length_le sourceNodeWord C.circuit.nodes _ hnodes
  simp only [sourceCircuitWord, List.length_append]
  change _ ≤ 11 * (C.circuit.nodes.length + 1) ^ 2
  dsimp only [BooleanCircuit.size] at hn hf
  nlinarith

theorem source_word_length_target (C : Circuit) :
    (sourceCircuitWord (sourceCircuit C)).length ≤ 11 * (C.m + 1) ^ 2 :=
  source_word_length (sourceCircuit C)

end NearCubicGates.Adapters.Proximity
