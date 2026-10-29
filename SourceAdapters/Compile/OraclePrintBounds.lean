import NineInputs
import Proof.Gates.Recovery.HTWord

/-!
# The native word of an oracle circuit is cubic in its arity and size

proof of `thm:short-pcp-ours`, Step 4: "This gives an oracle circuit of size \(\poly(n,\log T)\) [...] The algorithm \(A\) computes
[...] \(C^O_x\) in \(\poly(n,\log T)\) time". Writing the circuit is part of that time, so the length of the
precise native output word `OracleOutput.word` (`Statement.lean:1500`) must be polynomial in the circuit size and
the arity `ℓ`; (`cor:short-pcp-clock`) charges the same construction with the clock supplied as input.
This module gives the explicit bound `|OracleOutput.word ⟨ℓ, C⟩| ≤ 64·(ℓ + |C| + 1)^3` for every well-formed
oracle circuit, and its measure form for the join `ComputationToCircuit` (conjunct "writing the precise
native output word is charged").

The per-node word bound uses the sharper index bound idx < S to obtain the constant 64.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Recovery

set_option autoImplicit false

/-- Every node word of a well-formed circuit is at most `(ℓ + 3)·(2(ℓ + S + 4) + 3)` bits (`S` its size):
each node has at most `ℓ + 1` fields (tag plus three-field form, or tag plus `ℓ` argument wires), and every field
value is a tag `≤ 5`, an input index `< ℓ`, a Boolean, or an earlier node index `< S`. -/
theorem nodeWord_length_le {ell : ℕ} (C : OracleCircuit ell ell) :
    ∀ nd ∈ C.nodes, (oracleNodeWord nd).length ≤ (ell + 3) * (2 * (ell + C.size + 4) + 3) := by
  intro nd hnd
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.1 hnd
  have hw := C.wellFormed idx
  rw [hidx] at hw
  have hlt : idx.val < C.size := idx.isLt
  exact HT.oracleNodeWord_len_le nd idx.val (ell + C.size + 4) hw (by omega)

/-- **The native output word of an oracle circuit** (proof of `thm:short-pcp-ours`): at most `64·(ℓ + |C| + 1)^3` bits. -/
theorem word_length_le {ell : ℕ} (C : OracleCircuit ell ell) :
    (OracleOutput.word ⟨ell, C⟩).length ≤ 64 * (ell + C.size + 1) ^ 3 := by
  have hb := HT.flatMap_len_le oracleNodeWord _ C.nodes (nodeWord_length_le C)
  have hl : C.size = C.nodes.length := rfl
  rw [hl] at hb ⊢
  have ho : C.output.val < C.nodes.length := C.output.isLt
  have h1 := HT.natWord_le ell (ell + C.nodes.length + 1) (by omega)
  have h2 := HT.natWord_le C.nodes.length (ell + C.nodes.length + 1) (by omega)
  have h3 := HT.natWord_le C.output.val (ell + C.nodes.length + 1) (by omega)
  -- `S·(ℓ+3)·(2(ℓ+S+4)+3) ≤ X·(3X)·(13X)` and the three numbers `≤ 3(2X+3) ≤ 15X ≤ 15X^3`.
  have hA : C.nodes.length * ((ell + 3) * (2 * (ell + C.nodes.length + 4) + 3)) ≤
      (ell + C.nodes.length + 1) * ((3 * (ell + C.nodes.length + 1)) * (13 * (ell + C.nodes.length + 1))) := by
    apply Nat.mul_le_mul (by omega)
    exact Nat.mul_le_mul (by omega) (by omega)
  have hX3 : ell + C.nodes.length + 1 ≤ (ell + C.nodes.length + 1) ^ 3 := by
    calc ell + C.nodes.length + 1 = (ell + C.nodes.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ (ell + C.nodes.length + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hcube : (ell + C.nodes.length + 1) * ((3 * (ell + C.nodes.length + 1)) *
      (13 * (ell + C.nodes.length + 1))) = 39 * (ell + C.nodes.length + 1) ^ 3 := by ring
  unfold OracleOutput.word
  simp only [List.length_append]
  omega

/-- The measure form used by the join: if `ℓ ≤ m`, `|C| ≤ K·m^d` and `1 ≤ m`, the native output word has
at most `64·(K + 2)^3·m^(3d + 3)` bits. -/
theorem word_length_le_measure {ell : ℕ} (C : OracleCircuit ell ell) (m K d : ℕ) (hm : 1 ≤ m)
    (hell : ell ≤ m) (hsize : C.size ≤ K * m ^ d) :
    (OracleOutput.word ⟨ell, C⟩).length ≤ 64 * (K + 2) ^ 3 * m ^ (3 * d + 3) := by
  have hmd : 1 ≤ m ^ d := Nat.one_le_pow _ _ hm
  have hm1 : m ≤ m ^ (d + 1) := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ (d + 1) := Nat.pow_le_pow_right hm (by omega)
  have hmd1 : m ^ d ≤ m ^ (d + 1) := Nat.pow_le_pow_right hm (by omega)
  have h1 : 1 ≤ m ^ (d + 1) := Nat.one_le_pow _ _ hm
  have hsum : ell + C.size + 1 ≤ (K + 2) * m ^ (d + 1) := by
    have : K * m ^ d ≤ K * m ^ (d + 1) := Nat.mul_le_mul_left _ hmd1
    nlinarith
  have hcube : (ell + C.size + 1) ^ 3 ≤ ((K + 2) * m ^ (d + 1)) ^ 3 := Nat.pow_le_pow_left hsum 3
  have he : ((K + 2) * m ^ (d + 1)) ^ 3 = (K + 2) ^ 3 * m ^ (3 * d + 3) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  calc (OracleOutput.word ⟨ell, C⟩).length ≤ 64 * (ell + C.size + 1) ^ 3 := word_length_le C
    _ ≤ 64 * ((K + 2) ^ 3 * m ^ (3 * d + 3)) := by rw [← he]; exact Nat.mul_le_mul_left _ hcube
    _ = 64 * (K + 2) ^ 3 * m ^ (3 * d + 3) := by ring

end NearCubicGates.Adapters.Compile.OraclePrint
