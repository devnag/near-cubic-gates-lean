import Proof.Gates.CheckedPCPP.SubstitutedPoly
import Proof.Gates.CheckedPCPP.ChecksW
import Proof.Gates.CheckedPCPP.PolyClass
import Proof.Gates.CheckedPCPP.Composite
import Proof.Gates.Outer.Size

/-!
# Length bounds for the Case 2 producer's words ((a′) form)

The producer's cost (`sec:all-lengths`: "computable in polynomial time once the pair is known") is charged on the
lengths of its input words. Two of them are new with the repair:
* the word of `C_{⟨B_src⟩_ν}` (`OracleOutput.word`, imp:short-pcp): `word_len_le` bounds it by the size of `C` and its
  arity `ℓ`; `mwWord_poly`: at the instance `⟨B_src⟩_ν` it is at most a fixed polynomial in `2^ν` (the import's size
  clause `|C| ≤ K (L_ν + |bin T_G(L_ν)| + 1)^e`, `Outer.outC_size_le`, and `ℓ ≤ q(N_ν)`, `Outer.ell_le_width`, F-c7);
* the native descriptor of a Boolean circuit (`desc_len_le'`, quadratic in its size and arity; the same bound as the
  composite's `Comp.desc_len_le`, restated here so that the producer does not depend on the composite's internals).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.MW20 NearCubicGates.Close NearCubicGates.Close.CheckedPCPP

/-! ## The word of an oracle circuit -/

theorem natWord_le (x M : ℕ) (h : x ≤ M) : (natWord x).length ≤ 2 * M + 3 :=
  (SubstitutedPoly.natWord_len_le x).trans (by omega)

theorem flatMap_len_le {α β : Type} (f : α → List β) (K : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).length ≤ K) → (l.flatMap f).length ≤ l.length * K
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := flatMap_len_le f K l (fun b hb => h b (List.mem_cons_of_mem a hb))
    nlinarith

/-- The word of a well-formed node at index `idx` has at most `ℓ + 3` numbers, each at most `idx + n + 5`. -/
theorem oracleNodeWord_len_le {n a : ℕ} (nd : OracleNode n a) (idx M : ℕ) (h : nd.WellFormedAt idx)
    (hM : idx + n + 5 ≤ M) : (oracleNodeWord nd).length ≤ (a + 3) * (2 * M + 3) := by
  have hA : 3 * (2 * M + 3) ≤ (a + 3) * (2 * M + 3) := Nat.mul_le_mul_right _ (by omega)
  cases nd with
  | const v =>
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 0 M (by omega)
    have := natWord_le v.toNat M (by have := Bool.toNat_le v; omega)
    omega
  | input i =>
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 1 M (by omega)
    have := natWord_le i.val M (by have := i.isLt; omega)
    have := natWord_le 0 M (by omega)
    omega
  | not c =>
    simp only [OracleNode.WellFormedAt] at h
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 2 M (by omega)
    have := natWord_le c M (by omega)
    have := natWord_le 0 M (by omega)
    omega
  | and l r =>
    simp only [OracleNode.WellFormedAt] at h
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 3 M (by omega)
    have := natWord_le l M (by omega)
    have := natWord_le r M (by omega)
    omega
  | or l r =>
    simp only [OracleNode.WellFormedAt] at h
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 4 M (by omega)
    have := natWord_le l M (by omega)
    have := natWord_le r M (by omega)
    omega
  | oracle args =>
    simp only [OracleNode.WellFormedAt] at h
    simp only [oracleNodeWord, List.length_append]
    have h5 := natWord_le 5 M (by omega)
    have hf : ((List.ofFn fun j => natWord (args j)).flatten).length ≤ a * (2 * M + 3) := by
      rw [List.length_flatten]
      have := List.sum_le_card_nsmul ((List.ofFn fun j => natWord (args j)).map List.length) (2 * M + 3) (by
        intro x hx
        simp only [List.mem_map, List.mem_ofFn] at hx
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hx
        exact natWord_le _ M (by have := h j; omega))
      simpa using this
    nlinarith

/-- **The word of an oracle circuit** has length at most `(S + 3)(ℓ + 3)(2(S + ℓ + 5) + 3)` (`S` its size). -/
theorem word_len_le (o : OracleOutput) :
    o.word.length ≤ (o.circuit.size + 3) * ((o.ell + 3) * (2 * (o.circuit.size + o.ell + 5) + 3)) := by
  set S := o.circuit.size with hS
  set M := S + o.ell + 5 with hM
  have hn : ∀ nd ∈ o.circuit.nodes, (oracleNodeWord nd).length ≤ (o.ell + 3) * (2 * M + 3) := by
    intro nd hnd
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.1 hnd
    have hw := o.circuit.wellFormed idx
    rw [hidx] at hw
    have : idx.val < S := idx.isLt
    exact oracleNodeWord_len_le nd idx.val M hw (by omega)
  have hb := flatMap_len_le oracleNodeWord _ o.circuit.nodes hn
  have h1 := natWord_le o.ell M (by omega)
  have h2 := natWord_le o.circuit.nodes.length M (by change S ≤ M; omega)
  have h3 := natWord_le o.circuit.output.val M (by have := o.circuit.output.isLt; change _ < S at this; omega)
  have hl : o.circuit.nodes.length = S := rfl
  unfold OracleOutput.word
  simp only [List.length_append]
  rw [hl] at hb
  have hA : 2 * M + 3 ≤ (o.ell + 3) * (2 * M + 3) := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith

/-! ## The native descriptor of a Boolean circuit -/

theorem fields_le_of_wf' {n : ℕ} (nd : BooleanNode n) (idx : ℕ) (h : nd.WellFormedAt idx) (j : Fin 3) :
    PCPPRequestNodeSchema.fields nd j ≤ idx + n + 4 := by
  cases nd with
  | const b =>
    have := Bool.toNat_le b
    fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | input i => fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | not c => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | and l r => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | or l r => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)

/-- The native descriptor of a circuit is at most quadratic in its size and arity. -/
theorem desc_len_le' {n : ℕ} (c : BooleanCircuit n) :
    (PCPPNative.descriptor c).length ≤ (c.size + 1) * (6 * (c.size + n + 4) + 9) + 2 * n + 4 * c.size + 9 := by
  rw [PCPPNative.descriptor_eq]
  have hf : ∀ nd ∈ c.nodes, ∀ j, PCPPRequestNodeSchema.fields nd j ≤ c.size + n + 4 := by
    intro nd hnd j
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.1 hnd
    have hw := c.wellFormed idx
    rw [hidx] at hw
    have := fields_le_of_wf' nd idx.val hw j
    have : idx.val < c.size := idx.isLt
    omega
  have hb := ChecksW.flatMap_native_le (c.size + n + 4) c.nodes hf
  have h1 := SubstitutedPoly.natWord_len_le n
  have h2 := SubstitutedPoly.natWord_len_le c.nodes.length
  have h3 := SubstitutedPoly.natWord_len_le c.output.val
  have ho := c.output.isLt
  have hs : c.size = c.nodes.length := rfl
  simp only [List.length_append]
  change c.output.val < c.size at ho
  nlinarith

/-! ## The word of `C_{⟨B_src⟩_ν}` is polynomial in `2^ν` -/

/-- **The MW word is polynomial in the source length** (`sec:gadget-machine` with `imp:short-pcp`:
`|C| = poly(L_ν, log T_G(L_ν))` and
`ℓ ≤ q(N_ν)`): past the onset of `𝒱_G`, `|mwWord| ≤ C·(2^ν + 1)^e` for every source circuit. -/
theorem mwWord_poly (s : GateSources) (g : Transfer.GateParams) :
    ∃ C e : ℕ, ∀ (ν : ℕ) (B : BooleanCircuit (Outer.width s.mw (g.sv s) (2 ^ ν))), 1 ≤ ν →
      (g.sv s).onset ≤ ν → (mwWord s g (2 ^ ν) B).length ≤ C * (2 ^ ν + 1) ^ e := by
  set SV := g.sv s
  set K := (Outer.alg s.mw SV).coefficient
  set se := (Outer.alg s.mw SV).sizeExp
  obtain ⟨M0, hT⟩ := Outer.natBitLength_T_le SV
  obtain ⟨Cw, mw, hW⟩ := Outer.widthOf_pow g.k (Outer.apad s.mw SV)
  -- the size `S` and the arity `ℓ` as polynomials of `y = 2^ν`
  have hS : PolyB (fun ν : ℕ => 2 ^ ν) (fun ν => K * (Outer.instLength g.lenExp ν +
      natBitLength (SV.T (Outer.instLength g.lenExp ν)) + 1) ^ se) := by
    refine (PolyB.mul (PolyB.const K) (PolyB.pow (PolyB.add (PolyB.add (PolyB.pow PolyB.size (g.lenExp + 2))
      (PolyB.add (PolyB.const M0) (PolyB.mul (PolyB.const (g.k + 2)) PolyB.size))) (PolyB.const 1)) se)).mono
      fun ν => ?_
    have h1 : Outer.instLength g.lenExp ν ≤ (2 ^ ν) ^ (g.lenExp + 2) :=
      Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    have h2 := hT ν
    have h3 : (g.k + 2) * ν ≤ (g.k + 2) * 2 ^ ν := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hq : PolyB (fun ν : ℕ => 2 ^ ν) (fun ν => Outer.width s.mw SV (2 ^ ν)) :=
    ⟨Cw, mw, fun ν => (Nat.lt_two_pow_self.le).trans (hW (2 ^ ν))⟩
  obtain ⟨C, e, hCe⟩ := PolyB.mul (PolyB.add hS (PolyB.const 3)) (PolyB.mul (PolyB.add hq (PolyB.const 3))
    (PolyB.add (PolyB.mul (PolyB.const 2) (PolyB.add (PolyB.add hS hq) (PolyB.const 5))) (PolyB.const 3)))
  refine ⟨C, e, fun ν B hν hon => ?_⟩
  have hlog : Nat.log 2 (2 ^ ν) = ν := Nat.log_pow (by norm_num) ν
  have hw : mwWord s g (2 ^ ν) B = (Outer.outC s.mw SV ν B).word := by
    unfold mwWord; rw [hlog]
  rw [hw]
  have hsz := Outer.outC_size_le s.mw SV ν hν B
  have hel := Outer.ell_le_width s.mw SV ν B hon hν
  have hwl := word_len_le (Outer.outC s.mw SV ν B)
  have hC := hCe ν
  simp only at hC
  refine hwl.trans (le_trans ?_ hC)
  set S := (Outer.outC s.mw SV ν B).circuit.size
  set l := (Outer.outC s.mw SV ν B).ell
  set S' := K * (Outer.instLength g.lenExp ν + natBitLength (SV.T (Outer.instLength g.lenExp ν)) + 1) ^ se
  set q := Outer.width s.mw SV (2 ^ ν)
  have a1 : S + 3 ≤ S' + 3 := by omega
  have a2 : l + 3 ≤ q + 3 := by omega
  have a3 : 2 * (S + l + 5) + 3 ≤ 2 * (S' + q + 5) + 3 := by omega
  exact Nat.mul_le_mul a1 (Nat.mul_le_mul a2 a3)
end NearCubicGates.Close.Recovery.HT
