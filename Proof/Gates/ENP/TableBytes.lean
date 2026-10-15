import Proof.Gates.ENP.TableSpecParts
import Proof.Wire_3_5.PrimAsmParseNat

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicGates.Close.ENP.TCirc

namespace TBytes

/-- The native bytes of a node. -/
local notation "nat" => RepairOrdinary.PCPPRequestNodeSchema.native

theorem flatMap_length_le {α β γ : Type} (l : List α) (f : α → List β) (g : α → List γ)
    (h : ∀ x ∈ l, (f x).length ≤ (g x).length) : (l.flatMap f).length ≤ (l.flatMap g).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

theorem nbl_pos (x : ℕ) : 1 ≤ natBitLength x := by unfold natBitLength; omega

theorem nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 x; omega

theorem nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength; have := Nat.log_mono_right (b := 2) h; omega

theorem natWord_mono {a b : ℕ} (h : a ≤ b) : (natWord a).length ≤ (natWord b).length := by
  rw [natWord_length, natWord_length]; have := nbl_mono h; omega

theorem natWord_zero : (natWord 0).length = 3 := by rw [natWord_length]; simp [natBitLength]

theorem natWord_five : (natWord 5).length = 7 := by
  rw [natWord_length]
  have : Nat.log 2 5 = 2 := by
    rw [Nat.log_eq_iff (by norm_num)]; norm_num
  simp [natBitLength, this]

theorem native_len {n : ℕ} (nd : BooleanNode n) :
    (nat nd).length = (natWord (RepairOrdinary.PCPPRequestNodeSchema.fields nd 0)).length +
      (natWord (RepairOrdinary.PCPPRequestNodeSchema.fields nd 1)).length +
      (natWord (RepairOrdinary.PCPPRequestNodeSchema.fields nd 2)).length := by
  simp only [RepairOrdinary.PCPPRequestNodeSchema.native, List.length_append]

theorem nine_le_native {n : ℕ} (nd : BooleanNode n) : 9 ≤ (nat nd).length := by
  have h := native_len nd
  have a0 := natWord_length (RepairOrdinary.PCPPRequestNodeSchema.fields nd 0)
  have a1 := natWord_length (RepairOrdinary.PCPPRequestNodeSchema.fields nd 1)
  have a2 := natWord_length (RepairOrdinary.PCPPRequestNodeSchema.fields nd 2)
  have := nbl_pos (RepairOrdinary.PCPPRequestNodeSchema.fields nd 0)
  have := nbl_pos (RepairOrdinary.PCPPRequestNodeSchema.fields nd 1)
  have := nbl_pos (RepairOrdinary.PCPPRequestNodeSchema.fields nd 2)
  omega

theorem flatMap_nine {n : ℕ} (l : List (BooleanNode n)) : 9 * l.length ≤ (l.flatMap nat).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := nine_le_native a
    omega

variable {ℓ : ℕ} (C : OracleCircuit ℓ ℓ)

theorem le_img (z c : ℕ) : c ≤ img C z c := by
  unfold img base
  have hk := Nat.mul_pos (Nat.two_pow_pos ℓ) (by omega : 0 < 2 * ℓ + 1)
  have : c ≤ c * K ℓ := Nat.le_mul_of_pos_right c hk
  omega

/-- A plain block's bytes contain its translation's bytes. -/
theorem plain_bytes (x : BooleanNode (T ℓ)) :
    (nat x).length ≤ ((List.replicate (K ℓ - 1) (BooleanNode.const false : BooleanNode (T ℓ)) ++ [x]).flatMap nat).length := by
  simp [List.flatMap_append]

/-- The first block of a flatMap over `range n`, `n ≥ 1`. -/
theorem range_first {β : Type} (n : ℕ) (hn : 1 ≤ n) (g : ℕ → List β) :
    (g 0).length ≤ ((List.range n).flatMap g).length := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.flatMap_cons, List.length_append]
  omega

theorem replicate_bytes (k : ℕ) :
    ((List.replicate k (BooleanNode.const false : BooleanNode (T ℓ))).flatMap nat).length = 9 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatMap_cons, List.length_append, ih, native_len]
    simp only [RepairOrdinary.PCPPRequestNodeSchema.fields]
    simp [natBitLength]
    ring

/-- The arguments of an oracle gate, indexed by `ℕ`. -/
def argsN (args : Fin ℓ → ℕ) (j : ℕ) : ℕ := if h : j < ℓ then args ⟨j, h⟩ else 0

theorem ofFn_args (args : Fin ℓ → ℕ) :
    ((List.ofFn fun j => natWord (args j)).flatten).length =
      ((List.range ℓ).flatMap fun j => natWord (argsN args j)).length := by
  have h1 : (List.ofFn fun j => natWord (args j)) = (List.finRange ℓ).map fun j => natWord (args j) := List.ofFn_eq_map
  have h2 : (List.range ℓ).flatMap (fun j => natWord (argsN args j)) =
      (List.finRange ℓ).flatMap (fun j => natWord (args j)) := by
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    congr 1
    funext j
    simp [argsN, j.isLt]
  rw [h1, h2]
  rfl

/-- **One node's word is covered by its block at seed `0`.** -/
theorem node_bytes (c : ℕ) (nd : OracleNode ℓ ℓ) :
    (oracleNodeWord nd).length ≤ ((block C 0 c nd).flatMap nat).length := by
  cases nd with
  | const b =>
    refine le_trans ?_ (plain_bytes (TCirc.translate C 0 (.const b)))
    exact le_of_eq rfl
  | input i =>
    show _ ≤ ((List.replicate (K ℓ - 1) (BooleanNode.const false : BooleanNode (T ℓ)) ++
      [TCirc.translate C 0 (.input i)]).flatMap nat).length
    rw [List.flatMap_append, List.length_append, replicate_bytes, List.flatMap_singleton]
    have h9 := nine_le_native (TCirc.translate C 0 (.input i))
    have hi : natBitLength i.val ≤ ℓ := by have := nbl_le i.val; have := i.isLt; omega
    have h1 : natBitLength 1 ≤ 2 := nbl_le 1
    have h0 : natBitLength 0 ≤ 1 := nbl_le 0
    have hK : 2 * ℓ + 1 ≤ K ℓ := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos ℓ)
    have hw : (oracleNodeWord (OracleNode.input i : OracleNode ℓ ℓ)).length =
        (natWord 1).length + (natWord i.val).length + (natWord 0).length := by
      simp only [oracleNodeWord, List.length_append]
    rw [hw, natWord_length, natWord_length, natWord_length]
    generalize K ℓ = k at *
    omega
  | not c' =>
    refine le_trans ?_ (plain_bytes (TCirc.translate C 0 (.not c')))
    show (natWord 2 ++ natWord c' ++ natWord 0).length ≤ (natWord 2 ++ natWord (img C 0 c') ++ natWord 0).length
    have := natWord_mono (le_img C 0 c')
    simp only [List.length_append]
    omega
  | and l r =>
    refine le_trans ?_ (plain_bytes (TCirc.translate C 0 (.and l r)))
    show (natWord 3 ++ natWord l ++ natWord r).length ≤
      (natWord 3 ++ natWord (img C 0 l) ++ natWord (img C 0 r)).length
    have := natWord_mono (le_img C 0 l)
    have := natWord_mono (le_img C 0 r)
    simp only [List.length_append]
    omega
  | or l r =>
    refine le_trans ?_ (plain_bytes (TCirc.translate C 0 (.or l r)))
    show (natWord 4 ++ natWord l ++ natWord r).length ≤
      (natWord 4 ++ natWord (img C 0 l) ++ natWord (img C 0 r)).length
    have := natWord_mono (le_img C 0 l)
    have := natWord_mono (le_img C 0 r)
    simp only [List.length_append]
    omega
  | oracle args =>
    show _ ≤ (((List.range (T ℓ)).flatMap (group C 0 c args)).flatMap nat).length
    rw [List.flatMap_assoc]
    refine le_trans ?_ (range_first (T ℓ) (Nat.two_pow_pos ℓ) (fun a => (group C 0 c args a).flatMap nat))
    -- group 0: one literal per argument, then the closing `or`
    show _ ≤ (((List.range ℓ).flatMap (fun j =>
      [lit ((0 : ℕ).testBit j) (img C 0 (argsN args j)),
        (BooleanNode.and (gIdx C 0 c 0 j) (gs C 0 c 0 + 2 * j) : BooleanNode (T ℓ))]) ++
      [(BooleanNode.or (oPrev C 0 c 0) (gIdx C 0 c 0 ℓ) : BooleanNode (T ℓ))]).flatMap nat).length
    rw [List.flatMap_append, List.length_append, List.flatMap_singleton, List.flatMap_assoc]
    have hw : (oracleNodeWord (OracleNode.oracle args : OracleNode ℓ ℓ)).length =
        (natWord 5).length + ((List.range ℓ).flatMap fun j => natWord (argsN args j)).length := by
      simp only [oracleNodeWord, List.length_append, ofFn_args]
    rw [hw, natWord_five]
    have hor := nine_le_native (BooleanNode.or (oPrev C 0 c 0) (gIdx C 0 c 0 ℓ) : BooleanNode (T ℓ))
    have hlits : ((List.range ℓ).flatMap fun j => natWord (argsN args j)).length ≤
        ((List.range ℓ).flatMap fun j =>
          [lit ((0 : ℕ).testBit j) (img C 0 (argsN args j)),
            (BooleanNode.and (gIdx C 0 c 0 j) (gs C 0 c 0 + 2 * j) : BooleanNode (T ℓ))].flatMap nat).length := by
      apply flatMap_length_le
      intro j _
      have hl : lit ((0 : ℕ).testBit j) (img C 0 (argsN args j)) =
          (BooleanNode.not (img C 0 (argsN args j)) : BooleanNode (T ℓ)) := by
        simp [lit, Nat.zero_testBit]
      rw [hl, List.flatMap_cons, List.length_append]
      show _ ≤ (natWord 2 ++ natWord (img C 0 (argsN args j)) ++ natWord 0).length + _
      have := natWord_mono (le_img C 0 (argsN args j))
      simp only [List.length_append]
      omega
    omega

/-- The nodes as their indices. -/
theorem nodes_range : C.nodes = (List.range C.nodes.length).map (fun c => C.nodes.getD c (.const false)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h1]

end TBytes

open TBytes in

theorem tBytesSpec : TBytesSpec := by
  intro ℓ C
  have hK : 1 ≤ K ℓ := Nat.mul_pos (Nat.two_pow_pos ℓ) (by omega)
  -- the word, part by part
  have hword : (OracleOutput.word ⟨ℓ, C⟩).length = (natWord ℓ).length + (natWord C.nodes.length).length +
      (C.nodes.flatMap oracleNodeWord).length + (natWord C.output.val).length := by
    simp only [OracleOutput.word, List.length_append]
  -- the start region covers `natWord ℓ`
  have hstart : 9 * (T ℓ + 2) ≤ ((start ℓ).flatMap RepairOrdinary.PCPPRequestNodeSchema.native).length := by
    have := flatMap_nine (start ℓ)
    have hl : (start ℓ).length = T ℓ + 2 := by
      simp only [start, List.length_append, List.length_ofFn, List.length_singleton]
      omega
    rw [hl] at this
    exact this
  have hl : (natWord ℓ).length ≤ 9 * (T ℓ + 2) := by
    rw [natWord_length]
    have h1 := nbl_le ℓ
    have h2 : ℓ < T ℓ := Nat.lt_two_pow_self
    omega
  -- seed 0: the node blocks, `not (img output)`, `and (base − 1) (base + m·K)`
  have hseed : ((seed C 0).flatMap RepairOrdinary.PCPPRequestNodeSchema.native).length =
      (((List.range C.nodes.length).flatMap (fun c => block C 0 c (C.nodes.getD c (.const false)))).flatMap
        RepairOrdinary.PCPPRequestNodeSchema.native).length +
      (RepairOrdinary.PCPPRequestNodeSchema.native (BooleanNode.not (img C 0 C.output.val) : BooleanNode (T ℓ))).length +
      (RepairOrdinary.PCPPRequestNodeSchema.native
        (BooleanNode.and (base C 0 - 1) (base C 0 + C.nodes.length * K ℓ) : BooleanNode (T ℓ))).length := by
    simp only [seed, List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega
  have hnodes : (C.nodes.flatMap oracleNodeWord).length ≤
      (((List.range C.nodes.length).flatMap (fun c => block C 0 c (C.nodes.getD c (.const false)))).flatMap
        RepairOrdinary.PCPPRequestNodeSchema.native).length := by
    conv_lhs => rw [nodes_range C]
    rw [List.flatMap_map, List.flatMap_assoc]
    apply flatMap_length_le
    intro c _
    exact node_bytes C c _
  have hout : (natWord C.output.val).length ≤
      (RepairOrdinary.PCPPRequestNodeSchema.native (BooleanNode.not (img C 0 C.output.val) : BooleanNode (T ℓ))).length := by
    show _ ≤ (natWord 2 ++ natWord (img C 0 C.output.val) ++ natWord 0).length
    have := natWord_mono (le_img C 0 C.output.val)
    simp only [List.length_append]
    omega
  have hmw : (natWord C.nodes.length).length ≤ (RepairOrdinary.PCPPRequestNodeSchema.native
      (BooleanNode.and (base C 0 - 1) (base C 0 + C.nodes.length * K ℓ) : BooleanNode (T ℓ))).length := by
    show _ ≤ (natWord 3 ++ natWord (base C 0 - 1) ++ natWord (base C 0 + C.nodes.length * K ℓ)).length
    have hle : C.nodes.length ≤ base C 0 + C.nodes.length * K ℓ := by
      have := Nat.le_mul_of_pos_right C.nodes.length hK
      omega
    have := natWord_mono hle
    simp only [List.length_append]
    omega
  rw [hword, hseed]
  omega

end NearCubicGates.Close.ENP
