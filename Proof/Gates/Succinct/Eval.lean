import Proof.Gates.Succinct.Field
import Proof.PCP.PCPPNativeRequestSchema

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- The evaluator's state between nodes: the read position and the gate values so far. -/
structure EvSt where
  pos : ℕ
  vals : List Bool

/-- The value of one node read at `p0` (paper lem:succinct-verifier, stage (3)). -/
def nodeValue (d : List Bool) (lb lp : ℕ) (pt : ℕ → Bool) (vals : List Bool) (p0 : ℕ) : Bool :=
  let tag := fieldVal d p0 lb
  let p1 := fieldEnd d p0
  let a := fieldVal d p1 (if tag = 1 then lp else lb)
  let b := fieldVal d (fieldEnd d p1) lb
  if tag = 0 then decide (a ≠ 0)
  else if tag = 1 then decide (ones d p1 ≤ lp) && pt a
  else if tag = 2 then !(vals.getD a false)
  else if tag = 3 then vals.getD a false && vals.getD b false
  else vals.getD a false || vals.getD b false

/-- One node step: the position past the node's three fields, its value appended. -/
def nodeStep (d : List Bool) (lb lp : ℕ) (pt : ℕ → Bool) (st : EvSt) : EvSt :=
  ⟨fieldEnd d (fieldEnd d (fieldEnd d st.pos)), st.vals ++ [nodeValue d lb lp pt st.vals st.pos]⟩

/-- The state after the header: past the arity field and the node count. -/
def evStart (d : List Bool) : EvSt := ⟨fieldEnd d (fieldEnd d 0), []⟩

/-- The node count read from the header. -/
def evCount (d : List Bool) (lb : ℕ) : ℕ := fieldVal d (fieldEnd d 0) lb

/-- The state after all nodes. -/
def evFinal (d : List Bool) (lb lp : ℕ) (pt : ℕ → Bool) : EvSt :=
  (nodeStep d lb lp pt)^[evCount d lb] (evStart d)

/-- **The evaluator's model** (paper lem:succinct-verifier, stage (3)): total on every stream. -/
def evalModel (d : List Bool) (lb lp : ℕ) (pt : ℕ → Bool) : Bool :=
  (evFinal d lb lp pt).vals.getD (fieldVal d (evFinal d lb lp pt).pos lb) false

/-! ## Correctness on a circuit description -/

theorem natBitLength_le_of_lt {x lb : ℕ} (h : x < 2 ^ lb) (hlb : 1 ≤ lb) : natBitLength x ≤ lb := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) h
    omega

/-- A node whose fields fit the guard (the input index is guarded separately). -/
def NodeFits {m : ℕ} (lb : ℕ) (node : BooleanNode m) : Prop :=
  PCPPRequestNodeSchema.fields node 0 < 2 ^ lb ∧
    (PCPPRequestNodeSchema.tag node ≠ 1 → PCPPRequestNodeSchema.fields node 1 < 2 ^ lb) ∧
    PCPPRequestNodeSchema.fields node 2 < 2 ^ lb

/-- One node, read from its native fields. -/
theorem nodeStep_native {m : ℕ} (pre rest : List Bool) (lb lp : ℕ) (pt : ℕ → Bool) (hlb : 1 ≤ lb)
    (hpt : ∀ j, lp < natBitLength j → pt j = false) (node : BooleanNode m) (hfit : NodeFits lb node)
    (prior : Array Bool) :
    nodeStep (pre ++ PCPPRequestNodeSchema.native node ++ rest) lb lp pt ⟨pre.length, prior.toList⟩ =
      ⟨pre.length + (PCPPRequestNodeSchema.native node).length,
        (prior.push (node.eval (fun j => pt j.val) prior)).toList⟩ := by
  obtain ⟨hf0, hf1, hf2⟩ := hfit
  set f := PCPPRequestNodeSchema.fields node with hf
  have hnat : PCPPRequestNodeSchema.native node = natWord (f 0) ++ natWord (f 1) ++ natWord (f 2) := rfl
  set d := pre ++ PCPPRequestNodeSchema.native node ++ rest with hd
  -- the three fields
  have d0 : d = pre ++ natWord (f 0) ++ (natWord (f 1) ++ natWord (f 2) ++ rest) := by
    rw [hd, hnat]; simp only [List.append_assoc]
  have d1 : d = (pre ++ natWord (f 0)) ++ natWord (f 1) ++ (natWord (f 2) ++ rest) := by
    rw [hd, hnat]; simp only [List.append_assoc]
  have d2 : d = (pre ++ natWord (f 0) ++ natWord (f 1)) ++ natWord (f 2) ++ rest := by
    rw [hd, hnat]; simp only [List.append_assoc]
  have e0 : fieldEnd d pre.length = (pre ++ natWord (f 0)).length := by
    rw [d0, fieldEnd_natWord]; simp
  have e1 : fieldEnd d (pre ++ natWord (f 0)).length = (pre ++ natWord (f 0) ++ natWord (f 1)).length := by
    rw [d1, fieldEnd_natWord]; simp only [List.length_append]
  have e2 : fieldEnd d (pre ++ natWord (f 0) ++ natWord (f 1)).length =
      pre.length + (PCPPRequestNodeSchema.native node).length := by
    rw [d2, fieldEnd_natWord, hnat]; simp only [List.length_append]; omega
  have v0 : fieldVal d pre.length lb = f 0 := by
    rw [d0]; exact fieldVal_natWord _ _ _ _ (natBitLength_le_of_lt hf0 hlb)
  have v2 : fieldVal d (pre ++ natWord (f 0) ++ natWord (f 1)).length lb = f 2 := by
    rw [d2]; exact fieldVal_natWord _ _ _ _ (natBitLength_le_of_lt hf2 hlb)
  have o1 : ones d (pre ++ natWord (f 0)).length = natBitLength (f 1) := by rw [d1]; exact ones_natWord _ _ _
  have v1 : ∀ b, natBitLength (f 1) ≤ b → fieldVal d (pre ++ natWord (f 0)).length b = f 1 := by
    intro b hb; rw [d1]; exact fieldVal_natWord _ _ _ _ hb
  unfold nodeStep
  simp only []
  rw [e0, e1, e2]
  congr 1
  rw [Array.toList_push]
  congr 1
  simp only [nodeValue]
  rw [v0, e0, e1, v2, o1]
  generalize (pre ++ natWord (f 0)).length = p1 at v1 ⊢
  have htag := PCPPRequestNodeSchema.first_tag node
  rw [← hf] at htag
  cases node with
  | const b =>
    have h0 : f 0 = 0 := rfl
    rw [h0, if_neg (by decide : (0:ℕ) ≠ 1)]
    have h1 : f 1 = b.toNat := rfl
    rw [v1 lb (natBitLength_le_of_lt (hf1 (by simp [PCPPRequestNodeSchema.tag])) hlb), h1]
    cases b <;> simp [BooleanNode.eval]
  | input i =>
    have h0 : f 0 = 1 := rfl
    have h1 : f 1 = i.val := rfl
    rw [h0, if_pos rfl]
    simp only [if_pos rfl, one_ne_zero, if_false]
    by_cases hi : natBitLength i.val ≤ lp
    · rw [v1 lp (by rw [h1]; exact hi), h1]; simp [BooleanNode.eval, hi]
    · rw [h1]
      simp [hi, BooleanNode.eval, hpt i.val (by omega)]
  | not c =>
    have h0 : f 0 = 2 := rfl
    rw [h0, if_neg (by decide : (2:ℕ) ≠ 1)]
    have h1 : f 1 = c := rfl
    rw [v1 lb (natBitLength_le_of_lt (hf1 (by simp [PCPPRequestNodeSchema.tag])) hlb), h1]
    simp [BooleanNode.eval, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  | and l r =>
    have h0 : f 0 = 3 := rfl
    rw [h0, if_neg (by decide : (3:ℕ) ≠ 1)]
    have h1 : f 1 = l := rfl
    have h2 : f 2 = r := rfl
    rw [v1 lb (natBitLength_le_of_lt (hf1 (by simp [PCPPRequestNodeSchema.tag])) hlb), h1, h2]
    simp [BooleanNode.eval, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  | or l r =>
    have h0 : f 0 = 4 := rfl
    rw [h0, if_neg (by decide : (4:ℕ) ≠ 1)]
    have h1 : f 1 = l := rfl
    have h2 : f 2 = r := rfl
    rw [v1 lb (natBitLength_le_of_lt (hf1 (by simp [PCPPRequestNodeSchema.tag])) hlb), h1, h2]
    simp [BooleanNode.eval, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- All nodes, read from the native node stream. -/
theorem nodeSteps_native {m : ℕ} (lb lp : ℕ) (pt : ℕ → Bool) (hlb : 1 ≤ lb)
    (hpt : ∀ j, lp < natBitLength j → pt j = false) (rest : List Bool) :
    ∀ (nodes : List (BooleanNode m)) (pre : List Bool) (prior : Array Bool), (∀ x ∈ nodes, NodeFits lb x) →
      (nodeStep (pre ++ nodes.flatMap PCPPRequestNodeSchema.native ++ rest) lb lp pt)^[nodes.length]
          ⟨pre.length, prior.toList⟩ =
        ⟨pre.length + (nodes.flatMap PCPPRequestNodeSchema.native).length,
          (nodes.foldl (fun prior node => prior.push (node.eval (fun j => pt j.val) prior)) prior).toList⟩
  | [], pre, prior, _ => by simp
  | x :: xs, pre, prior, hfit => by
    have hx := hfit x (by simp)
    have e : pre ++ (x :: xs).flatMap PCPPRequestNodeSchema.native ++ rest =
        pre ++ PCPPRequestNodeSchema.native x ++ (xs.flatMap PCPPRequestNodeSchema.native ++ rest) := by
      simp [List.append_assoc]
    rw [List.length_cons, Function.iterate_succ_apply, e, nodeStep_native pre _ lb lp pt hlb hpt x hx prior]
    have e' : pre ++ PCPPRequestNodeSchema.native x ++ (xs.flatMap PCPPRequestNodeSchema.native ++ rest) =
        (pre ++ PCPPRequestNodeSchema.native x) ++ xs.flatMap PCPPRequestNodeSchema.native ++ rest := by
      simp [List.append_assoc]
    rw [e']
    have ih := nodeSteps_native lb lp pt hlb hpt rest xs (pre ++ PCPPRequestNodeSchema.native x)
      (prior.push (x.eval (fun j => pt j.val) prior)) (fun y hy => hfit y (by simp [hy]))
    rw [List.length_append] at ih
    rw [ih]
    simp [List.foldl_cons, Nat.add_assoc]

/-- The fields of a well-formed node at index `< s` fit the guard when `s + 5 ≤ 2^lb`. -/
theorem nodeFits_of_wf {m : ℕ} (lb s index : ℕ) (hs : s + 5 ≤ 2 ^ lb) (hi : index < s) (node : BooleanNode m)
    (hwf : node.WellFormedAt index) : NodeFits lb node := by
  have h5 : 5 ≤ 2 ^ lb := by omega
  cases node with
  | const b =>
    have := Bool.toNat_le b
    exact ⟨show 0 < 2 ^ lb by omega, fun _ => show b.toNat < 2 ^ lb by omega, show 0 < 2 ^ lb by omega⟩
  | input i => exact ⟨show 1 < 2 ^ lb by omega, fun h => absurd rfl h, show 0 < 2 ^ lb by omega⟩
  | not c =>
    change c < index at hwf
    exact ⟨show 2 < 2 ^ lb by omega, fun _ => show c < 2 ^ lb by omega, show 0 < 2 ^ lb by omega⟩
  | and l r =>
    obtain ⟨hl, hr⟩ := hwf
    exact ⟨show 3 < 2 ^ lb by omega, fun _ => show l < 2 ^ lb by omega, show r < 2 ^ lb by omega⟩
  | or l r =>
    obtain ⟨hl, hr⟩ := hwf
    exact ⟨show 4 < 2 ^ lb by omega, fun _ => show l < 2 ^ lb by omega, show r < 2 ^ lb by omega⟩

theorem evalModel_descriptor {m : ℕ} (c : BooleanCircuit m) (rest : List Bool) (lb lp : ℕ) (pt : ℕ → Bool)
    (hs : c.nodes.length + 5 ≤ 2 ^ lb) (hpt : ∀ j, lp < natBitLength j → pt j = false) :
    evalModel (PCPPNative.descriptor c ++ rest) lb lp pt = c.eval (fun j => pt j.val) := by
  have hlb : 1 ≤ lb := by
    rcases Nat.eq_zero_or_pos lb with h | h
    · subst h; simp at hs
    · exact h
  have hd := PCPPNative.descriptor_eq c
  set d := PCPPNative.descriptor c ++ rest with hdd
  have d0 : d = [] ++ natWord m ++ (natWord c.nodes.length ++ c.nodes.flatMap PCPPRequestNodeSchema.native ++
      natWord c.output.val ++ rest) := by rw [hdd, hd]; simp [List.append_assoc]
  have d1 : d = natWord m ++ natWord c.nodes.length ++ (c.nodes.flatMap PCPPRequestNodeSchema.native ++
      natWord c.output.val ++ rest) := by rw [hdd, hd]; simp [List.append_assoc]
  have e0 : fieldEnd d 0 = (natWord m).length := by
    have := fieldEnd_natWord [] (natWord c.nodes.length ++ c.nodes.flatMap PCPPRequestNodeSchema.native ++
      natWord c.output.val ++ rest) m
    rw [← d0] at this; simpa using this
  have hcount : evCount d lb = c.nodes.length := by
    unfold evCount; rw [e0, d1]
    exact fieldVal_natWord _ _ _ _ (natBitLength_le_of_lt (by omega) hlb)
  have hstart : evStart d = ⟨(natWord m ++ natWord c.nodes.length).length, (#[] : Array Bool).toList⟩ := by
    unfold evStart; rw [e0, d1, fieldEnd_natWord]; simp
  have d2 : d = (natWord m ++ natWord c.nodes.length) ++ c.nodes.flatMap PCPPRequestNodeSchema.native ++
      (natWord c.output.val ++ rest) := by rw [hdd, hd]; simp [List.append_assoc]
  have hfits : ∀ x ∈ c.nodes, NodeFits lb x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact nodeFits_of_wf lb c.nodes.length k (by omega) hk _ (c.wellFormed ⟨k, hk⟩)
  have hfinal : evFinal d lb lp pt = ⟨(natWord m ++ natWord c.nodes.length).length +
      (c.nodes.flatMap PCPPRequestNodeSchema.native).length, (c.values (fun j => pt j.val)).toList⟩ := by
    unfold evFinal
    rw [hcount, hstart, d2]
    exact nodeSteps_native lb lp pt hlb hpt _ c.nodes _ #[] hfits
  have d3 : d = ((natWord m ++ natWord c.nodes.length) ++ c.nodes.flatMap PCPPRequestNodeSchema.native) ++
      natWord c.output.val ++ rest := by rw [hdd, hd]
  unfold evalModel
  rw [hfinal]
  simp only []
  have hout : fieldVal d ((natWord m ++ natWord c.nodes.length).length +
      (c.nodes.flatMap PCPPRequestNodeSchema.native).length) lb = c.output.val := by
    rw [d3]
    have := fieldVal_natWord ((natWord m ++ natWord c.nodes.length) ++ c.nodes.flatMap PCPPRequestNodeSchema.native)
      rest c.output.val lb (natBitLength_le_of_lt (by have := c.output.isLt; omega) hlb)
    rw [List.length_append] at this
    exact this
  rw [hout]
  simp [BooleanCircuit.eval, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-! ## Description length -/

theorem natWord_length_ge (x : ℕ) : 3 ≤ (RepairRepresentation.natWord x).length := by
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]; unfold natBitLength; omega

theorem flatMap_native_length {m : ℕ} : ∀ (l : List (BooleanNode m)),
    9 * l.length ≤ (l.flatMap PCPPRequestNodeSchema.native).length
  | [] => by simp
  | x :: l => by
    have ih := flatMap_native_length l
    have h0 := natWord_length_ge (PCPPRequestNodeSchema.fields x 0)
    have h1 := natWord_length_ge (PCPPRequestNodeSchema.fields x 1)
    have h2 := natWord_length_ge (PCPPRequestNodeSchema.fields x 2)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, PCPPRequestNodeSchema.native]
    omega

theorem descriptor_length_ge {m : ℕ} (B : BooleanCircuit m) :
    B.nodes.length + 5 ≤ (PCPPNative.descriptor B).length := by
  rw [PCPPNative.descriptor_eq]
  have h1 := flatMap_native_length B.nodes
  have h2 := natWord_length_ge m
  have h3 := natWord_length_ge B.nodes.length
  have h4 := natWord_length_ge B.output.val
  simp only [List.length_append]
  omega

end NearCubicGates.Close.Succinct
