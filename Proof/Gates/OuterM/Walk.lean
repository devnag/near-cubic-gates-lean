import Proof.Gates.Succinct.Field
import Proof.Gates.OuterM.Spec

set_option autoImplicit false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicGates.Close.Succinct

theorem readTapeBit_lt {d : List Bool} {pos : ℕ} (h : readTapeBit d pos = true) : pos < d.length := by
  unfold readTapeBit at h
  by_contra hc
  rw [List.getD_eq_default _ _ (by omega)] at h
  exact Bool.false_ne_true h

set_option linter.unusedVariables false in
/-- The end of the field walk from `pos`. -/
def walkEnd (d : List Bool) (pos : ℕ) : ℕ :=
  if h : readTapeBit d pos = true then walkEnd d (fieldEnd d pos) else pos
termination_by d.length + 1 - pos
decreasing_by
  have := readTapeBit_lt h
  unfold fieldEnd
  omega

theorem walkEnd_true {d : List Bool} {pos : ℕ} (h : readTapeBit d pos = true) :
    walkEnd d pos = walkEnd d (fieldEnd d pos) := by
  rw [walkEnd, dif_pos h]

theorem walkEnd_false {d : List Bool} {pos : ℕ} (h : readTapeBit d pos = false) : walkEnd d pos = pos := by
  rw [walkEnd, dif_neg (by simp [h])]

theorem le_walkEnd (d : List Bool) (pos : ℕ) : pos ≤ walkEnd d pos := by
  induction pos using walkEnd.induct d with
  | case1 pos h ih =>
    rw [walkEnd_true h]
    have := le_fieldEnd d pos
    omega
  | case2 pos h =>
    rw [walkEnd_false (by simpa using h)]

/-- The walk never passes `2|d| + 1`. -/
theorem walkEnd_le (d : List Bool) (pos : ℕ) : walkEnd d pos ≤ max pos (2 * d.length + 1) := by
  induction pos using walkEnd.induct d with
  | case1 pos h ih =>
    rw [walkEnd_true h]
    have hl := readTapeBit_lt h
    have := ones_le_drop d pos
    unfold fieldEnd at ih ⊢
    omega
  | case2 pos h =>
    rw [walkEnd_false (by simpa using h)]
    omega

theorem onesL_eq_of : ∀ (n : ℕ) (l : List Bool), (∀ k < n, l.getD k false = true) → l.getD n false = false →
    onesL l = n
  | 0, [], _, _ => rfl
  | 0, b :: l, _, h => by simp at h; subst h; rfl
  | n + 1, [], ht, _ => by have := ht 0 (by omega); simp at this
  | n + 1, b :: l, ht, hf => by
    have hb : b = true := by simpa using ht 0 (by omega)
    subst hb
    simp only [onesL]
    rw [onesL_eq_of n l (fun k hk => by simpa using ht (k + 1) (by omega)) (by simpa using hf)]

theorem ones_eq_of (d : List Bool) (pos n : ℕ) (ht : ∀ k < n, readTapeBit d (pos + k) = true)
    (hf : readTapeBit d (pos + n) = false) : ones d pos = n := by
  unfold ones
  apply onesL_eq_of
  · intro k hk; rw [← read_drop]; exact ht k hk
  · rw [← read_drop]; exact hf

/-- The number of `1`s at `pos` depends only on the cells up to the first `0`. -/
theorem ones_congr (d1 d2 : List Bool) (pos : ℕ)
    (h : ∀ i, pos ≤ i → i ≤ pos + ones d1 pos → readTapeBit d1 i = readTapeBit d2 i) : ones d2 pos = ones d1 pos := by
  apply ones_eq_of
  · intro k hk
    rw [← h (pos + k) (by omega) (by omega)]
    exact ones_true d1 pos k hk
  · rw [← h (pos + ones d1 pos) (by omega) le_rfl]
    exact ones_false d1 pos

/-- **The walk reads only cells at or before its end.** -/
theorem walkEnd_congr (d1 d2 : List Bool) (pos : ℕ)
    (h : ∀ i, pos ≤ i → i ≤ walkEnd d1 pos → readTapeBit d1 i = readTapeBit d2 i) :
    walkEnd d2 pos = walkEnd d1 pos := by
  induction pos using walkEnd.induct d1 with
  | case1 pos h1 ih =>
    have he := walkEnd_true h1
    have hle := le_walkEnd d1 (fieldEnd d1 pos)
    have hfe : fieldEnd d1 pos = pos + 2 * ones d1 pos + 1 := rfl
    have h2 : readTapeBit d2 pos = true := by rw [← h pos le_rfl (by have := le_walkEnd d1 pos; omega)]; exact h1
    have ho := ones_congr d1 d2 pos (fun i hi1 hi2 => h i hi1 (by rw [he]; omega))
    have hfe2 : fieldEnd d2 pos = fieldEnd d1 pos := by unfold fieldEnd; rw [ho]
    rw [walkEnd_true h2, hfe2, he]
    exact ih (fun i hi1 hi2 => h i (by unfold fieldEnd at hi1; omega) (by rw [he]; exact hi2))
  | case2 pos h1 =>
    have h1' : readTapeBit d1 pos = false := by simpa using h1
    have h2 : readTapeBit d2 pos = false := by rw [← h pos le_rfl (by rw [walkEnd_false h1'])]; exact h1'
    rw [walkEnd_false h1', walkEnd_false h2]

/-! ## A genuine description -/

/-- The walk over a sequence of fields ends at its length. -/
theorem walkEnd_fields : ∀ (vs : List ℕ) (pre : List Bool),
    walkEnd (pre ++ vs.flatMap natWord) pre.length = pre.length + (vs.flatMap natWord).length
  | [], pre => by
    simp only [List.flatMap_nil, List.append_nil, List.length_nil, Nat.add_zero]
    apply walkEnd_false
    unfold readTapeBit
    exact List.getD_eq_default _ _ le_rfl
  | v :: vs, pre => by
    have hd : pre ++ (v :: vs).flatMap natWord = pre ++ natWord v ++ vs.flatMap natWord := by
      simp [List.flatMap_cons, List.append_assoc]
    have hb : readTapeBit (pre ++ natWord v ++ vs.flatMap natWord) pre.length = true := by
      unfold readTapeBit
      rw [List.append_assoc, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
        List.getD_append _ _ _ _ (by rw [natWord_length]; omega)]
      exact natWord_getD_one v 0 (by unfold natBitLength; omega)
    rw [hd, walkEnd_true hb, fieldEnd_natWord]
    have ih := walkEnd_fields vs (pre ++ natWord v)
    simp only [List.length_append] at ih ⊢
    rw [ih, List.flatMap_cons, List.length_append]
    ring

/-- The fields of the native descriptor. -/
def descVals {m : ℕ} (B : BooleanCircuit m) : List ℕ :=
  [m, B.nodes.length] ++ B.nodes.flatMap (fun nd => [PCPPRequestNodeSchema.fields nd 0,
    PCPPRequestNodeSchema.fields nd 1, PCPPRequestNodeSchema.fields nd 2]) ++ [B.output.val]

theorem descriptor_fields {m : ℕ} (B : BooleanCircuit m) :
    PCPPNative.descriptor B = (descVals B).flatMap natWord := by
  have hn : (PCPPRequestNodeSchema.native : BooleanNode m → List Bool) = fun nd =>
      natWord (PCPPRequestNodeSchema.fields nd 0) ++ (natWord (PCPPRequestNodeSchema.fields nd 1) ++
        natWord (PCPPRequestNodeSchema.fields nd 2)) := by
    funext nd; simp [PCPPRequestNodeSchema.native, List.append_assoc]
  rw [PCPPNative.descriptor_eq, hn]
  simp only [descVals, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.flatMap_assoc, List.append_assoc]

theorem walkEnd_descriptor {m : ℕ} (B : BooleanCircuit m) :
    walkEnd (PCPPNative.descriptor B) 0 = (PCPPNative.descriptor B).length := by
  have := walkEnd_fields (descVals B) []
  simpa [← descriptor_fields] using this

/-! ## The copy of the first cells -/

/-- The first `n` cells of a stream (blank cells read `false`). -/
def cellsOf (d : List Bool) (n : ℕ) : List Bool := List.ofFn fun i : Fin n => readTapeBit d i.val

theorem read_cellsOf (d : List Bool) (n i : ℕ) : readTapeBit (cellsOf d n) i = if i < n then readTapeBit d i else false := by
  unfold readTapeBit cellsOf
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp [readTapeBit, List.getD_eq_getElem?_getD]
  · exact List.getD_eq_default _ _ (by simpa using h)

/-- **The guard** (`sec:gadget-machine`: the source circuit's "description … has at most `L_ν` bits"): the walk
over the first `L + 1` cells of a
genuine description ends within `L` iff the description has at most `L` bits. -/
theorem fits_iff {m : ℕ} (B : BooleanCircuit m) (L : ℕ) :
    walkEnd (cellsOf (PCPPNative.descriptor B) (L + 1)) 0 ≤ L ↔ (PCPPNative.descriptor B).length ≤ L := by
  set d := PCPPNative.descriptor B with hd
  have hw := walkEnd_descriptor B
  rw [← hd] at hw
  constructor
  · intro hle
    have := walkEnd_congr (cellsOf d (L + 1)) d 0 (fun i _ hi => by rw [read_cellsOf, if_pos (by omega)])
    omega
  · intro hle
    have := walkEnd_congr d (cellsOf d (L + 1)) 0 (fun i _ _ => by
      rw [read_cellsOf]
      split_ifs with h
      · rfl
      · unfold readTapeBit; exact List.getD_eq_default _ _ (by omega))
    omega

/-- `⟨B⟩_ν` is the first `L_ν` cells of the description. -/
theorem ofFn_srcBits_cells (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) :
    List.ofFn (Outer.srcBits G ν B) = cellsOf (PCPPNative.descriptor B) (Outer.instLength G ν) := by
  unfold cellsOf Outer.srcBits Outer.srcWord Outer.srcDescriptor
  congr 1
  funext i
  unfold readTapeBit
  by_cases h : i.val < (PCPPNative.descriptor B).length
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default (PCPPNative.descriptor B) _ (by omega)]
    simp

end NearCubicGates.Close.OuterM
