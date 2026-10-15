import Proof.Gates.CounterMachine.CellTablesBody4
import Proof.Gates.CounterMachine.CellTablesWalk2

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

/-! ## Requests -/

theorem mem_vecs (q : ℕ) : ∀ (n : ℕ) (v : List ℕ), v.length = n → (∀ x ∈ v, x < q) → v ∈ vecs q n
  | 0, v, h, _ => by rw [List.eq_nil_of_length_eq_zero h]; simp [vecs]
  | n + 1, [], h, _ => by simp at h
  | n + 1, a :: v, h, hv => by
    simp only [vecs, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨a, hv a (by simp), v, mem_vecs q n v (by simpa using h) (fun x hx => hv x (by simp [hx])), rfl⟩

theorem digs_length (q t D : ℕ) : (digs q t D).length = D := by simp [digs]

theorem digs_lt (q t D : ℕ) (hq : 0 < q) : ∀ x ∈ digs q t D, x < q := by
  intro x hx; simp only [digs, List.mem_map] at hx; obtain ⟨i, _, rfl⟩ := hx; exact Nat.mod_lt _ hq

theorem resId_eq (c : Call) (p : Params) (part : Option Bool) (q t : ℕ) :
    resId c p part q t = .residue part q ((digs q t (dOf c p)).take (roleCount c.kind * p.J))
      ((digs q t (dOf c p)).drop (roleCount c.kind * p.J)) := by
  unfold resId; rw [digitsM_rep]; rfl

theorem resId_mem (c : Call) (p : Params) (part : Option Bool) (q t : ℕ) (hpart : part ∈ parts c)
    (hq : q ∈ p.primes) (hq0 : 0 < q) : resId c p part q t ∈ reqIds c p := by
  rw [resId_eq]
  have hD : dOf c p = roleCount c.kind * p.J + roleCount c.kind := by unfold dOf; ring
  unfold reqIds
  apply List.mem_append_left
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨part, hpart, q, (Finset.mem_sort _).mpr hq, _, mem_vecs q _ _ (by simp [digs_length, hD])
    (fun x hx => digs_lt q t _ hq0 x (List.mem_of_mem_take hx)), _, mem_vecs q _ _ (by simp [digs_length, hD])
    (fun x hx => digs_lt q t _ hq0 x (List.mem_of_mem_drop hx)), rfl⟩

/-- The key of a residue request is the Horner fold of its digits from `partCode·B₂ + q`. -/
theorem reqKey_res (c : Call) (p : Params) (part : Option Bool) (q t : ℕ) :
    reqKey c p (resId c p part q t) = hfold (2 ^ keyBits p) (partCode part * 2 ^ keyBits p + q) (digs q t (dOf c p)) := by
  rw [resId_eq]
  have hD : dOf c p = roleCount c.kind * p.J + roleCount c.kind := by unfold dOf; ring
  unfold reqKey radixKey
  simp only [keyFields]
  have hK : roleCount c.kind * (p.J + 1) = roleCount c.kind * p.J + roleCount c.kind := by ring
  have hl : ([0, partCode part, q] ++ (digs q t (dOf c p)).take (roleCount c.kind * p.J) ++
      (digs q t (dOf c p)).drop (roleCount c.kind * p.J)).length = keyLen c p := by
    simp [digs_length, keyLen, hD]; omega
  rw [hl, Nat.sub_self, List.replicate_zero, List.append_nil, List.append_assoc, List.take_append_drop]
  simp [hfold, List.foldl_append]

theorem descN_res (c : Call) (p : Params) (part : Option Bool) (q t : ℕ) :
    (descN (resId c p part q t)).flatMap natWord = natWord 0 ++ natWord (partCode part) ++ natWord q ++
      natWord (dOf c p) ++ (digs q t (dOf c p)).flatMap natWord := by
  rw [resId_eq]
  simp only [descN, List.take_append_drop, digs_length, List.flatMap_append, List.cons_append, List.singleton_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.append_assoc]

/-! ## The program -/

def resHead : St VV MM :=
  .seq (emV vZ) (.seq (emV lPC) (.seq (emV lQ) (.seq (emV kD) (.seq (.op (.copy bKey lPC))
  (.seq (.op (.mul bKey kB2 bTmp)) (.seq (.op (.copy bKey bTmp)) (.seq (.op (.add bKey lQ))
  (.op (.copy bPw lQD)))))))))

def resB : St VV MM := .seq resHead (.seq digL (tailB kVW2 lQE v1))

/-! ## Sizes -/

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem not_bodyVar {y : Fin VV} (h : bodyVarB y = false) : ¬ BodyVar y := by
  unfold bodyVarB at h; unfold BodyVar
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le] at h
  omega

theorem prime_mem_cellN (r : CellReq B1 B2 cT) {q : ℕ} (hq : q ∈ r.p.primes) : q ∈ cellN r.c r.p r.wt := by
  unfold cellN paramsN
  simp only [List.mem_append]
  left; right
  simp [(Finset.mem_sort _).mpr hq]

theorem srList_le_witN (c : Call) (p : Params) (wt : Wit c.n) : (srList c p).length ≤ (witN c p wt).length := by
  have hsp : witN c p wt = (coordsOf wt.I).length :: (coordsOf wt.I ++ (srList c p).flatMap (witSeg c wt)) := by
    simp only [witN, List.append_assoc, List.singleton_append, List.cons_append]; rfl
  have hS2 : (srList c p).length ≤ ((srList c p).flatMap (witSeg c wt)).length := by
    rw [List.length_flatMap]
    calc (srList c p).length = ((srList c p).map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum (by intro i _; simp [witSeg])
  rw [hsp, List.length_cons, List.length_append]; omega

theorem dOf_le (r : CellReq B1 B2 cT) : dOf r.c r.p ≤ 2 * (cellInput r).length + 2 := by
  have h1 := srList_le_witN r.c r.p r.wt
  have h2 : (srList r.c r.p).length = r.p.J * roleCount r.c.kind := by simp [srList, List.length_flatMap]
  have h3 : (witN r.c r.p r.wt).length ≤ (cellN r.c r.p r.wt).length := by unfold cellN; simp; omega
  have h4 := cellN_len_le r
  have h5 : roleCount r.c.kind ≤ 2 := by cases r.c.kind <;> decide
  have h6 : 1 ≤ roleCount r.c.kind := roleCount_pos _
  unfold dOf
  have : roleCount r.c.kind * (r.p.J + 1) = r.p.J * roleCount r.c.kind + roleCount r.c.kind := by ring
  have : r.p.J ≤ r.p.J * roleCount r.c.kind := Nat.le_mul_of_pos_right _ h6
  omega

theorem nbl_le_self (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 v
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
