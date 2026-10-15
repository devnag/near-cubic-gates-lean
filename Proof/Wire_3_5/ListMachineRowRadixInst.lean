import Proof.Wire_3_5.ListMachineRowRadixSem
import Proof.Wire_3_5.ListMachineRowPopContract

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.WireExponent3_5.FinalPass

/-- A digit population: its occurrence count and its corner labels. -/
abbrev Dig := ℕ × List ℕ

/-- The digit population of digit `d`. -/
def digAt (digs : List Dig) (d : ℕ) : Dig := digs.getD d (0, [])

/-- **The print `P_{d,+,t}`** (computable). -/
def radPp (D : ListData) (digs : List Dig) (d t : ℕ) : Poly := polyC D (digAt digs d).1 t true false (digAt digs d).2
/-- **The print `P_{d,−,t}`** (computable). -/
def radPm (D : ListData) (digs : List Dig) (d t : ℕ) : Poly := polyC D (digAt digs d).1 t false false (digAt digs d).2

def repAt (D : ListData) (digs : List Dig) (sgn : Bool) (σ : ℕ → Bool) (d : ℕ) : ℕ :=
  D.listReport (Pop.popBits sgn (readX (4 * (digAt digs d).1) (digAt digs d).2 σ))

/-- The labels cover the corners of every digit population. -/
def DigsOk (digs : List Dig) : Prop := ∀ dg ∈ digs, 4 * dg.1 ≤ dg.2.length

theorem radP_eval (D : ListData) (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (digs : List Dig) (hok : DigsOk digs) (sgn : Bool) (d : ℕ) (hd : d < digs.length) (t : ℕ) (ht : t ≤ D.M)
    (σ : ℕ → Bool) :
    F2Poly.eval (polyC D (digAt digs d).1 t sgn false (digAt digs d).2) σ = decide (t = repAt D digs sgn σ d) := by
  have hdg : digAt digs d ∈ digs := by unfold digAt; rw [List.getD_eq_getElem _ _ hd]; exact List.getElem_mem hd
  have hl := hok _ hdg
  rw [← visitSpec_poly D (digAt digs d).1 t sgn ht false (digAt digs d).2 hl, visitSpec_eval D hnest]
  simp only [Bool.xor_false, repAt, ListFast.listReport_eq_fast]
  exact decide_eq_decide.mpr eq_comm

theorem repAt_le (D : ListData) (digs : List Dig) (sgn : Bool) (σ : ℕ → Bool) (d : ℕ) : repAt D digs sgn σ d ≤ D.M := by
  unfold repAt; rw [ListFast.listReport_eq_fast]; exact ListFast.fast_le D _

/-- The RADIX row's expression `H_{g,p,s}` over the digit lists. -/
def radExpr (D : ListData) (digs : List Dig) (p b0 : ℕ) (s : ZMod p) : Expr :=
  radixExpr digs.length D.M p b0 (radPp D digs) (radPm D digs) s

theorem radExpr_value (D : ListData) (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (digs : List Dig) (hok : DigsOk digs) (p b0 : ℕ) [NeZero p] (s : ZMod p) (σ : ℕ → Bool) :
    IntExpression.eval (radExpr D digs p b0 s) σ =
      bitInt (decide (Rows.tupleResidue p b0 (fun d : Fin digs.length => repAt D digs true σ d)
        (fun d : Fin digs.length => repAt D digs false σ d) = s)) := by
  let tp : Fin digs.length → Fin (D.M + 1) := fun d => ⟨repAt D digs true σ d, Nat.lt_succ_of_le (repAt_le _ _ _ _ _)⟩
  let tm : Fin digs.length → Fin (D.M + 1) := fun d => ⟨repAt D digs false σ d, Nat.lt_succ_of_le (repAt_le _ _ _ _ _)⟩
  have hp : ∀ (d : Fin digs.length) t, t ≤ D.M → F2Poly.eval (radPp D digs d t) σ = decide (t = tp d) := by
    intro d t ht
    rw [radPp, radP_eval D hnest digs hok true d d.isLt t ht σ]
  have hm : ∀ (d : Fin digs.length) t, t ≤ D.M → F2Poly.eval (radPm D digs d t) σ = decide (t = tm d) := by
    intro d t ht
    rw [radPm, radP_eval D hnest digs hok false d d.isLt t ht σ]
  rw [radExpr, radixExpr_eval digs.length D.M p b0 (radPp D digs) (radPm D digs) σ tp tm hp hm s,
    Rows.radixState_of_oneHot p b0 _ _ tp tm (fun d t => (hp d t (Nat.le_of_lt_succ t.isLt)).trans (by
      simp [Fin.ext_iff])) (fun d t => (hm d t (Nat.le_of_lt_succ t.isLt)).trans (by simp [Fin.ext_iff])) s]
  unfold bitInt
  split_ifs <;> simp_all [tp, tm]

/-! ## The factor specifications, in store order -/

/-- One block of factor specifications: the states `0, …, M` of one digit population. -/
noncomputable def blockSpecs (D : ListData) (dg : Dig) (sgn : Bool) (hl : 4 * dg.1 ≤ dg.2.length) :
    List (FSpec (negFam F35)) :=
  (List.range (D.M + 1)).map fun t => visitSpec D dg.1 (min t D.M) sgn (capC D dg.1) (min_le_right _ _) le_rfl
    false dg.2 hl

/-- **The RADIX row's factor specifications**: `P_{d,+,0..M}`, `P_{d,−,0..M}`, digit by digit. -/
noncomputable def radSpecs (D : ListData) : (digs : List Dig) → DigsOk digs → List (FSpec (negFam F35))
  | [], _ => []
  | dg :: rest, h => blockSpecs D dg true (h dg (by simp)) ++
      (blockSpecs D dg false (h dg (by simp)) ++ radSpecs D rest (fun x hx => h x (by simp [hx])))

theorem blockSpecs_poly (D : ListData) (dg : Dig) (sgn : Bool) (hl : 4 * dg.1 ≤ dg.2.length) :
    (blockSpecs D dg sgn hl).map FSpec.poly = (List.range (D.M + 1)).map fun t => polyC D dg.1 t sgn false dg.2 := by
  unfold blockSpecs
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  have ht' : t ≤ D.M := Nat.le_of_lt_succ (List.mem_range.mp ht)
  simp only [Function.comp_apply]
  rw [visitSpec_poly, min_eq_left ht']

theorem digAt_append (pre : List Dig) (dg : Dig) (rest : List Dig) : digAt (pre ++ dg :: rest) pre.length = dg := by
  simp [digAt]

theorem digAt_shift (pre : List Dig) (dg : Dig) (rest : List Dig) (i : ℕ) :
    digAt (pre ++ [dg] ++ rest) (pre.length + 1 + i) = digAt (pre ++ dg :: rest) (pre.length + 1 + i) := by
  simp

/-- **The factor prints are the store.** -/
theorem radSpecs_poly (D : ListData) : ∀ (digs : List Dig) (h : DigsOk digs) (pre : List Dig),
    (radSpecs D digs h).map FSpec.poly =
      storeFrom D.M (radPp D (pre ++ digs)) (radPm D (pre ++ digs)) pre.length digs.length
  | [], _, _ => by simp [radSpecs, storeFrom]
  | dg :: rest, h, pre => by
    have ih := radSpecs_poly D rest (fun x hx => h x (by simp [hx])) (pre ++ [dg])
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at ih
    simp only [radSpecs, List.map_append, blockSpecs_poly, List.length_cons, storeFrom, ih]
    congr 1
    · apply List.map_congr_left; intro t _; simp [radPp, digAt_append]
    · congr 1
      apply List.map_congr_left; intro t _; simp [radPm, digAt_append]

theorem radSpecs_length (D : ListData) : ∀ (digs : List Dig) (h : DigsOk digs),
    (radSpecs D digs h).length = 2 * digs.length * (D.M + 1)
  | [], _ => by simp [radSpecs]
  | dg :: rest, h => by
    simp only [radSpecs, List.length_append, blockSpecs, List.length_map, List.length_range,
      radSpecs_length D rest (fun x hx => h x (by simp [hx])), List.length_cons]
    ring

end NearCubicWires.WireExponent3_5.ListMachine.Row
