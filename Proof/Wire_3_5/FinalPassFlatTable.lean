import Proof.Wire_3_5.FinalPassFlatBuild

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Flat
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.SupplierWalk
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.SourceInterfaces Theorem25Completion

/-! ## The seed bits of a vertex -/

theorem eq_map_range_of_getD (l : List Bool) (n : ℕ) (f : ℕ → Bool) (hl : l.length = n)
    (h : ∀ c < n, l.getD c false = f c) : l = (List.range n).map f := by
  apply List.ext_getElem (by simp [hl])
  intro c h1 h2
  have hc : c < n := by rw [← hl]; exact h1
  have := h c hc
  rw [List.getD_eq_getElem _ _ h1] at this
  simp [this]

theorem bits_getD (m x y k : ℕ) (hy : y < 2 ^ m) (hk : k < 2 * m) :
    (binary m y ++ binary m x).getD k false = (y + 2 ^ m * x).testBit k := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add x hy]
  by_cases hkm : k < m
  · rw [if_pos hkm, List.getD_append _ _ _ _ (by simpa using hkm), binary_getD' m y k hkm]
  · rw [if_neg hkm, List.getD_append_right _ _ _ _ (by simp; omega), binary_length,
      binary_getD' m x (k - m) (by omega)]

/-- **The seed bits the machine reads are the vertex number's bits after the padding.** -/
theorem vertexSw_getD (m tf x y c : ℕ) (hy : y < 2 ^ m) (hc : tf + c < 2 * m) :
    (vertexSw m tf x y).getD c false = (y + 2 ^ m * x).testBit (tf + c) := by
  unfold vertexSw swOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  exact bits_getD m x y (tf + c) hy hc

section Vertex
variable (rank : ℕ) (v : MargulisVertex (2 ^ sideB rank))

/-- The seed bits of the walk vertex `v`. -/
def swV : List Bool := vertexSw (sideB rank) (padB rank) v.1.val v.2.val

theorem sideB_facts (hr : 1 ≤ rank) :
    padB rank ≤ 1 ∧ padB rank ≤ sideB rank ∧ 2 * sideB rank - padB rank = 2 * rank + (rank - 1) := by
  unfold padB sideB SupplierWalkBridge.toeplitzWalkSideBits SupplierWalkBridge.toeplitzSeedBits
  omega

theorem swV_getD (hr : 1 ≤ rank) (c : ℕ) (hc : c < 2 * rank + (rank - 1)) :
    (swV rank v).getD c false = (vnum v).testBit (padB rank + c) := by
  obtain ⟨_, _, h3⟩ := sideB_facts rank hr
  unfold swV vnum
  exact vertexSw_getD _ _ _ _ _ (ZMod.val_lt v.2) (by omega)

theorem swV_length (hr : 1 ≤ rank) : (swV rank v).length = 2 * rank + (rank - 1) := by
  obtain ⟨_, _, h3⟩ := sideB_facts rank hr
  unfold swV; rw [vertexSw_length, h3]

/-- The machine's diagonal word at the vertex is the vertex's diagonal word. -/
theorem epOfSw_vertex (hr : 1 ≤ rank) : epOfSw rank (swV rank v) = epV v := by
  have hl := swV_length rank v hr
  unfold epOfSw epV epL
  congr 1
  · congr 1
    refine eq_map_range_of_getD _ _ _ (by simp; omega) (fun c hc => ?_)
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hc, ← List.getD_eq_getElem?_getD,
      swV_getD rank v hr c (by omega)]
    rfl
  · refine eq_map_range_of_getD _ _ _ (by simp; omega) (fun c hc => ?_)
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hc, List.getElem?_drop,
      ← List.getD_eq_getElem?_getD, swV_getD rank v hr (rank + c) (by omega)]
    rfl

/-- The machine's translation word at the vertex is the vertex's translation word. -/
theorem bwOfSw_vertex (hr : 1 ≤ rank) : bwOfSw rank (swV rank v) = trLV v := by
  have hl := swV_length rank v hr
  unfold bwOfSw trLV trL
  refine eq_map_range_of_getD _ _ _ (by simp; omega) (fun c hc => ?_)
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hc, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, swV_getD rank v hr (2 * rank - 1 + c) (by omega)]
  unfold trV
  congr 2
  omega

end Vertex

/-! ## A visit's word -/

theorem frame_eq' (w : List Bool) : frame w = frameP w ++ [false] := frame_eq_frameP w

/-- **The word of a visit is the visit marker and the level rows of the base list at the decoded seed.** -/
theorem visitWordL_vertex (P : FlatListParams) (v : MargulisVertex (2 ^ sideB P.base.rank)) (L : ℕ)
    (hr : 1 ≤ P.base.rank) :
    visitWordL (sideB P.base.rank) P.base.rank L (padB P.base.rank) (P.base.J + 1) v.1.val v.2.val =
      true :: (levels P.base.J).flatMap (fun j => frame (rowsOf (P.base.data (P.decode v)) L j)) := by
  unfold visitWordL levelRows levels
  congr 1
  apply List.flatMap_congr
  intro j hj
  have hjJ : j ≤ P.base.J := by simp at hj; omega
  have hjr : j ≤ P.base.rank := le_trans hjJ (J_le_rank P.base)
  rw [frame_eq', rowsOf_decode P v L j hjr]
  have e1 := epOfSw_vertex P.base.rank v hr
  have e2 := bwOfSw_vertex P.base.rank v hr
  unfold swV at e1 e2
  rw [e1, e2]
  congr 2
  unfold rowOf rowBits rowBit
  rw [List.range_eq_range']

/-! ## The table of a list seed -/

/-- **The list walk's table** of the list seed `e`: for each visit, the marker and the rows of levels `J, …, 0` of the
base list at the visited seed (each framed and closed); then `false`. -/
def flatTable (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) : List Bool :=
  (List.finRange P.walkLen).flatMap (fun k =>
    true :: (levels P.base.J).flatMap (fun j => frame (rowsOf (P.base.data (P.decode (e.vertex k))) L j))) ++ [false]

theorem finRange_map_val' (n : ℕ) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) (fun i _ _ => by simp)

theorem walk_vertex (P : FlatListParams) (e : P.FlatSeed) (k : Fin P.walkLen) :
    WalkTimeLoop.vertex (r := sideB P.base.rank) (n := 2 * (P.errExp / 4)) e k.val = e.vertex k := by
  unfold WalkTimeLoop.vertex
  congr 1
  apply Fin.ext
  have := k.isLt
  unfold FlatListParams.walkLen at this
  simp only
  omega

/-- **The builder writes the list seed's table.** -/
theorem owAt_flatTable (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (hr : 1 ≤ P.base.rank) :
    owAt (n := 2 * (P.errExp / 4)) (sideB P.base.rank) P.base.rank L (padB P.base.rank) (P.base.J + 1) e P.walkLen ++
      [false] = flatTable P e L := by
  unfold flatTable owAt
  congr 1
  have hf : ∀ k : Fin P.walkLen, (true :: (levels P.base.J).flatMap
      (fun j => frame (rowsOf (P.base.data (P.decode (e.vertex k))) L j))) =
      visitAt (n := 2 * (P.errExp / 4)) (sideB P.base.rank) P.base.rank L (padB P.base.rank) (P.base.J + 1) e k.val := by
    intro k
    unfold visitAt
    rw [walk_vertex P e k, visitWordL_vertex P _ L hr]
  rw [List.flatMap_congr (fun k _ => hf k)]
  rw [← List.flatMap_map Fin.val (fun i => visitAt (n := 2 * (P.errExp / 4)) (sideB P.base.rank) P.base.rank L
    (padB P.base.rank) (P.base.J + 1) e i) (List.finRange P.walkLen), finRange_map_val']

end NearCubicWires.WireExponent3_5.FinalPass.Flat
