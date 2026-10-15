import Proof.Gates.Dispatch.WitnessG

/-!
# Fragment (W), part H: what the walks compute is `decodeWitness` / `witWord`
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- The decoded segments. -/
def segsOf (c : Call) (p : Params) (w : List Bool) : List (List ℕ) :=
  (readSegments (w.drop (p.k * Target.lambda c.n)) (segmentWidths c p)).1

theorem segsOf_eq (c : Call) (p : Params) (w : List Bool) :
    segsOf c p w = (readSegments (L0 c p w) (segmentWidths c p)).1 := by
  unfold segsOf L0 LCof; rw [readSegments_take]

theorem segsOf_get (c : Call) (p : Params) (w : List Bool) (g : ℕ) (hg : g < p.J * roleCount c.kind) :
    (segsOf c p w).getD g [] = (readBlock (rsG c p w g).2 (wsR c (g % roleCount c.kind))).1 := by
  have hR := roleCount_pos c.kind
  have hgl : g < (segmentWidths c p).length := by rw [segW_length]; exact hg
  have hseg : (segmentWidths c p).getD g [] = wsR c (g % roleCount c.kind) := by
    have h1 : g = g / roleCount c.kind * roleCount c.kind + g % roleCount c.kind := (Nat.div_add_mod' g _).symm
    have h2 : g / roleCount c.kind < p.J := by
      rw [Nat.div_lt_iff_lt_mul hR]; exact hg
    conv_lhs => rw [h1]
    exact segW_get c p _ _ h2 (Nat.mod_lt _ hR)
  rw [segsOf_eq]
  have e1 : ((readSegments (L0 c p w) (segmentWidths c p)).1).getD g [] =
      (((readSegments (L0 c p w) (segmentWidths c p)).1).take (g + 1)).getD g [] := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  rw [e1, readSegments_fst_take, take_succ_getD _ [] _ hgl, readSegments_snoc, hseg, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [readSegments_fst_length]; simp)]
  simp [readSegments_fst_length, Nat.min_eq_left hgl.le]
  rfl

theorem readBlock_getD (l : List Bool) (ws : List ℕ) (i : ℕ) (hi : i < ws.length) :
    ((readBlock l ws).1).getD i 0 = bitsValue ((l.drop (ws.take i).sum).take (ws.getD i 0)) := by
  have e1 : ((readBlock l ws).1).getD i 0 = (((readBlock l ws).1).take (i + 1)).getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  rw [e1, readBlock_fst_take, readBlock_take_succ l ws i hi, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [readBlock_fst_length]; simp)]
  simp [readBlock_fst_length, Nat.min_eq_left hi.le, List.getD_eq_getElem?_getD, hi]

/-- Field `i` of segment `g` is the decoded offset. -/
theorem fieldV_eq (c : Call) (p : Params) (w : List Bool) (g i : ℕ) (hg : g < p.J * roleCount c.kind)
    (hi : i < (circ c (g % roleCount c.kind)).coeffs.length) :
    fieldV c p w g i = ((segsOf c p w).getD g []).getD i 0 := by
  rw [segsOf_get c p w g hg, readBlock_getD _ _ _ (by simp [wsR, hi])]; rfl

theorem segsOf_get_length (c : Call) (p : Params) (w : List Bool) (g : ℕ) (hg : g < p.J * roleCount c.kind) :
    ((segsOf c p w).getD g []).length = (circ c (g % roleCount c.kind)).coeffs.length := by
  rw [segsOf_get c p w g hg, readBlock_fst_length]; simp [wsR]

/-- The coordinate list of the witness. -/
theorem decode_coords (c : Call) (p : Params) (w : List Bool) :
    (readBlock w (List.replicate p.k (Target.lambda c.n))).1 = cl w (Target.lambda c.n) p.k := rfl

theorem zip_all_iff (cs : List ℤ) (vs : List ℕ) (h : vs.length = cs.length) :
    ((cs.zip vs).all fun av => decide (av.2 ≤ 2 * av.1.natAbs)) = true ↔
      ∀ i < cs.length, vs.getD i 0 ≤ 2 * (cs.getD i 0).natAbs := by
  rw [List.all_eq_true]
  constructor
  · intro hall i hi
    have hm : (cs[i], vs[i]'(by omega)) ∈ cs.zip vs := by
      rw [List.mem_iff_getElem]; exact ⟨i, by simp [h, hi], by simp⟩
    have := hall _ hm
    simp only [decide_eq_true_eq] at this
    simpa [List.getD_eq_getElem?_getD, hi, show i < vs.length by omega] using this
  · intro hall av hav
    rw [List.mem_iff_getElem] at hav
    obtain ⟨i, hi, rfl⟩ := hav
    simp only [List.length_zip, Nat.lt_min] at hi
    have := hall i hi.1
    simp only [List.getElem_zip, decide_eq_true_eq]
    simpa [List.getD_eq_getElem?_getD, hi.1, hi.2] using this

theorem range_all_iff (J R : ℕ) (P : ℕ → Prop) [DecidablePred P] (hR : 0 < R) :
    ((List.range J).all fun s => (List.range R).all fun r => decide (P (s * R + r))) = true ↔
      ∀ g < J * R, P g := by
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h g hg
    have h1 : g = g / R * R + g % R := (Nat.div_add_mod' g R).symm
    rw [h1]; exact h _ ((Nat.div_lt_iff_lt_mul hR).mpr hg) _ (Nat.mod_lt _ hR)
  · intro h s hs r hr; exact h _ (by nlinarith)

theorem segOK_iff_zip (c : Call) (p : Params) (w : List Bool) (s r : ℕ) (hs : s < p.J) (hr : r < roleCount c.kind) :
    segOK c p w (s * roleCount c.kind + r) ↔
      (((circ c r).coeffs.zip ((segsOf c p w).getD (s * roleCount c.kind + r) [])).all
        fun av => decide (av.2 ≤ 2 * av.1.natAbs)) = true := by
  have hg : s * roleCount c.kind + r < p.J * roleCount c.kind := by nlinarith
  have hm := mod_role c s r hr
  rw [zip_all_iff _ _ (by rw [segsOf_get_length _ _ _ _ hg, hm])]
  unfold segOK
  rw [hm]
  constructor
  · intro h i hi
    have := h i hi
    rwa [fieldV_eq c p w _ i hg (by rw [hm]; exact hi)] at this
  · intro h i hi
    rw [fieldV_eq c p w _ i hg (by rw [hm]; exact hi)]
    exact h i hi

/-- **The validity test of `decodeWitness`.** -/
theorem decode_isSome_iff (c : Call) (p : Params) (w : List Bool) :
    (decodeWitness c p w).isSome = true ↔
      goodC c.n (cl w (Target.lambda c.n) p.k) ∧ ∀ g < p.J * roleCount c.kind, segOK c p w g := by
  have hR := roleCount_pos c.kind
  have hsegs : (readSegments (readBlock w (List.replicate p.k (Target.lambda c.n))).2 (segmentWidths c p)).1 =
      segsOf c p w := by rw [readBlock_snd]; simp [segsOf, List.sum_replicate]
  have key : (decodeWitness c p w).isSome = true ↔
      (((cl w (Target.lambda c.n) p.k).all fun x => decide (x < c.n)) &&
        decide (cl w (Target.lambda c.n) p.k).Nodup &&
        (List.range p.J).all fun s => (List.range (roleCount c.kind)).all fun r =>
          ((circ c r).coeffs.zip ((segsOf c p w).getD (segmentIndex c s r) [])).all
            fun av => decide (av.2 ≤ 2 * av.1.natAbs)) = true := by
    simp only [cl]
    unfold decodeWitness
    rw [hsegs]
    dsimp only
    split_ifs with h <;> simp_all <;> exact h.2
  rw [key]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hc1 : ((cl w (Target.lambda c.n) p.k).all fun x => decide (x < c.n)) = true ↔
      ∀ x ∈ cl w (Target.lambda c.n) p.k, x < c.n := by simp [List.all_eq_true]
  have hc3 : ((List.range p.J).all fun s => (List.range (roleCount c.kind)).all fun r =>
      ((circ c r).coeffs.zip ((segsOf c p w).getD (segmentIndex c s r) [])).all
        fun av => decide (av.2 ≤ 2 * av.1.natAbs)) = true ↔ ∀ g < p.J * roleCount c.kind, segOK c p w g := by
    simp only [List.all_eq_true, List.mem_range]
    constructor
    · intro h g hg
      have h1 : g = g / roleCount c.kind * roleCount c.kind + g % roleCount c.kind := (Nat.div_add_mod' g _).symm
      have hs : g / roleCount c.kind < p.J := (Nat.div_lt_iff_lt_mul hR).mpr hg
      have hr : g % roleCount c.kind < roleCount c.kind := Nat.mod_lt _ hR
      rw [h1, segOK_iff_zip c p w _ _ hs hr, List.all_eq_true]
      exact h _ hs _ hr
    · intro h s hs r hr
      have := (segOK_iff_zip c p w s r hs hr).mp (h _ (by nlinarith))
      rw [List.all_eq_true] at this
      exact this
  rw [hc1, hc3]
  unfold goodC
  tauto

end NearCubicGates.Close.Dispatch
