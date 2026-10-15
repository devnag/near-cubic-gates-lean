import Proof.Wire_3_5.FinalPassMask

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.SupplierWalk NearCubicWires.SupplierToeplitzCore NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary

/-! ## The per-point reference -/

/-- The parity `⊕_k c_k Z_k` of a coefficient word against a point. -/
def parityDot : List Bool → List Bool → Bool
  | c :: cs, z :: zs => xor (c && z) (parityDot cs zs)
  | _, _ => false

def visitOk (vs : List (List Bool)) (Z : List Bool) : Bool := decide ((vs.filter fun c => parityDot c Z).length ≤ 32)

/-- **The filter from its table**: at least `thr` of the visited base seeds accept. -/
def tabEval (thr : ℕ) (tbl : List (List (List Bool))) (Z : List Bool) : Bool :=
  decide (thr ≤ (tbl.filter fun vs => visitOk vs Z).length)

/-- One copy's word: a marker, then the framed coefficient word. -/
def copyWord (cs : List Bool) : List Bool := true :: frame cs

/-- One visit's word: a marker, the copies, an end marker. -/
def visitWord (vs : List (List Bool)) : List Bool := true :: (vs.flatMap copyWord ++ [false])

/-- **The table as one word**: the visits, then an end marker. -/
def tableWord (tbl : List (List (List Bool))) : List Bool := tbl.flatMap visitWord ++ [false]

/-! ## Parities as counts -/

/-- The number of coordinates where both words are one. -/
def dotCnt (cs zs : List Bool) : ℕ := ∑ i ∈ Finset.range cs.length, if (cs.getD i false && zs.getD i false) then 1 else 0

theorem odd_add_ite (n : ℕ) (b : Bool) : decide (Odd (n + if b then 1 else 0)) = xor b (decide (Odd n)) := by
  cases b
  · simp
  · rw [if_pos rfl, Bool.true_xor]
    by_cases h : Odd n
    · have h1 : ¬ Odd (n + 1) := by rw [Nat.odd_add_one]; exact not_not.mpr h
      simp [h, h1]
    · have h1 : Odd (n + 1) := by rw [Nat.odd_add_one]; exact h
      simp [h, h1]

theorem parityDot_eq_odd : ∀ (cs zs : List Bool), parityDot cs zs = decide (Odd (dotCnt cs zs))
  | [], zs => by simp [parityDot, dotCnt]
  | c :: cs, [] => by simp [parityDot, dotCnt]
  | c :: cs, z :: zs => by
    rw [parityDot, parityDot_eq_odd cs zs]
    unfold dotCnt
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [odd_add_ite]

/-! ## The seed's filter is the table's filter -/

def coefWord (P : GapParams) {K : Type} (o : BiasOps K) (c : CopySeed P K) (L : ℕ) : List Bool :=
  (List.range L).map fun k => selected P c.1 k && biasBit o c.2.1 c.2.2 k

theorem copyParity_eq_parityDot (P : GapParams) {K : Type} (o : BiasOps K) (c : CopySeed P K) (Z : List Bool) :
    copyParity P o c Z = parityDot (coefWord P o c Z.length) Z := by
  rw [parityDot_eq_odd]
  unfold copyParity selectedActive dotCnt coefWord
  rw [Finset.filter_filter, Finset.card_filter, List.length_map, List.length_range]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have e : ((List.range Z.length).map fun k => selected P c.1 k && biasBit o c.2.1 c.2.2 k).getD i false =
      (selected P c.1 i && biasBit o c.2.1 c.2.2 i) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  rw [e]
  cases Z.getD i false <;> cases selected P c.1 i <;> cases biasBit o c.2.1 c.2.2 i <;> simp

theorem card_univ_filter {n : ℕ} (p : Fin n → Bool) :
    (Finset.univ.filter fun j => p j = true).card = ((List.finRange n).filter p).length := by
  rw [Fin.univ_def]
  show Multiset.card (Multiset.filter (fun j => p j = true) (↑(List.finRange n) : Multiset (Fin n))) = _
  rw [Multiset.filter_coe, Multiset.coe_card]
  simp

theorem baseFilter_eq_visitOk (P : GapParams) {K : Type} (o : BiasOps K) (s : BaseSeed P K) (Z : List Bool) :
    baseFilter P o s Z = visitOk ((List.finRange 128).map fun j => coefWord P o (s j) Z.length) Z := by
  unfold baseFilter visitOk
  rw [card_univ_filter, List.filter_map, List.length_map]
  have h : ∀ j ∈ List.finRange 128,
      copyParity P o (s j) Z = ((fun c => parityDot c Z) ∘ fun j => coefWord P o (s j) Z.length) j := by
    intro j _; simp [copyParity_eq_parityDot]
  rw [List.filter_congr h]

/-- The machine's field operations of the filter (`filterBits`). -/
def filtOps (P : GapParams) : BiasOps (Fin (2 ^ P.fieldBits)) :=
  GF.bitOps (GF.firstPrimitive P.fieldBits) P.fieldBits (GF.firstPrimitive_fieldBits P)

/-- **The seed's table**: for each visited base seed, the coefficient words of its `128` copies at length `L`. -/
def filterTable (P : GapParams) (e : GapSeed P) (L : ℕ) : List (List (List Bool)) :=
  (List.finRange P.walkLen).map fun i =>
    (List.finRange 128).map fun j => coefWord P (filtOps P) (vertexSeed P (Equiv.refl _) (e.vertex i) j) L

theorem filterBits_eq_tab (P : GapParams) (e : GapSeed P) (Z : List Bool) :
    filterBits P e Z = tabEval (majorityThreshold P.walkLen) (filterTable P e Z.length) Z := by
  unfold filterBits gapFilterWith concreteMajorityFailure concreteBadTimes tabEval filterTable
  rw [card_univ_filter, List.filter_map, List.length_map]
  have h : ∀ i ∈ List.finRange P.walkLen,
      concreteBadAt (fun v => baseFilter P (filtOps P) (vertexSeed P (Equiv.refl _) v) Z) e i =
        ((fun vs => visitOk vs Z) ∘ fun i => (List.finRange 128).map fun j =>
          coefWord P (filtOps P) (vertexSeed P (Equiv.refl _) (e.vertex i) j) Z.length) i := by
    intro i _
    simp only [Function.comp_apply, concreteBadAt]
    rw [baseFilter_eq_visitOk]
  exact congrArg (fun l => decide (majorityThreshold P.walkLen ≤ l.length)) (List.filter_congr h)

/-- Every coefficient word of the table has the point's length. -/
theorem filterTable_lengths (P : GapParams) (e : GapSeed P) (L : ℕ) :
    ∀ vs ∈ filterTable P e L, ∀ cs ∈ vs, cs.length = L := by
  intro vs hvs cs hcs
  simp only [filterTable, List.mem_map] at hvs
  obtain ⟨i, _, rfl⟩ := hvs
  simp only [List.mem_map] at hcs
  obtain ⟨j, _, rfl⟩ := hcs
  simp [coefWord]

end NearCubicWires.WireExponent3_5.FinalPass.Filt
