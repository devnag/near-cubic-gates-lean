import Proof.Wire_3_5.SeedFixSampExpr
import Proof.Wire_3_5.ListMachineRowPopClass
import Proof.Wire_3_5.ListMachineRowFiltClass
import Proof.Wire_3_5.ListMachineRowRadixClass
import Proof.Wire_3_5.FinalPassMaskRef
import Proof.Wire_3_5.CompilerMachinePoolSpec

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Records
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.SupplierPipeline

/-! ## Reading a row's corner atoms -/

theorem range_map_getD {α β : Type} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem labsOf_length (G r : ℕ) (gis : List ℕ) : (CompilerMachine.Pool.labsOf G r gis).length = 4 * gis.length := by
  unfold CompilerMachine.Pool.labsOf
  induction gis with
  | nil => simp
  | cons g gs ih => simp [List.flatMap_cons] at ih ⊢; omega

/-- **The corner atoms of star row `r`, read through `labsOf`, are the corner word of the pool gates.** -/
theorem readX_labsOf {n : ℕ} (G r : ℕ) (gis : List ℕ) (σ : ℕ → Bool) (T : ℕ → BitInput n → Bool) (c U V : BitInput n)
    (hσ : ∀ gi ∈ gis, ∀ k : Fin 4, σ (CompilerMachine.Pool.poolIndex G r k gi) = corners (T gi) c U V k) :
    ListMachine.Row.readX (4 * gis.length) (CompilerMachine.Pool.labsOf G r gis) σ = cornerWord (gis.map T) c U V := by
  unfold ListMachine.Row.readX ListMachine.Print.labOf
  rw [← labsOf_length G r gis, range_map_getD]
  unfold CompilerMachine.Pool.labsOf cornerWord
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro gi hgi
  simp only [List.map_map, Function.comp_def]
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    exact hσ gi hgi ⟨k, h1⟩

/-! ## Slices of the pool -/

/-- A default gate (never read inside a slice). -/
def dGate {n : ℕ} : NormalizedThresholdGate n := ⟨fun _ => 0, 0⟩

/-- The offset of slice `j` in the concatenation. -/
def sliceOff {α : Type} (ls : List (List α)) (j : ℕ) : ℕ := ((ls.take j).map List.length).sum

/-- The pool indices of slice `j`. -/
def sliceGis {α : Type} (ls : List (List α)) (j : ℕ) : List ℕ := List.range' (sliceOff ls j) (ls.getD j []).length

theorem getD_flatten_slice {α : Type} (ls : List (List α)) (d : α) (j : ℕ) (hj : j < ls.length) (i : ℕ)
    (hi : i < (ls.getD j []).length) : ls.flatten.getD (sliceOff ls j + i) d = (ls.getD j []).getD i d := by
  induction ls generalizing j with
  | nil => simp at hj
  | cons l ls ih =>
    cases j with
    | zero =>
      simp only [sliceOff, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.getD_cons_zero] at hi ⊢
      rw [List.flatten_cons, List.getD_append _ _ _ _ hi]
    | succ j =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
      simp only [List.getD_cons_succ] at hi ⊢
      have h := ih j hj hi
      simp only [sliceOff, List.take_succ_cons, List.map_cons, List.sum_cons] at h ⊢
      rw [List.flatten_cons, Nat.add_assoc, List.getD_append_right _ _ _ _ (by omega)]
      rw [show l.length + (((ls.take j).map List.length).sum + i) - l.length = ((ls.take j).map List.length).sum + i by omega]
      exact h

/-- **Slice `j` of the pool, read by its indices**, is the `j`-th list. -/
theorem slice_map {α : Type} (ls : List (List α)) (d : α) (j : ℕ) (hj : j < ls.length) :
    (sliceGis ls j).map (fun gi => ls.flatten.getD gi d) = ls.getD j [] := by
  apply List.ext_getElem
  · simp [sliceGis]
  · intro i h1 h2
    simp only [sliceGis, List.length_map, List.length_range'] at h1
    simp only [List.getElem_map, sliceGis, List.getElem_range']
    rw [Nat.one_mul, getD_flatten_slice ls d j hj i h1, List.getD_eq_getElem _ _ h1]

theorem sliceGis_length {α : Type} (ls : List (List α)) (j : ℕ) : (sliceGis ls j).length = (ls.getD j []).length := by
  simp [sliceGis]

theorem sliceOff_add_le {α : Type} (ls : List (List α)) (j : ℕ) (hj : j < ls.length) :
    sliceOff ls j + (ls.getD j []).length ≤ ls.flatten.length := by
  induction ls generalizing j with
  | nil => simp at hj
  | cons l ls ih =>
    cases j with
    | zero => simp [sliceOff]
    | succ j =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
      have h := ih j hj
      simp only [sliceOff, List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ,
        List.flatten_cons, List.length_append] at h ⊢
      omega

theorem mem_sliceGis_lt {α : Type} (ls : List (List α)) (j : ℕ) (hj : j < ls.length) :
    ∀ gi ∈ sliceGis ls j, gi < ls.flatten.length := by
  intro gi hgi
  have h := sliceOff_add_le ls j hj
  simp only [sliceGis, List.mem_range'] at hgi
  obtain ⟨i, hi, rfl⟩ := hgi
  omega

/-! ## Row requests and the values their errSpecs pin -/

/-- A C2 row request of the three kinds the entries use. -/
inductive RowReq
  | filt (r : ListMachine.Row.FiltReq)
  | pop (r : ListMachine.Row.PopReq)
  | rad (r : ListMachine.Row.RadReq)

/-- **The value a row's errSpec pins at the assignment `σ`** (C2's `filtContract`/`popContract`/`radContract`
errSpecs, verbatim). -/
noncomputable def RowReq.val : RowReq → (ℕ → Bool) → ℤ
  | .filt r, σ => bitInt (gapFilter r.P r.e (popBits r.sgn (ListMachine.Row.readX (4 * r.L) r.labs σ)))
  | .pop r, σ =>
    bitInt (decide (r.P.flatReport r.e (popBits r.sgn (ListMachine.Row.readX (4 * r.L) r.labs σ)) = r.s.val))
  | .rad r, σ =>
    bitInt (decide (Rows.tupleResidue r.p r.b0 (fun d : Fin r.digs.length => ListMachine.Row.repAt r.D r.digs true σ d)
      (fun d : Fin r.digs.length => ListMachine.Row.repAt r.D r.digs false σ d) = (r.s : ZMod r.p)))

/-- A printed row is a list of requests whose expressions are concatenated: its value is the sum. -/
noncomputable def groupVal (g : List RowReq) (σ : ℕ → Bool) : ℤ := (g.map fun r => r.val σ).sum

/-- An entry's value: the product of its printed rows (`sampTerms_eval`'s `hD`). -/
noncomputable def entryVal (gs : List (List RowReq)) (σ : ℕ → Bool) : ℤ := (gs.map fun g => groupVal g σ).prod

/-! ## From C2's outputs to the entry value -/

/-- A request's output expression meets its errSpec: its value is the request's pinned value at every assignment. -/
def RowReq.Meets (r : RowReq) (V : IntExpression ℕ) : Prop := ∀ σ, IntExpression.eval V σ = r.val σ

section Meets
open NearCubicWires.WireExponent3_5.Cost
variable {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E)

theorem filt_meets (r : ListMachine.Row.FiltReq) (V : IntExpression ℕ)
    (h : (ListMachine.Row.filtContract B).errSpec r V) : (RowReq.filt r).Meets V := h

theorem pop_meets (r : ListMachine.Row.PopReq) (V : IntExpression ℕ)
    (h : (ListMachine.Row.popContract B).errSpec r V) : (RowReq.pop r).Meets V := h

theorem rad_meets (r : ListMachine.Row.RadReq) (V : IntExpression ℕ)
    (h : (ListMachine.Row.radContract B).errSpec r V) : (RowReq.rad r).Meets V := h

end Meets

/-- **A printed row's expression** (the concatenated outputs of its requests) has the row's value. -/
theorem groupExpr_eval (g : List RowReq) (Ws : List (IntExpression ℕ)) (h : List.Forall₂ RowReq.Meets g Ws)
    (σ : ℕ → Bool) : IntExpression.eval Ws.flatten σ = groupVal g σ := by
  induction h with
  | nil => rfl
  | cons hW _ ih =>
    rw [List.flatten_cons, SeedFix.seval_append, ih, hW σ]
    simp [groupVal]

/-- **An entry's printed rows multiply to the entry value**: `sampTerms_eval`'s `hD` from the product lemmas. -/
theorem entryExpr_eval (gs : List (List RowReq)) (Vs : List (IntExpression ℕ))
    (h : List.Forall₂ (fun g V => ∀ σ, IntExpression.eval V σ = groupVal g σ) gs Vs) (σ : ℕ → Bool) :
    (Vs.map fun V => IntExpression.eval V σ).prod = entryVal gs σ := by
  induction h with
  | nil => rfl
  | cons hV _ ih =>
    rw [List.map_cons, List.prod_cons, ih, hV σ]
    simp [entryVal]

theorem bitInt_all {β : Type} (l : List β) (f : β → Bool) : (l.map fun b => bitInt (f b)).prod = bitInt (l.all f) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.all_cons, ListMachine.bitInt_and]

theorem prod_bitInt {a : ℕ} (f : Fin a → Bool) : ∏ j, bitInt (f j) = bitInt (decide (∀ j, f j = true)) := by
  by_cases h : ∀ j, f j = true
  · rw [decide_eq_true h]
    exact Finset.prod_eq_one fun j _ => by rw [h j]; rfl
  · rw [decide_eq_false h]
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp only [Bool.not_eq_true] at hj; rw [hj]; rfl)

theorem sum_filter_map {β : Type} (l : List β) (p : β → Bool) (g : β → ℤ) :
    ((l.filter p).map g).sum = (l.map fun s => if p s then g s else 0).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => by_cases h : p b <;> simp [h, ih]

/-! ## The SYM clamp factor -/

/-- The reports `s ≤ M` whose clamp at `m` is the state `τ`: `{τ}` for `τ ≥ 1`, `{0} ∪ (m, M]` for `τ = 0`. -/
def clampPre (M m τ : ℕ) : List (Fin (M + 1)) :=
  (List.finRange (M + 1)).filter fun s => decide ((Rows.clampState m s.val : ℕ) = τ)

/-- **The clamp factor's value**: the sum of the indicators `[r = s]` over the preimage is `[clamp_m r = τ]`. -/
theorem sum_clampPre (M m τ r : ℕ) (hr : r ≤ M) :
    ((clampPre M m τ).map fun s => bitInt (decide (r = s.val))).sum =
      bitInt (decide ((Rows.clampState m r : ℕ) = τ)) := by
  unfold clampPre
  rw [sum_filter_map, ← Fin.sum_univ_def]
  rw [Finset.sum_eq_single_of_mem (⟨r, by omega⟩ : Fin (M + 1)) (Finset.mem_univ _)]
  · by_cases hp : (Rows.clampState m r : ℕ) = τ
    · simp [hp, bitInt]
    · simp [hp, bitInt]
  · intro s _ hs
    have hne : r ≠ s.val := fun h => hs (Fin.ext h.symm)
    simp [hne, bitInt]

/-! ## The SYM entry -/

/-- The SYM pool slices: each carrier's doubled atoms (`maskGates`), then each circuit's bottoms. -/
def symSlices {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) :
    List (List (NormalizedThresholdGate n)) :=
  carriers.map maskGates ++ List.ofFn fun i => symGates (Cs i)

/-- The SYM pool: the slices concatenated. -/
def symPool {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) :
    List (NormalizedThresholdGate n) :=
  (symSlices Cs carriers).flatten

/-- The FILTER row of slice `j` at star row `row` (sign `+`). -/
def filtRow {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (FP : GapParams) (e : GapSeed FP)
    (G row nw j : ℕ) : RowReq :=
  .filt ⟨FP, e, ⟨(sl.getD j []).length, true, CompilerMachine.Pool.labsOf G row (sliceGis sl j), nw⟩⟩

/-- The POP row of slice `j` at star row `row`, sign `sgn`, target `s`. -/
def popRow {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (Pl : FlatListParams) (e' : Pl.FlatSeed)
    (G row nw j : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1)) : RowReq :=
  .pop ⟨Pl, e', (sl.getD j []).length, sgn, CompilerMachine.Pool.labsOf G row (sliceGis sl j), s, nw⟩

/-- **The SYM factor `(j, ±)`**: the POP rows of the targets whose clamp at `m` is `τ`. -/
def popFactor {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (Pl : FlatListParams) (e' : Pl.FlatSeed)
    (G row nw j : ℕ) (sgn : Bool) (m τ : ℕ) : List RowReq :=
  (clampPre Pl.M m τ).map (popRow sl Pl e' G row nw j sgn)

/-- **The SYM entry's printed rows**: `R = |carriers| + 2a` rows, the FILTER rows then per circuit
the `+` and `−` factors. -/
def symGroups {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (FP : GapParams) (e : GapSeed FP) (Pl : FlatListParams) (e' : Pl.FlatSeed) (m : Fin a → ℕ) (τ : Rows.SymState m)
    (G row nw : ℕ) : List (List RowReq) :=
  (List.range carriers.length).map (fun j => [filtRow (symSlices Cs carriers) FP e G row nw j]) ++
    (List.finRange a).flatMap fun (i : Fin a) =>
      [popFactor (symSlices Cs carriers) Pl e' G row nw (carriers.length + (i : ℕ)) true (m i) (τ i).1,
        popFactor (symSlices Cs carriers) Pl e' G row nw (carriers.length + (i : ℕ)) false (m i) (τ i).2]

theorem symGroups_length {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (FP : GapParams) (e : GapSeed FP) (Pl : FlatListParams) (e' : Pl.FlatSeed) (m : Fin a → ℕ) (τ : Rows.SymState m)
    (G row nw : ℕ) : (symGroups Cs carriers FP e Pl e' m τ G row nw).length = carriers.length + 2 * a := by
  unfold symGroups
  rw [List.length_append, List.length_map, List.length_range, List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
  ring

theorem symSlices_length {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) :
    (symSlices Cs carriers).length = carriers.length + a := by
  simp [symSlices]

theorem symSlices_carrier {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (j : ℕ) (hj : j < carriers.length) : (symSlices Cs carriers).getD j [] = maskGates (carriers.getD j []) := by
  unfold symSlices
  rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ hj, List.getElem_map]

theorem symSlices_circuit {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (i : Fin a) : (symSlices Cs carriers).getD (carriers.length + i) [] = symGates (Cs i) := by
  unfold symSlices
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **A slice's corner atoms, read through its labels**, are the corner word of the slice's gates. -/
theorem readX_slice {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (j : ℕ) (hj : j < sl.length) (G row : ℕ)
    (σ : ℕ → Bool) (c U V : BitInput n)
    (hσ : ∀ gi < sl.flatten.length, ∀ k : Fin 4, σ (CompilerMachine.Pool.poolIndex G row k gi) =
      corners (sl.flatten.getD gi dGate).eval c U V k) :
    ListMachine.Row.readX (4 * (sl.getD j []).length) (CompilerMachine.Pool.labsOf G row (sliceGis sl j)) σ =
      cornerWord ((sl.getD j []).map NormalizedThresholdGate.eval) c U V := by
  rw [← sliceGis_length sl j, readX_labsOf G row (sliceGis sl j) σ (fun gi => (sl.flatten.getD gi dGate).eval) c U V
    (fun gi hgi k => hσ gi (mem_sliceGis_lt sl j hj gi hgi) k)]
  congr 1
  rw [← slice_map sl dGate j hj, List.map_map]
  rfl

/-- **The SYM product lemma, generic form**: at every assignment whose row atoms are the corners of the SYM pool at
`(c, U_u, V_v)`, the entry's printed rows multiply to `bitInt (mask && H_{e',τ})`. -/
theorem symEntry_prod_gen (P : StarParams) (σt : P.Translation) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (FP : GapParams) (e : GapSeed FP) (Pl : FlatListParams) (e' : Pl.FlatSeed)
    (τ : Rows.SymState (Primitive.symM P Cs)) (c : BitInput P.n) (hc : P.IsCenter σt c) (u v : P.Errors)
    (G row nw : ℕ) (σ : ℕ → Bool)
    (hσ : ∀ gi < (symPool Cs carriers).length, ∀ k : Fin 4, σ (CompilerMachine.Pool.poolIndex G row k gi) =
      corners ((symPool Cs carriers).getD gi dGate).eval c (P.errorVector P.leftBlock u)
        (P.errorVector P.rightBlock v) k) :
    entryVal (symGroups Cs carriers FP e Pl e' (Primitive.symM P Cs) τ G row nw) σ =
      bitInt (maskBits P σt carriers FP e (P.point c u v) &&
        Rows.symIndicator (Primitive.symM P Cs) (symRepFast P Cs Pl e' c u v) τ) := by
  -- the FILTER rows: the mask
  have hF : ((List.range carriers.length).map fun j =>
      groupVal [filtRow (symSlices Cs carriers) FP e G row nw j] σ).prod =
      bitInt (maskBits P σt carriers FP e (P.point c u v)) := by
    rw [maskBits_point P hc u v carriers FP e, ← bitInt_all, ← range_map_getD carriers []]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < carriers.length := List.mem_range.mp hj
    have hjs : j < (symSlices Cs carriers).length := by rw [symSlices_length]; omega
    unfold groupVal filtRow
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    show bitInt (gapFilter FP e (popBits true (ListMachine.Row.readX (4 * ((symSlices Cs carriers).getD j []).length)
      (CompilerMachine.Pool.labsOf G row (sliceGis (symSlices Cs carriers) j)) σ))) = _
    rw [readX_slice (symSlices Cs carriers) j hjs G row σ c _ _ hσ, gapFilter_eq_filterBits,
      symSlices_carrier Cs carriers j hj']
  -- the POP factors: the joint state indicator
  have hPf : ∀ (i : Fin a) (sgn : Bool) (τi : ℕ),
      groupVal (popFactor (symSlices Cs carriers) Pl e' G row nw (carriers.length + (i : ℕ)) sgn
        (Primitive.symM P Cs i) τi) σ =
        bitInt (decide ((Rows.clampState (Primitive.symM P Cs i)
          (flatReportFast Pl e' (if sgn then Primitive.symZp P Cs c u v i else Primitive.symZm P Cs c u v i)) : ℕ) =
            τi)) := by
    intro i sgn τi
    have his : carriers.length + (i : ℕ) < (symSlices Cs carriers).length := by rw [symSlices_length]; omega
    have hZ : popBits sgn (ListMachine.Row.readX (4 * ((symSlices Cs carriers).getD (carriers.length + (i : ℕ)) []).length)
        (CompilerMachine.Pool.labsOf G row (sliceGis (symSlices Cs carriers) (carriers.length + (i : ℕ)))) σ) =
        (if sgn then Primitive.symZp P Cs c u v i else Primitive.symZm P Cs c u v i) := by
      rw [readX_slice (symSlices Cs carriers) _ his G row σ c _ _ hσ, symSlices_circuit Cs carriers i]
      cases sgn
      · rw [(popBits_cornerWord _ c _ _).2, List.map_map]; rfl
      · rw [(popBits_cornerWord _ c _ _).1, List.map_map]; rfl
    unfold groupVal popFactor
    rw [List.map_map, ← flatReport_eq_fast]
    rw [← sum_clampPre Pl.M (Primitive.symM P Cs i) τi _ (Pl.flatReport_le _ _)]
    refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
    show bitInt (decide (Pl.flatReport e' (popBits sgn (ListMachine.Row.readX
      (4 * ((symSlices Cs carriers).getD (carriers.length + (i : ℕ)) []).length)
      (CompilerMachine.Pool.labsOf G row (sliceGis (symSlices Cs carriers) (carriers.length + (i : ℕ)))) σ)) =
        s.val)) = _
    rw [hZ]
  have hS : (((List.finRange a).flatMap (fun (i : Fin a) =>
      [popFactor (symSlices Cs carriers) Pl e' G row nw (carriers.length + (i : ℕ)) true (Primitive.symM P Cs i) (τ i).1,
        popFactor (symSlices Cs carriers) Pl e' G row nw (carriers.length + (i : ℕ)) false (Primitive.symM P Cs i)
          (τ i).2])).map (fun g => groupVal g σ)).prod =
      bitInt (Rows.symIndicator (Primitive.symM P Cs) (symRepFast P Cs Pl e' c u v) τ) := by
    rw [SeedFix.prod_map_flatMap, ← Fin.prod_univ_def]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hPf, if_true,
      Bool.false_eq_true, if_false]
    simp only [← ListMachine.bitInt_and]
    rw [prod_bitInt]
    unfold Rows.symIndicator
    refine congrArg bitInt (decide_eq_decide.mpr ?_)
    constructor
    · intro h
      funext j
      have hj := h j
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      exact Prod.ext (Fin.ext hj.1.symm) (Fin.ext hj.2.symm)
    · intro h j
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨rfl, rfl⟩
  unfold entryVal symGroups
  rw [List.map_append, List.prod_append, List.map_map]
  simp only [Function.comp_def]
  rw [hF, hS, ListMachine.bitInt_and]

section SymCall
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

theorem symEntry_prod (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (t : SeedFix.SymIndex I hs Cs carriers)
    (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)))
    (G : ℕ) (σ : ℕ → Bool)
    (hσ : ∀ gi < (symPool Cs carriers).length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex G (SeedFix.cellNumC x) k gi) =
        corners ((symPool Cs carriers).getD gi dGate).eval c.1
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv _).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv _).symm x.2)) k) :
    entryVal (symGroups Cs carriers (I.filterParams .sym n) t.1.1 (symListParams I n a Cs carriers) t.1.2
      (symM (I.starParams n hs) Cs) t.2 G (SeedFix.cellNumC x) n) σ =
      bitZ (SeedFix.symStateBits I hs Cs carriers translation c t x) :=
  symEntry_prod_gen (I.starParams n hs) _ Cs carriers _ t.1.1 _ t.1.2 t.2 c.1 c.2 _ _ G _ n σ hσ

end SymCall

/-! ## The FILTER rows of any pool with the carrier prefix -/

theorem prefix_carrier {n : ℕ} (carriers : List (Carrier n)) (rest : List (List (NormalizedThresholdGate n)))
    (j : ℕ) (hj : j < carriers.length) : (carriers.map maskGates ++ rest).getD j [] = maskGates (carriers.getD j []) := by
  rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ hj, List.getElem_map]

theorem filtRows_prod (P : StarParams) (σt : P.Translation) (carriers : List (Carrier P.n))
    (rest : List (List (NormalizedThresholdGate P.n))) (FP : GapParams) (e : GapSeed FP) (c : BitInput P.n)
    (hc : P.IsCenter σt c) (u v : P.Errors) (G row nw : ℕ) (σ : ℕ → Bool)
    (hσ : ∀ gi < (carriers.map maskGates ++ rest).flatten.length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex G row k gi) =
        corners ((carriers.map maskGates ++ rest).flatten.getD gi dGate).eval c (P.errorVector P.leftBlock u)
          (P.errorVector P.rightBlock v) k) :
    ((List.range carriers.length).map fun j => groupVal [filtRow (carriers.map maskGates ++ rest) FP e G row nw j] σ).prod =
      bitInt (maskBits P σt carriers FP e (P.point c u v)) := by
  rw [maskBits_point P hc u v carriers FP e, ← bitInt_all]
  conv_rhs => rw [← range_map_getD carriers []]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < carriers.length := List.mem_range.mp hj
  have hjs : j < (carriers.map maskGates ++ rest).length := by simp only [List.length_append, List.length_map]; omega
  unfold groupVal filtRow
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  show bitInt (gapFilter FP e (popBits true (ListMachine.Row.readX
    (4 * ((carriers.map maskGates ++ rest).getD j []).length)
    (CompilerMachine.Pool.labsOf G row (sliceGis (carriers.map maskGates ++ rest) j)) σ))) = _
  rw [readX_slice _ j hjs G row σ c _ _ hσ, gapFilter_eq_filterBits, prefix_carrier carriers rest j hj']

/-! ## T's aux hash rows -/

theorem prefix_length {n : ℕ} (carriers : List (Carrier n)) :
    (carriers.map maskGates).flatten.length = 2 * (carriers.map List.length).sum := by
  induction carriers with
  | nil => rfl
  | cons X rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons, ih]
    have : (maskGates X).length = 2 * X.length := by
      unfold maskGates
      rw [List.length_flatMap]
      simp [List.map_const', List.sum_replicate]; ring
    rw [this]; ring

theorem range_map_prefix {α : Type} (l r : List α) (d : α) :
    (List.range l.length).map (fun gi => (l ++ r).getD gi d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1]

/-- **The aux FILTER row of seed `e'`** (T's HASH batch): the thrAux filter over the pool's carrier prefix
(gates `0 … 2Σ|X_j| − 1`). -/
def hashRow (P : StarParams) (carriers : List (Carrier P.n)) (FP : GapParams) (e : ℕ)
    (e' : GapSeed (Primitive.thrAux P carriers FP e)) (G row nw : ℕ) : RowReq :=
  .filt ⟨Primitive.thrAux P carriers FP e, e', ⟨2 * (carriers.map List.length).sum, true,
    CompilerMachine.Pool.labsOf G row (List.range (2 * (carriers.map List.length).sum)), nw⟩⟩

theorem hashRow_val (P : StarParams) (carriers : List (Carrier P.n)) (rest : List (List (NormalizedThresholdGate P.n)))
    (FP : GapParams) (e : ℕ) (e' : GapSeed (Primitive.thrAux P carriers FP e)) (c : BitInput P.n) (u v : P.Errors)
    (G row nw : ℕ) (σ : ℕ → Bool)
    (hσ : ∀ gi < (carriers.map maskGates ++ rest).flatten.length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex G row k gi) =
        corners ((carriers.map maskGates ++ rest).flatten.getD gi dGate).eval c (P.errorVector P.leftBlock u)
          (P.errorVector P.rightBlock v) k) :
    (hashRow P carriers FP e e' G row nw).val σ =
      bitInt (gapFilter (Primitive.thrAux P carriers FP e) e' (Primitive.thrZres P carriers c u v)) := by
  have hL := prefix_length carriers
  have hlt : ∀ gi ∈ List.range (2 * (carriers.map List.length).sum),
      gi < (carriers.map maskGates ++ rest).flatten.length := by
    intro gi hgi
    rw [List.mem_range] at hgi
    rw [List.flatten_append, List.length_append]; omega
  show bitInt (gapFilter (Primitive.thrAux P carriers FP e) e' (popBits true (ListMachine.Row.readX
    (4 * (2 * (carriers.map List.length).sum))
    (CompilerMachine.Pool.labsOf G row (List.range (2 * (carriers.map List.length).sum))) σ))) = _
  have hlen : 4 * (2 * (carriers.map List.length).sum) =
      4 * (List.range (2 * (carriers.map List.length).sum)).length := by
    rw [List.length_range]
  rw [hlen, readX_labsOf G row _ σ (fun gi => ((carriers.map maskGates ++ rest).flatten.getD gi dGate).eval) c _ _
    (fun gi hgi k => hσ gi (hlt gi hgi) k)]
  have hmap : (List.range (2 * (carriers.map List.length).sum)).map
      (fun gi => ((carriers.map maskGates ++ rest).flatten.getD gi dGate).eval) =
      ((carriers.map maskGates).flatten).map NormalizedThresholdGate.eval := by
    have h1 : (List.range (2 * (carriers.map List.length).sum)).map
        (fun gi => ((carriers.map maskGates ++ rest).flatten.getD gi dGate).eval) =
        ((List.range (2 * (carriers.map List.length).sum)).map
          (fun gi => (carriers.map maskGates ++ rest).flatten.getD gi dGate)).map NormalizedThresholdGate.eval := by
      rw [List.map_map]; rfl
    rw [h1, ← hL, List.flatten_append, range_map_prefix]
  have hz : ∀ cs : List (Carrier P.n), ((cs.map maskGates).flatten.map NormalizedThresholdGate.eval).map
      (fun T => residualPlus T c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)) =
      cs.flatMap (fun X => Carrier.residualBits X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)) := by
    intro cs
    induction cs with
    | nil => rfl
    | cons X cs ih =>
      rw [List.map_cons, List.flatten_cons, List.map_append, List.map_append, ih, List.flatMap_cons,
        residualBits_eq_pop, (popBits_cornerWord _ c _ _).1]
  rw [hmap, (popBits_cornerWord _ c _ _).1]
  unfold Primitive.thrZres
  rw [hz carriers]

/-! ## The THR entry -/

section Thr
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPrime
variable (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Carrier P.n)) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)

/-- The THR pool slices: each carrier's doubled atoms, then the tuple's bottom occurrences. -/
def thrSlices : List (List (NormalizedThresholdGate P.n)) :=
  carriers.map maskGates ++ [(thrOccs P Cs).map (·.gate)]

/-- The THR pool. -/
def thrPool : List (NormalizedThresholdGate P.n) := (thrSlices P Cs carriers).flatten

/-- `oOff`: the offset of the occurrence slice (`= 2Σ|X_j|`, `thrOff_eq`). -/
def thrOff : ℕ := sliceOff (thrSlices P Cs carriers) carriers.length

theorem thrOff_eq : thrOff P Cs carriers = 2 * (carriers.map List.length).sum := by
  unfold thrOff sliceOff thrSlices
  rw [List.take_left' (by simp), ← prefix_length carriers, List.length_flatten, List.map_map]

def thrDigGis (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (d : Fin (thrDigits P Cs algorithm den)) : List ℕ :=
  (List.finRange (thrOccs P Cs).length).flatMap fun i =>
    List.replicate (digitOf (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val 2 (thrDigits P Cs algorithm den) i d)
      (thrOff P Cs carriers + i)

/-- The RADIX row's digit data: per digit, the occurrence count and the corner labels. -/
def thrDigs (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (G row : ℕ) :
    List ListMachine.Row.Dig :=
  List.ofFn fun d => ((thrDigGis P Cs carriers algorithm den g pr d).length,
    CompilerMachine.Pool.labsOf G row (thrDigGis P Cs carriers algorithm den g pr d))

/-- The RADIX row of `(g, p, s)` over the fixed hash's list data `D`, radix `b_0 = 2`. -/
def radRow (D : ListData) (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val)
    (G row nw : ℕ) : RowReq :=
  .rad ⟨D, thrDigs P Cs carriers algorithm den g pr G row, pr.val, 2, s.val, nw⟩

/-- **The THR entry's printed rows**: `R = |carriers| + 1`, the FILTER rows then the RADIX row. -/
def thrGroups (FP : GapParams) (e : GapSeed FP) (D : ListData) (g : ThrEq P Cs algorithm)
    (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val) (G row nw : ℕ) : List (List RowReq) :=
  (List.range carriers.length).map (fun j => [filtRow (thrSlices P Cs carriers) FP e G row nw j]) ++
    [[radRow P Cs carriers algorithm den D g pr s G row nw]]

theorem thrGroups_length (FP : GapParams) (e : GapSeed FP) (D : ListData) (g : ThrEq P Cs algorithm)
    (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val) (G row nw : ℕ) :
    (thrGroups P Cs carriers algorithm den FP e D g pr s G row nw).length = carriers.length + 1 := by
  simp [thrGroups]

theorem tupleResidue_len (p b0 : ℕ) {m m' : ℕ} (h : m = m') (f g : ℕ → ℕ) :
    Rows.tupleResidue p b0 (fun d : Fin m => f d) (fun d : Fin m => g d) =
      Rows.tupleResidue p b0 (fun d : Fin m' => f d) (fun d : Fin m' => g d) := by
  subst h; rfl

theorem thrRepAt (D : ListData) (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (c : BitInput P.n) (u v : P.Errors) (G row : ℕ) (σ : ℕ → Bool)
    (hσ : ∀ gi < (thrPool P Cs carriers).length, ∀ k : Fin 4, σ (CompilerMachine.Pool.poolIndex G row k gi) =
      corners ((thrPool P Cs carriers).getD gi dGate).eval c (P.errorVector P.leftBlock u)
        (P.errorVector P.rightBlock v) k)
    (sgn : Bool) (d : Fin (thrDigits P Cs algorithm den)) :
    ListMachine.Row.repAt D (thrDigs P Cs carriers algorithm den g pr G row) sgn σ d =
      ListFast.listReportFast D (thrDigitPop P Cs algorithm den g pr d sgn c u v) := by
  have hj : carriers.length < (thrSlices P Cs carriers).length := by simp [thrSlices]
  have hsl : (thrSlices P Cs carriers).getD carriers.length [] = (thrOccs P Cs).map (·.gate) := by
    unfold thrSlices
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hT : ∀ i : Fin (thrOccs P Cs).length,
      (thrPool P Cs carriers).getD (thrOff P Cs carriers + i) dGate = ((thrOccs P Cs).get i).gate := by
    intro i
    unfold thrPool thrOff
    rw [getD_flatten_slice _ dGate _ hj i (by rw [hsl]; simp), hsl, List.getD_eq_getElem _ _ (by simp),
      List.getElem_map, List.get_eq_getElem]
  have hlt : ∀ gi ∈ thrDigGis P Cs carriers algorithm den g pr d, gi < (thrPool P Cs carriers).length := by
    intro gi hgi
    unfold thrDigGis at hgi
    rw [List.mem_flatMap] at hgi
    obtain ⟨i, _, hi⟩ := hgi
    rw [(List.mem_replicate.mp hi).2]
    have h := sliceOff_add_le (thrSlices P Cs carriers) carriers.length hj
    rw [hsl, List.length_map] at h
    unfold thrPool thrOff
    omega
  unfold ListMachine.Row.repAt ListMachine.Row.digAt thrDigs
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp only []
  rw [readX_labsOf G row _ σ (fun gi => ((thrPool P Cs carriers).getD gi dGate).eval) c _ _
    (fun gi hgi k => hσ gi (hlt gi hgi) k), ListFast.listReport_eq_fast]
  congr 1
  unfold thrDigitPop digitPop thrDigGis
  cases sgn
  · rw [(popBits_cornerWord _ c _ _).2, List.map_map, List.map_flatMap]
    simp only [Bool.false_eq_true, if_false]
    refine List.flatMap_congr fun i _ => ?_
    rw [List.map_replicate]
    simp only [Function.comp_apply, hT]
    rfl
  · rw [(popBits_cornerWord _ c _ _).1, List.map_map, List.map_flatMap]
    simp only [if_true]
    refine List.flatMap_congr fun i _ => ?_
    rw [List.map_replicate]
    simp only [Function.comp_apply, hT]
    rfl

theorem radRow_val (D : ListData) (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (s : ZMod pr.val) (c : BitInput P.n) (u v : P.Errors) (G row nw : ℕ) (σ : ℕ → Bool)
    (hσ : ∀ gi < (thrPool P Cs carriers).length, ∀ k : Fin 4, σ (CompilerMachine.Pool.poolIndex G row k gi) =
      corners ((thrPool P Cs carriers).getD gi dGate).eval c (P.errorVector P.leftBlock u)
        (P.errorVector P.rightBlock v) k) :
    (radRow P Cs carriers algorithm den D g pr s G row nw).val σ =
      bitInt (decide (thrResHat P Cs algorithm den (ListFast.listReportFast D) g pr c u v = s)) := by
  have hp : NeZero pr.val := ⟨(mem_primesUpTo.mp pr.2).1.ne_zero⟩
  show bitInt (decide (Rows.tupleResidue pr.val 2
      (fun d : Fin (thrDigs P Cs carriers algorithm den g pr G row).length =>
        ListMachine.Row.repAt D (thrDigs P Cs carriers algorithm den g pr G row) true σ d)
      (fun d : Fin (thrDigs P Cs carriers algorithm den g pr G row).length =>
        ListMachine.Row.repAt D (thrDigs P Cs carriers algorithm den g pr G row) false σ d) =
      ((s.val : ℕ) : ZMod pr.val))) = _
  rw [ZMod.natCast_zmod_val, tupleResidue_len pr.val 2 (by simp [thrDigs] : (thrDigs P Cs carriers algorithm den g pr
    G row).length = thrDigits P Cs algorithm den)]
  unfold thrResHat
  simp only [thrRepAt P Cs carriers algorithm den D g pr c u v G row σ hσ]

/-- **The THR product lemma, generic form**: at every assignment whose row atoms are the corners of the THR pool at
`(c, U_u, V_v)`, the entry's printed rows multiply to `bitInt (mask && [ŝ_{g,p} = s])`. -/
theorem thrEntry_prod_gen (σt : P.Translation) (FP : GapParams) (e : GapSeed FP) (D : ListData)
    (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val) (c : BitInput P.n)
    (hc : P.IsCenter σt c) (u v : P.Errors) (G row nw : ℕ) (σ : ℕ → Bool)
    (hσ : ∀ gi < (thrPool P Cs carriers).length, ∀ k : Fin 4, σ (CompilerMachine.Pool.poolIndex G row k gi) =
      corners ((thrPool P Cs carriers).getD gi dGate).eval c (P.errorVector P.leftBlock u)
        (P.errorVector P.rightBlock v) k) :
    entryVal (thrGroups P Cs carriers algorithm den FP e D g pr s G row nw) σ =
      bitInt (maskBits P σt carriers FP e (P.point c u v) &&
        decide (thrResHat P Cs algorithm den (ListFast.listReportFast D) g pr c u v = s)) := by
  unfold entryVal thrGroups
  rw [List.map_append, List.prod_append, List.map_map]
  simp only [Function.comp_def]
  have hF : ((List.range carriers.length).map fun j =>
      groupVal [filtRow (thrSlices P Cs carriers) FP e G row nw j] σ).prod =
      bitInt (maskBits P σt carriers FP e (P.point c u v)) := filtRows_prod P σt carriers _ FP e c hc u v G row nw σ hσ
  rw [hF]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  unfold groupVal
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [radRow_val P Cs carriers algorithm den D g pr s c u v G row nw σ hσ, ListMachine.bitInt_and]

end Thr

section ThrCall
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- The THR call's fixed-hash list data `D` (the rational greedy's bits, `thrHashBits`): the RADIX rows' `ListData`. -/
def thrCallD (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) : ListData :=
  MajorantBits.dataBits
    (thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs)
      (thrCallE algorithm I hs Cs carriers) (thrCallT algorithm I hs Cs carriers) (thrCallJ algorithm I hs Cs carriers))
    (thrHashBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
      (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs) (thrCallE algorithm I hs Cs carriers)
      (thrCallT algorithm I hs Cs carriers) (thrCallJ algorithm I hs Cs carriers))

theorem thrCallReport_eq_D (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) :
    thrCallReportBits algorithm I hs Cs carriers translation =
      ListFast.listReportFast (thrCallD algorithm I hs Cs carriers translation) := rfl

/-- **The THR product lemma** (`row:matrix`): at every assignment whose star-row `cellNumC x` atoms are the
corners of the THR pool at `(c, U_x, V_x)`, the entry's printed rows (FILTER rows, then the RADIX row over the fixed
hash's list data) multiply to the state matrix bit `D_{e,g,p,s}(c)(x) = thrStateBits` — C4's `sampTerms_eval`
hypothesis `hD` at the entry. -/
theorem thrEntry_prod (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (t : SeedFix.ThrIndex algorithm I hs Cs)
    (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)))
    (G : ℕ) (σ : ℕ → Bool)
    (hσ : ∀ gi < (thrPool (I.starParams n hs) Cs carriers).length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex G (SeedFix.cellNumC x) k gi) =
        corners ((thrPool (I.starParams n hs) Cs carriers).getD gi dGate).eval c.1
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv _).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv _).symm x.2)) k) :
    entryVal (thrGroups (I.starParams n hs) Cs carriers algorithm (thrCallDen algorithm I hs Cs) (I.filterParams .thr n)
      t.1 (thrCallD algorithm I hs Cs carriers translation) t.2.1 t.2.2.1 t.2.2.2 G (SeedFix.cellNumC x) n) σ =
      bitZ (SeedFix.thrStateBits algorithm I hs Cs carriers translation c t x) :=
  thrEntry_prod_gen (I.starParams n hs) Cs carriers algorithm _ _ _ t.1 _ t.2.1 t.2.2.1 t.2.2.2 c.1 c.2 _ _ G _ n σ hσ

end ThrCall

end NearCubicWires.WireExponent3_5.PrimAsm.Records
