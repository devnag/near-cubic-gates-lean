import Proof.Wire_3_5.PrimAsmRecords

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records

/-! ## Uniform-length flattening -/

theorem getD_flatMap_uniform {α β : Type} (l : List α) (f : α → List β) (R : ℕ) (hR : ∀ a ∈ l, (f a).length = R)
    (d : β) (a : α) (i r : ℕ) (hi : i < l.length) (hr : r < R) (d' : α) (ha : l.getD i d' = a) :
    (l.flatMap f).getD (i * R + r) d = (f a).getD r d := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    have hx : (f x).length = R := hR x List.mem_cons_self
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at ha
      subst ha
      rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by omega)]
    | succ i =>
      simp only [List.getD_cons_succ] at ha
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      rw [List.getD_append_right _ _ _ _ (by rw [hx]; nlinarith)]
      rw [show (i + 1) * R + r - (f x).length = i * R + r by rw [hx, Nat.succ_mul]; omega]
      exact ih (fun b hb => hR b (List.mem_cons_of_mem x hb)) i hi ha

/-! ## The batch -/

/-- **The batch** of `nT` states over `N²` cells: entry `(t, row)` is `grp t row` (its `R` printed rows), in C4's
state-major order. -/
def batchOf (nT N : ℕ) (grp : ℕ → ℕ → List (List RowReq)) : List (List RowReq) :=
  (List.range (nT * N ^ 2)).flatMap fun q => grp (q / N ^ 2) (q % N ^ 2)

theorem batchOf_getD (nT N R : ℕ) (grp : ℕ → ℕ → List (List RowReq)) (hR : ∀ t row, (grp t row).length = R)
    (t row r : ℕ) (ht : t < nT) (hrow : row < N ^ 2) (hr : r < R) :
    (batchOf nT N grp).getD ((t * N ^ 2 + row) * R + r) [] = (grp t row).getD r [] := by
  have hq : t * N ^ 2 + row < nT * N ^ 2 := by nlinarith
  unfold batchOf
  rw [getD_flatMap_uniform (List.range (nT * N ^ 2)) _ R (fun q _ => hR _ _) [] (t * N ^ 2 + row)
    (t * N ^ 2 + row) r (by simpa using hq) hr 0 (by rw [List.getD_eq_getElem _ _ (by simpa using hq),
      List.getElem_range])]
  have hN : 0 < N ^ 2 := by
    rcases Nat.eq_zero_or_pos (N ^ 2) with h | h
    · rw [h] at hrow; omega
    · exact h
  rw [show (t * N ^ 2 + row) / N ^ 2 = t by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hrow, Nat.zero_add],
    show (t * N ^ 2 + row) % N ^ 2 = row by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrow]]

theorem cellNumC_lt {N : ℕ} (c : Fin N × Fin N) : SeedFix.cellNumC c < N ^ 2 := by
  unfold SeedFix.cellNumC
  have h1 := c.1.isLt
  have h2 := c.2.isLt
  nlinarith

theorem entry_pos (N t : ℕ) (c : Fin N × Fin N) :
    (t * N + (c.1 : ℕ)) * N + c.2 = t * N ^ 2 + SeedFix.cellNumC c := by
  unfold SeedFix.cellNumC
  ring

theorem forall2_getD (bl : List (List RowReq)) (Vs : List (IntExpression ℕ))
    (hV : List.Forall₂ (fun g V => ∀ σ, IntExpression.eval V σ = groupVal g σ) bl Vs) (σ : ℕ → Bool) :
    ∀ i, IntExpression.eval (Vs.getD i []) σ = groupVal (bl.getD i []) σ := by
  induction hV with
  | nil => intro i; simp only [List.getD_nil]; rfl
  | cons h _ ih =>
    intro i
    cases i with
    | zero => exact h σ
    | succ i => exact ih i

/-- **The entry rows of the batch's expressions multiply to the entry's value**, whenever each expression meets its
printed row (a missing position reads `[]`, value `0`, on both sides). -/
theorem batch_entry (nT N R : ℕ) (grp : ℕ → ℕ → List (List RowReq)) (hR : ∀ t row, (grp t row).length = R)
    (Vs : List (IntExpression ℕ))
    (hV : List.Forall₂ (fun g V => ∀ σ, IntExpression.eval V σ = groupVal g σ) (batchOf nT N grp) Vs)
    (σ : ℕ → Bool) (t : ℕ) (ht : t < nT) (c : Fin N × Fin N) :
    ((SeedFix.entryRows Vs R N t c.1 c.2).map fun V => IntExpression.eval V σ).prod =
      entryVal (grp t (SeedFix.cellNumC c)) σ := by
  have hget := forall2_getD _ Vs hV σ
  unfold SeedFix.entryRows entryVal
  rw [List.map_map, entry_pos N t c]
  have hrow := cellNumC_lt c
  rw [← range_map_getD (grp t (SeedFix.cellNumC c)) [] (fun g => groupVal g σ), hR t (SeedFix.cellNumC c)]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  have hr' : r < R := List.mem_range.mp hr
  simp only [Function.comp_apply]
  rw [hget, batchOf_getD nT N R grp hR t _ r ht hrow hr']

/-! ## The printed column value over an enumeration -/

theorem sampElim_reindex (P : Sampler.SeedParams) {T : Type} [Fintype T] (nT : ℕ) (e : Fin nT ≃ T)
    (Dz : T → Fin P.N × Fin P.N → Bool) (plen pre : ℕ) :
    SeedFix.sampElim P (fun t => Dz (e t)) plen pre = SeedFix.sampElim P Dz plen pre := by
  unfold SeedFix.sampElim
  exact Fintype.sum_equiv e _ _ (fun t => rfl)

/-! ## The SYM and THR batches -/

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- **The SYM batch** over the enumeration `enum` of the states `((e, e'), τ)`. -/
def symBatch (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (nT : ℕ)
    (enum : ℕ → SeedFix.SymIndex I hs Cs carriers) (G : ℕ) : List (List RowReq) :=
  batchOf nT (2 ^ SeedFix.callKh (I.starParams n hs)) fun t row =>
    symGroups Cs carriers (I.filterParams .sym n) (enum t).1.1 (symListParams I n a Cs carriers) (enum t).1.2
      (symM (I.starParams n hs) Cs) (enum t).2 G row n

/-- **The SYM batch meets `sampTerms_eval`'s `hD`**: at every column assignment `σ` (the corners of the SYM pool at
every star row), the entry rows of `(t, x)` in the batch's expressions multiply to `bitZ (symStateBits (enum t) x)`. -/
theorem symBatch_hD (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (nT : ℕ) (enum : ℕ → SeedFix.SymIndex I hs Cs carriers) (G : ℕ) (Vs : List (IntExpression ℕ))
    (hV : List.Forall₂ (fun g V => ∀ σ, IntExpression.eval V σ = groupVal g σ)
      (symBatch I hs Cs carriers nT enum G) Vs)
    (σ : ℕ → Bool)
    (hσ : ∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)),
      ∀ gi < (symPool Cs carriers).length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex G (SeedFix.cellNumC x) k gi) =
        corners ((symPool Cs carriers).getD gi dGate).eval c.1
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv _).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv _).symm x.2)) k)
    (t : Fin nT) (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs))) :
    ((SeedFix.entryRows Vs (carriers.length + 2 * a) (2 ^ SeedFix.callKh (I.starParams n hs)) t x.1 x.2).map
      fun V => IntExpression.eval V σ).prod =
      bitZ (SeedFix.symStateBits I hs Cs carriers translation c (enum t) x) := by
  rw [batch_entry nT _ (carriers.length + 2 * a) _ (fun t row => symGroups_length _ _ _ _ _ _ _ _ _ _ _) Vs hV σ t
    t.isLt x]
  exact symEntry_prod I hs Cs carriers translation c (enum t) x G σ (hσ x)

/-- **The THR batch** over the enumeration `enum` of the states `(e, g, p, s)`, with the fixed hash's list data. -/
def thrBatch (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (nT : ℕ) (enum : ℕ → SeedFix.ThrIndex algorithm I hs Cs) (G : ℕ) : List (List RowReq) :=
  batchOf nT (2 ^ SeedFix.callKh (I.starParams n hs)) fun t row =>
    thrGroups (I.starParams n hs) Cs carriers algorithm (thrCallDen algorithm I hs Cs) (I.filterParams .thr n)
      (enum t).1 (thrCallD algorithm I hs Cs carriers translation) (enum t).2.1 (enum t).2.2.1 (enum t).2.2.2 G row n

/-- **The THR batch meets `sampTerms_eval`'s `hD`** (as `symBatch_hD`, at `bitZ (thrStateBits (enum t) x)`). -/
theorem thrBatch_hD (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (nT : ℕ) (enum : ℕ → SeedFix.ThrIndex algorithm I hs Cs) (G : ℕ) (Vs : List (IntExpression ℕ))
    (hV : List.Forall₂ (fun g V => ∀ σ, IntExpression.eval V σ = groupVal g σ)
      (thrBatch algorithm I hs Cs carriers translation nT enum G) Vs)
    (σ : ℕ → Bool)
    (hσ : ∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)),
      ∀ gi < (thrPool (I.starParams n hs) Cs carriers).length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex G (SeedFix.cellNumC x) k gi) =
        corners ((thrPool (I.starParams n hs) Cs carriers).getD gi dGate).eval c.1
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv _).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv _).symm x.2)) k)
    (t : Fin nT) (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs))) :
    ((SeedFix.entryRows Vs (carriers.length + 1) (2 ^ SeedFix.callKh (I.starParams n hs)) t x.1 x.2).map
      fun V => IntExpression.eval V σ).prod =
      bitZ (SeedFix.thrStateBits algorithm I hs Cs carriers translation c (enum t) x) := by
  rw [batch_entry nT _ (carriers.length + 1) _ (fun t row => thrGroups_length _ _ _ _ _ _ _ _ _ _ _ _ _ _) Vs hV
    σ t t.isLt x]
  exact thrEntry_prod algorithm I hs Cs carriers translation c (enum t) x G σ (hσ x)

end Call

/-! ## T's HASH batch -/

/-- **The HASH batch**: per cell (in `cellNum` order) the aux FILTER rows of the `nE` aux seeds `enumE e'`; row
`row·nE + e'`. -/
def hashBatch (P : StarParams) (carriers : List (Carrier P.n)) (FP : GapParams) (e : ℕ) (N nE : ℕ)
    (enumE : ℕ → GapSeed (Primitive.thrAux P carriers FP e)) (G nw : ℕ) : List RowReq :=
  (List.range (N ^ 2 * nE)).map fun q => hashRow P carriers FP e (enumE (q % nE)) G (q / nE) nw

/-- **The HASH batch's values** (for C4.Hb): whenever the expressions meet the rows, the expression at
`cellNumC x·nE + e'` is the aux filter `F_{enumE e'}` on the named carriers' residual vector at the cell's pair. -/
theorem hashBatch_val (P : StarParams) (carriers : List (Carrier P.n)) (rest : List (List (NormalizedThresholdGate P.n)))
    (FP : GapParams) (e : ℕ) (N nE : ℕ) (enumE : ℕ → GapSeed (Primitive.thrAux P carriers FP e)) (G nw : ℕ)
    (eqv : P.Errors ≃ Fin N) (c : BitInput P.n) (Vs : List (IntExpression ℕ))
    (hV : List.Forall₂ RowReq.Meets (hashBatch P carriers FP e N nE enumE G nw) Vs) (σ : ℕ → Bool)
    (hσ : ∀ x : Fin N × Fin N, ∀ gi < (carriers.map maskGates ++ rest).flatten.length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex G (SeedFix.cellNumC x) k gi) =
        corners ((carriers.map maskGates ++ rest).flatten.getD gi dGate).eval c
          (P.errorVector P.leftBlock (eqv.symm x.1)) (P.errorVector P.rightBlock (eqv.symm x.2)) k)
    (x : Fin N × Fin N) (e' : Fin nE) :
    IntExpression.eval (Vs.getD (SeedFix.cellNumC x * nE + e') []) σ =
      bitInt (gapFilter (Primitive.thrAux P carriers FP e) (enumE e')
        (Primitive.thrZres P carriers c (eqv.symm x.1) (eqv.symm x.2))) := by
  have hq : SeedFix.cellNumC x * nE + e' < N ^ 2 * nE := by
    have h1 := cellNumC_lt x
    have h2 := e'.isLt
    nlinarith
  have hlen := hV.length_eq
  have hlenB : (hashBatch P carriers FP e N nE enumE G nw).length = N ^ 2 * nE := by simp [hashBatch]
  have hi : SeedFix.cellNumC x * nE + e' < Vs.length := by rw [← hlen, hlenB]; exact hq
  rw [List.getD_eq_getElem _ _ hi]
  have hm := (List.forall₂_iff_get.mp hV).2 (SeedFix.cellNumC x * nE + e') (by rw [hlenB]; exact hq) hi
  rw [List.get_eq_getElem, List.get_eq_getElem] at hm
  rw [hm σ]
  have hb : (hashBatch P carriers FP e N nE enumE G nw)[SeedFix.cellNumC x * nE + e'] =
      hashRow P carriers FP e (enumE e') G (SeedFix.cellNumC x) nw := by
    unfold hashBatch
    rw [List.getElem_map, List.getElem_range]
    have hE : 0 < nE := by have := e'.isLt; omega
    rw [show (SeedFix.cellNumC x * nE + e') % nE = e' by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt e'.isLt],
      show (SeedFix.cellNumC x * nE + e') / nE = SeedFix.cellNumC x by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hE, Nat.div_eq_of_lt e'.isLt, Nat.zero_add]]
  rw [hb]
  exact hashRow_val P carriers rest FP e (enumE e') c _ _ G _ nw σ (hσ x)

end NearCubicWires.WireExponent3_5.PrimAsm.Batch
