import Proof.Wire_3_5.PrimAsmEnum
import Proof.Wire_3_5.SeedFixJLink

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-! ## The printed expressions -/

/-- **The C2 reference expression of a request** (what its certified row machine prints). -/
def refOf : RowReq → IntExpression ℕ
  | .filt r => ListMachine.Row.filtRefC r.tbl r.thr r.L r.sgn r.labs
  | .pop r => ListMachine.Row.popRefC r.P r.e r.L r.sgn r.labs r.s
  | .rad r => ListMachine.Row.radRefC r.D r.digs r.p r.b0 r.s

/-- A printed row's expression: its requests' expressions concatenated. -/
def groupExpr (g : List RowReq) : IntExpression ℕ := (g.map refOf).flatten

/-- The batch's expressions, one per printed row. -/
def batchExprs (bl : List (List RowReq)) : List (IntExpression ℕ) := bl.map groupExpr

theorem batch_meets (bl : List (List RowReq)) (h : ∀ g ∈ bl, ∀ r ∈ g, r.Meets (refOf r)) :
    List.Forall₂ (fun g V => ∀ σ, IntExpression.eval V σ = groupVal g σ) bl (batchExprs bl) := by
  unfold batchExprs
  induction bl with
  | nil => exact List.Forall₂.nil
  | cons g bl ih =>
    refine List.Forall₂.cons ?_ (ih fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
    intro σ
    apply groupExpr_eval
    have hg := h g List.mem_cons_self
    clear h ih
    induction g with
    | nil => exact List.Forall₂.nil
    | cons r g ih => exact List.Forall₂.cons (hg r List.mem_cons_self) (ih fun r' hr' => hg r' (List.mem_cons_of_mem r hr'))

/-! ## Each request's expression meets its errSpec -/

theorem filt_meets' (r : ListMachine.Row.FiltReq) : (RowReq.filt r).Meets (refOf (.filt r)) :=
  fun σ => ListMachine.Row.filtRow_value r σ

theorem pop_meets' (r : ListMachine.Row.PopReq) (hlabs : 4 * r.L ≤ r.labs.length)
    (hnest : ∀ h j i, r.P.base.inLevel h (j + 1) i = true → r.P.base.inLevel h j i = true) :
    (RowReq.pop r).Meets (refOf (.pop r)) :=
  fun σ => (ListMachine.Row.popRow_run r.P r.e r.L r.sgn r.labs hlabs hnest r.s [] [] [] []).2.1 σ

theorem rad_meets' (r : ListMachine.Row.RadReq) (hp : r.p ≠ 0)
    (hnest : ∀ j i, r.D.inLevel (j + 1) i = true → r.D.inLevel j i = true) (hok : ListMachine.Row.DigsOk r.digs) :
    (RowReq.rad r).Meets (refOf (.rad r)) := by
  haveI : NeZero r.p := ⟨hp⟩
  intro σ
  exact ListMachine.Row.radExpr_value r.D hnest r.digs hok r.p r.b0 (r.s : ZMod r.p) σ

theorem inLevelBits_nest (MP : MajorantParams) (s : Fin (2 * MP.t * MP.ell0) → Bool) :
    ∀ j i, (MajorantBits.dataBits MP s).inLevel (j + 1) i = true → (MajorantBits.dataBits MP s).inLevel j i = true := by
  intro j i h
  show MajorantBits.inLevelBits MP s j i = true
  have h' : MajorantBits.inLevelBits MP s (j + 1) i = true := h
  unfold MajorantBits.inLevelBits at h' ⊢
  split_ifs at h' ⊢ with hi
  · simp only [decide_eq_true_eq] at h' ⊢
    exact fun b hb hbj => h' b hb (by omega)
  · rfl

theorem labsOf_slice {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (G row j : ℕ) :
    4 * (sl.getD j []).length ≤ (CompilerMachine.Pool.labsOf G row (sliceGis sl j)).length := by
  rw [labsOf_length, sliceGis_length]

theorem thrDigs_ok (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) (G row : ℕ) :
    ListMachine.Row.DigsOk (thrDigs P Cs carriers alg den g pr G row) := by
  intro dg hdg
  unfold thrDigs at hdg
  obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hdg
  simp only [labsOf_length]
  exact le_refl _

/-- **A RADIX row's expression meets its errSpec** (the list data nested, the prime nonzero, the digits covered). -/
theorem radRow_meets (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (D : ListData)
    (hD : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (g : Primitive.ThrEq P Cs alg)
    (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) (s : ZMod pr.val) (G row nw : ℕ) :
    (radRow P Cs carriers alg den D g pr s G row nw).Meets (refOf (radRow P Cs carriers alg den D g pr s G row nw)) := by
  unfold radRow
  exact rad_meets' _ (SupplierPrime.mem_primesUpTo.mp pr.2).1.ne_zero hD (thrDigs_ok P Cs carriers alg den g pr G row)

/-! ## The SYM tape -/

section Sym
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n))

/-- The SYM batch at the determined enumeration and the full pool. -/
def symBatchE : List (List RowReq) :=
  symBatch I hs Cs carriers (symNT I hs Cs carriers) (symEnum I hs Cs carriers) (symPool Cs carriers).length

/-- **The SYM batch's expressions** (C2's printed rows in C4's order). -/
def symExprs : List (IntExpression ℕ) := batchExprs (symBatchE I hs Cs carriers)

/-- The SYM entries (C4's `ents`). -/
def symEnts : List (List (IntExpression ℕ)) :=
  SeedFix.JLink.chunk (2 ^ SeedFix.callKh (I.starParams n hs)) (symNT I hs Cs carriers) (carriers.length + 2 * a)
    (symExprs I hs Cs carriers)

/-- **The SYM tape**: C4's `BAT` word of the call. -/
def symTape : List Bool := SeedFix.blockWord (symEnts I hs Cs carriers)

theorem symBatchE_meets : ∀ g ∈ symBatchE I hs Cs carriers, ∀ r ∈ g, r.Meets (refOf r) := by
  intro g hg r hr
  unfold symBatchE symBatch batchOf at hg
  obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hg
  unfold symGroups at hq
  rcases List.mem_append.mp hq with hf | hp
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
    rw [List.mem_singleton] at hr
    subst hr
    exact filt_meets' _
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;>
    · unfold popFactor at hr
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hr
      exact pop_meets' _ (labsOf_slice _ _ _ _) (fun h j i hh => BaseListParams.inLevel_nest _ h j i hh)

theorem sym_entsOk :
    SeedFix.JLink.EntsOk (2 ^ SeedFix.callKh (I.starParams n hs)) (symNT I hs Cs carriers) (carriers.length + 2 * a)
      (symExprs I hs Cs carriers) (symEnts I hs Cs carriers) :=
  SeedFix.JLink.chunk_ok _ _ _ _

/-- **The SYM tape's entries meet `sampTerms_eval`'s `hD`**: at every column assignment (the corners of the SYM pool
at every star row), the entry rows of `(t, x)` multiply to `bitZ (symStateBits (symEnum t) x)`. -/
theorem sym_hD (translation : List ℕ)
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c}) (σ : ℕ → Bool)
    (hσ : ∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)),
      ∀ gi < (symPool Cs carriers).length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex (symPool Cs carriers).length (SeedFix.cellNumC x) k gi) =
        corners ((symPool Cs carriers).getD gi dGate).eval c.1
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv _).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv _).symm x.2)) k)
    (t : Fin (symNT I hs Cs carriers))
    (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs))) :
    ((SeedFix.entryRows (symExprs I hs Cs carriers) (carriers.length + 2 * a) (2 ^ SeedFix.callKh (I.starParams n hs))
      t x.1 x.2).map fun V => IntExpression.eval V σ).prod =
      bitZ (SeedFix.symStateBits I hs Cs carriers translation c (symEnum I hs Cs carriers t) x) :=
  symBatch_hD I hs Cs carriers translation c _ _ _ _ (batch_meets _ (symBatchE_meets I hs Cs carriers)) σ hσ t x

end Sym

/-! ## The THR tape -/

section Thr
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- The entry `(t, row)` of the THR batch (states `t < thrNT`; blank rows past the end). -/
def thrGrp (t row : ℕ) : List (List RowReq) :=
  if h : t < thrNT alg I hs Cs then
    thrGroups (I.starParams n hs) Cs carriers alg (thrCallDen alg I hs Cs) (I.filterParams .thr n)
      ((thrIndexEquiv alg I hs Cs).symm ⟨t, h⟩).1 (thrCallD alg I hs Cs carriers translation)
      ((thrIndexEquiv alg I hs Cs).symm ⟨t, h⟩).2.1 ((thrIndexEquiv alg I hs Cs).symm ⟨t, h⟩).2.2.1
      ((thrIndexEquiv alg I hs Cs).symm ⟨t, h⟩).2.2.2 (thrPool (I.starParams n hs) Cs carriers).length row n
  else List.replicate (carriers.length + 1) []

theorem thrGrp_length (t row : ℕ) : (thrGrp alg I hs Cs carriers translation t row).length = carriers.length + 1 := by
  unfold thrGrp
  split_ifs
  · exact thrGroups_length _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact List.length_replicate

/-- The THR batch at the determined enumeration and the full pool. -/
def thrBatchE : List (List RowReq) :=
  batchOf (thrNT alg I hs Cs) (2 ^ SeedFix.callKh (I.starParams n hs)) (thrGrp alg I hs Cs carriers translation)

/-- **The THR batch's expressions.** -/
def thrExprs : List (IntExpression ℕ) := batchExprs (thrBatchE alg I hs Cs carriers translation)

/-- The THR entries (C4's `ents`). -/
def thrEnts : List (List (IntExpression ℕ)) :=
  SeedFix.JLink.chunk (2 ^ SeedFix.callKh (I.starParams n hs)) (thrNT alg I hs Cs) (carriers.length + 1)
    (thrExprs alg I hs Cs carriers translation)

/-- **The THR tape**: C4's `BAT` word of the call (the RADIX rows over the fixed hash's list data). -/
def thrTape : List Bool := SeedFix.blockWord (thrEnts alg I hs Cs carriers translation)

theorem thrBatchE_meets : ∀ g ∈ thrBatchE alg I hs Cs carriers translation, ∀ r ∈ g, r.Meets (refOf r) := by
  intro g hg r hr
  unfold thrBatchE batchOf at hg
  obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hg
  unfold thrGrp at hq
  split_ifs at hq with h
  · unfold thrGroups at hq
    rcases List.mem_append.mp hq with hf | hrad
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
      rw [List.mem_singleton] at hr
      subst hr
      exact filt_meets' _
    · rw [List.mem_singleton] at hrad
      subst hrad
      rw [List.mem_singleton] at hr
      subst hr
      exact radRow_meets _ _ _ _ _ _ (inLevelBits_nest _ _) _ _ _ _ _ _
  · obtain ⟨_, hrep⟩ := List.mem_replicate.mp hq
    subst hrep
    simp at hr

theorem thr_entsOk :
    SeedFix.JLink.EntsOk (2 ^ SeedFix.callKh (I.starParams n hs)) (thrNT alg I hs Cs) (carriers.length + 1)
      (thrExprs alg I hs Cs carriers translation) (thrEnts alg I hs Cs carriers translation) :=
  SeedFix.JLink.chunk_ok _ _ _ _

/-- **The THR tape's entries meet `sampTerms_eval`'s `hD`** at `bitZ (thrStateBits ((thrIndexEquiv).symm t) x)`. -/
theorem thr_hD
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c}) (σ : ℕ → Bool)
    (hσ : ∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)),
      ∀ gi < (thrPool (I.starParams n hs) Cs carriers).length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex (thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) k gi) =
        corners ((thrPool (I.starParams n hs) Cs carriers).getD gi dGate).eval c.1
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv _).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv _).symm x.2)) k)
    (t : Fin (thrNT alg I hs Cs))
    (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs))) :
    ((SeedFix.entryRows (thrExprs alg I hs Cs carriers translation) (carriers.length + 1)
      (2 ^ SeedFix.callKh (I.starParams n hs)) t x.1 x.2).map fun V => IntExpression.eval V σ).prod =
      bitZ (SeedFix.thrStateBits alg I hs Cs carriers translation c ((thrIndexEquiv alg I hs Cs).symm t) x) := by
  unfold thrExprs thrBatchE
  rw [batch_entry _ _ (carriers.length + 1) _ (thrGrp_length alg I hs Cs carriers translation) _
    (batch_meets _ (thrBatchE_meets alg I hs Cs carriers translation)) σ t t.isLt x]
  unfold thrGrp
  rw [dif_pos t.isLt]
  simp only [Fin.eta]
  exact thrEntry_prod alg I hs Cs carriers translation c ((thrIndexEquiv alg I hs Cs).symm t) x _ σ (hσ x)

end Thr

/-! ## T's HASH tape -/

section Hash
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))

/-- The aux filter's parameters at the call. -/
abbrev auxP : GapParams := thrAux (I.starParams n hs) carriers (I.filterParams .thr n) (thrCallE alg I hs Cs carriers)

/-- The number of aux seeds `nE = |GapSeed (thrAux …)|`. -/
abbrev nE : ℕ := Fintype.card (GapSeed (auxP alg I hs Cs carriers))

/-- The aux seeds in the determined enumeration. -/
def auxEnum (e' : ℕ) : GapSeed (auxP alg I hs Cs carriers) :=
  (gapSeedEquiv _).symm ⟨e' % nE alg I hs Cs carriers, Nat.mod_lt _ (card_gapSeed_pos _)⟩

/-- **The HASH rows' expressions**: per cell (in `cellNum` order) the aux FILTER rows of the `nE` aux seeds. -/
def hashExprs : List (IntExpression ℕ) :=
  (hashBatch (I.starParams n hs) carriers (I.filterParams .thr n) (thrCallE alg I hs Cs carriers)
    (2 ^ SeedFix.callKh (I.starParams n hs)) (nE alg I hs Cs carriers) (auxEnum alg I hs Cs carriers)
    (thrPool (I.starParams n hs) Cs carriers).length n).map refOf

/-- **The HASH tape**: one entry record per aux row, row `cellNumC x·nE + e'` (C4's `blockWord` format). -/
def hashTape : List Bool := SeedFix.blockWord ((hashExprs alg I hs Cs carriers).map fun V => [V])

/-- **The HASH rows' values** (for C4.Hb): at every column assignment of the THR pool, the expression at
`cellNumC x·nE + e'` is the aux filter `F_{e'}` on the named carriers' residual vector at the cell's pair. -/
theorem hash_val (c : BitInput (I.starParams n hs).n) (σ : ℕ → Bool)
    (hσ : ∀ x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)),
      ∀ gi < (thrPool (I.starParams n hs) Cs carriers).length, ∀ k : Fin 4,
      σ (CompilerMachine.Pool.poolIndex (thrPool (I.starParams n hs) Cs carriers).length (SeedFix.cellNumC x) k gi) =
        corners ((thrPool (I.starParams n hs) Cs carriers).getD gi dGate).eval c
          ((I.starParams n hs).errorVector (I.starParams n hs).leftBlock ((SeedFix.callEqv _).symm x.1))
          ((I.starParams n hs).errorVector (I.starParams n hs).rightBlock ((SeedFix.callEqv _).symm x.2)) k)
    (x : Fin (2 ^ SeedFix.callKh (I.starParams n hs)) × Fin (2 ^ SeedFix.callKh (I.starParams n hs)))
    (e' : Fin (nE alg I hs Cs carriers)) :
    IntExpression.eval ((hashExprs alg I hs Cs carriers).getD (SeedFix.cellNumC x * nE alg I hs Cs carriers + e') []) σ =
      bitInt (gapFilter (auxP alg I hs Cs carriers) (auxEnum alg I hs Cs carriers e')
        (thrZres (I.starParams n hs) carriers c ((SeedFix.callEqv _).symm x.1) ((SeedFix.callEqv _).symm x.2))) := by
  have hV : List.Forall₂ RowReq.Meets (hashBatch (I.starParams n hs) carriers (I.filterParams .thr n)
      (thrCallE alg I hs Cs carriers) (2 ^ SeedFix.callKh (I.starParams n hs)) (nE alg I hs Cs carriers)
      (auxEnum alg I hs Cs carriers) (thrPool (I.starParams n hs) Cs carriers).length n)
      (hashExprs alg I hs Cs carriers) := by
    unfold hashExprs hashBatch
    rw [List.map_map]
    refine List.forall₂_iff_get.mpr ⟨by simp, fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map, Function.comp_apply]
    exact filt_meets' _
  exact hashBatch_val (I.starParams n hs) carriers [(thrOccs (I.starParams n hs) Cs).map SupportedNormalizedGate.gate]
    (I.filterParams .thr n) (thrCallE alg I hs Cs carriers) _ _ _ _ n (SeedFix.callEqv _) c _ hV σ hσ x e'

end Hash

/-! ## The writers' machine types -/

/-- The writers' input bank: `frame w` on the input tape, every other tape blank. -/
def inBank {t : ℕ} (i : Fin t) (w : List Bool) : Fin t → List Bool := fun j => if j = i then frame w else []

/-- The writers' output bank: `frame w` kept on the input tape, the tape word `v` on the output tape, every other tape
blank. -/
def outBank {t : ℕ} (i o : Fin t) (w v : List Bool) : Fin t → List Bool :=
  fun j => if j = i then frame w else if j = o then v else []

/-- A clean writer machine on its own `t` tapes: from `inBank`, it halts at `outBank` with every head at `0`. -/
structure WriterStage where
  t : ℕ
  s : ℕ
  M : Machine t s
  inS : Fin t
  outS : Fin t
  hio : inS ≠ outS

section Writers
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EW : Envelope) (cW kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM batch writer** at one call family: `frame req.word ↦ symTape`, within the preprocessing class. -/
structure SymWriterAt extends WriterStage where
  ready : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ClockJoin.ReadyRun M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n))
        (inBank inS (symReq n a' ha' Cs carriers translation).word)
        (outBank inS outS (symReq n a' ha' Cs carriers translation).word
          (symTape (callInputs l F kclk coef A a ha) hs Cs carriers))

/-- **The THR batch writer**: `frame (req.word ++ frame hashBits) ↦ thrTape` (the hash is fixed first, C4.Hb). -/
structure ThrWriterAt extends WriterStage where
  ready : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ClockJoin.ReadyRun M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n))
        (inBank inS ((thrReq n a' ha' Cs carriers translation).word ++
          frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
            (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
            ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
            (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
            (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
            (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
            (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))))
        (outBank inS outS ((thrReq n a' ha' Cs carriers translation).word ++
          frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
            (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
            ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
            (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
            (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
            (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
            (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))))
          (thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation))

/-- **The HASH row writer** (for C4.Hb): `frame req.word ↦ hashTape`. -/
structure HashWriterAt extends WriterStage where
  ready : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ClockJoin.ReadyRun M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n))
        (inBank inS (thrReq n a' ha' Cs carriers translation).word)
        (outBank inS outS (thrReq n a' ha' Cs carriers translation).word
          (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))

/-- The three writers at one call family. -/
structure WritersAt where
  sym : SymWriterAt l F EW cW kclk coef A a ha
  thr : ThrWriterAt l F EW cW kclk coef A a ha
  hash : HashWriterAt l F EW cW kclk coef A a ha

end Writers

/-- **PA's (d) deliverable** in `SeedFixLeaf`'s order of choice: after the endpoint exponent `fe`, the writers' floors
`E_W` (powers of `n`, `c_r`-free); for every admissible `F`, a coefficient `c_W` and the three writers
at every clock and source work. -/
def WriterLeaf (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Cost.Envelope, ∀ F : Split.GateFree l, F.filterErrDeg = fe → PrimAsm.Plan.ClassLE EW F.E →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), WritersAt l F EW cW kclk coef A a ha

end NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
