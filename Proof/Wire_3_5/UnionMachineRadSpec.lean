import Proof.Wire_3_5.UnionMachineRadSetupB

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSpec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB

/-! ## The block writer (stage 5b) -/

/-- **One digit's pool indices**, `DigsW`'s format: each index `gi` as `true :: 1^gi 0`, then the closing `false`. -/
def gisWord (gis : List ℕ) : List Bool := gis.flatMap (fun gi => true :: (List.replicate gi true ++ [false])) ++ [false]

/-- The block writer's register count (inputs in `0 … 6`, scratch `7 …`). -/
abbrev radBlkK : ℕ := 64

/-- The block writer's size measure: the output's length, the block, the table word, the indices' word, the labels'
bound, `t`, `3·listBound D` and `capC D L`. -/
def blkSize (D : ListData) (gis : List ℕ) (G row t : ℕ) (sgn : Bool) (olen : ℕ) : ℕ :=
  olen + (Streaming.marks (true :: blockC D gis.length t sgn false (CompilerMachine.Pool.labsOf G row gis))).length +
    (FinalPass.ListEval.levelWord D.M D.J D.W (FinalPass.ListEval.rowsOf D gis.length)).length + (gisWord gis).length +
    (G + 1) * (4 * row + 4) + t + 3 * ListMachine.listBound D + capC D gis.length

/-- **The RADIX block writer** (stage 5b, C1b): one word program per layout (output stream `O`, table stream `T`,
indices stream `GS`, two scratch streams `Sc`, registers `Rg`), with capacity `need` and cost `bound` polynomial. From
the table word `levelWord M J W (rowsOf D L)` on `T` and one digit's indices `gisWord gis` on `GS` (heads `0`), the
output's head at its end, and in registers `L = |gis|`, `G`, `row`, `t`, the sign (`1`/`0`), `3·listBound D`,
`capC D L` (the scratch registers `7 …` zero, the scratch streams blank): it APPENDS
`marks (true :: blockC D L t sgn false (labsOf G row gis))` to `O`, moves `O`'s head to the new end, and changes
nothing else. -/
structure RadBlockW where
  prog : ∀ {ns nr : ℕ}, Fin (ns + 1) → Fin (ns + 1) → Fin (ns + 1) → (Fin 2 → Fin (ns + 1)) →
    (Fin radBlkK ↪ Fin nr) → WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ N, need N ≤ C * (N + 1) ^ D
  bound_le : ∀ c, bound c ≤ C * (c + 1) ^ D
  run : ∀ {ns nr : ℕ} (O T GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr),
    O ≠ T → O ≠ GS → T ≠ GS → Function.Injective Sc → (∀ i, Sc i ≠ O ∧ Sc i ≠ T ∧ Sc i ≠ GS) →
    ∀ (Dl : ListData) (gis : List ℕ) (G row t : ℕ) (sgn : Bool) (cap : ℕ) (σ : WState ns nr),
    σ.st T = FinalPass.ListEval.levelWord Dl.M Dl.J Dl.W (FinalPass.ListEval.rowsOf Dl gis.length) → σ.sh T = 0 →
    σ.st GS = gisWord gis → σ.sh GS = 0 → σ.sh O = (σ.st O).length →
    (∀ i, σ.st (Sc i) = [] ∧ σ.sh (Sc i) = 0) →
    σ.val (Rg 0) = gis.length → σ.val (Rg 1) = G → σ.val (Rg 2) = row → σ.val (Rg 3) = t →
    σ.val (Rg 4) = (if sgn then 1 else 0) → σ.val (Rg 5) = 3 * ListMachine.listBound Dl →
    σ.val (Rg 6) = capC Dl gis.length →
    (∀ j : Fin radBlkK, 7 ≤ j.val → σ.val (Rg j) = 0) →
    need (blkSize Dl gis G row t sgn (σ.st O).length) ≤ cap →
    WExec cap (prog O T GS Sc Rg) σ
      ((σ.sets O (σ.st O ++ Streaming.marks (true :: blockC Dl gis.length t sgn false
        (CompilerMachine.Pool.labsOf G row gis)))).seth O
        (σ.st O ++ Streaming.marks (true :: blockC Dl gis.length t sgn false
          (CompilerMachine.Pool.labsOf G row gis))).length)
      (bound cap)

/-! ## The row's capacities (stage 7) -/

/-- Route B's size measure: the digit lists' counting capacity `(8L+2)^{3·lb+1}` and the row's numbers. -/
def radX (M τ Lmax Mlab lb lw p b0 : ℕ) : ℕ :=
  (8 * Lmax + 2) ^ (3 * lb + 1) + M + τ + Lmax + Mlab + lb + lw + p + b0 + 2

/-- The power scale `U = 2^20·radX`. -/
def radU (M τ Lmax Mlab lb lw p b0 : ℕ) : ℕ := 2 ^ 20 * radX M τ Lmax Mlab lb lw p b0

/-- Route B's scrub capacity `R = U^40` (its log capacity is `R + 1`). -/
def radRB (U : ℕ) : ℕ := U ^ 40

/-- Route B's loop capacity `cap = U^45`. -/
def radCapB (U : ℕ) : ℕ := U ^ 45

/-- The Route-B request at the measure's numbers. -/
def reqB (r : RadReq) (Lmax Mlab lb lw : ℕ) : RadReqB :=
  ⟨r, radRB (radU r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0),
    radRB (radU r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0) + 1,
    radCapB (radU r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0)⟩

/-- **Stage 7 (a), the capacities** (C1b): at an admissible request whose digit lists have at most `Lmax`
occurrences, exactly four labels per occurrence, labels at most `Mlab`, `listBound D ≤ lb` and table word at `Lmax` of
length at most `lw`, Route B's capacities meet the row's conditions. -/
def RadCapsStmt : Prop :=
  ∀ (r : RadReq) (Lmax Mlab lb lw : ℕ), r.Pre → ListMachine.listBound r.D ≤ lb →
    (∀ dg ∈ r.digs, dg.1 ≤ Lmax ∧ dg.2.length = 4 * dg.1 ∧ ∀ lab ∈ dg.2, lab ≤ Mlab) →
    (FinalPass.ListEval.levelWord r.D.M r.D.J r.D.W (FinalPass.ListEval.rowsOf r.D Lmax)).length ≤ lw →
    (reqB r Lmax Mlab lb lw).Caps

/-- **Stage 7 (b), admissibility** (C1b): at every THR call of the gate, every selection, prime, residue and star
row, the RADIX row's request is admissible. -/
def RadPreStmt (l : Literals) (F : GateFree l) : Prop :=
  ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
      (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
      (s : ZMod pr.val) (row : ℕ),
    row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2 →
    (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).Pre

end NearCubicWires.WireExponent3_5.UnionMachine.RadSpec
