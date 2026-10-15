import Proof.Wire_3_5.PrimAsmSymFlat

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFlat
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.SymFlat NearCubicWires.SupplierPipeline

section Hash
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))

/-- The HASH entry `q`'s row: the aux FILTER row of cell `q / nE`, aux seed `q % nE`. -/
def hashRowQ (q : ℕ) : RowReq :=
  hashRow (I.starParams n hs) carriers (I.filterParams .thr n) (thrCallE alg I hs Cs carriers)
    (auxEnum alg I hs Cs carriers (q % nE alg I hs Cs carriers)) (thrPool (I.starParams n hs) Cs carriers).length
    (q / nE alg I hs Cs carriers) n

/-- The HASH request units (entry `q`, its only row, its only request). -/
def hashUnit (q _r _s : ℕ) : List Bool := unitBody (hashRowQ alg I hs Cs carriers q)

/-- The number of HASH entries `N²·nE`. -/
abbrev nHash : ℕ := (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 * nE alg I hs Cs carriers

theorem hashExprs_eq : hashExprs alg I hs Cs carriers =
    (List.range (nHash alg I hs Cs carriers)).map fun q => refOf (hashRowQ alg I hs Cs carriers q) := by
  unfold hashExprs hashBatch
  rw [List.map_map]
  rfl

/-- **The HASH tape is the writer loop's units, closed** (one printed row, one request per entry). -/
theorem hashTape_flat :
    (List.range (nHash alg I hs Cs carriers * (1 * (0 + 3) + 2))).flatMap
      (symEmit 1 0 (hashUnit alg I hs Cs carriers)) ++ [false] = hashTape alg I hs Cs carriers := by
  rw [units_blockWord 1 0 (nHash alg I hs Cs carriers) (hashUnit alg I hs Cs carriers)
    (fun q => [[hashRowQ alg I hs Cs carriers q]]) (fun _ _ => rfl) (fun q _ r hr => by
      have : r = 0 := by omega
      subst this
      simp [hashUnit])]
  unfold hashTape
  rw [hashExprs_eq, List.map_map]
  congr 1

end Hash

end NearCubicWires.WireExponent3_5.PrimAsm.HashFlat
