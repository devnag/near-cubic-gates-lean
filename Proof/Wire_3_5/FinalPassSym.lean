import Proof.Wire_3_5.FinalPassList

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierWalk NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Rows

/-! ## The amplified list, fast -/

/-- A visit's report by the followed state. -/
def visitReportFast (P : FlatListParams) (e : P.FlatSeed) (k : Fin P.walkLen) (Z : List Bool) : ℕ :=
  ListFast.listReportFast (P.base.data (P.decode (e.vertex k))) Z

/-- The majority state, fast. -/
def majStateFast (P : FlatListParams) (e : P.FlatSeed) (Z : List Bool) (s : ℕ) : Bool :=
  concreteMajorityFailure (fun v => decide (ListFast.listReportFast (P.base.data (P.decode v)) Z = s)) e

def flatReportFast (P : FlatListParams) (e : P.FlatSeed) (Z : List Bool) : ℕ :=
  (((List.range P.M).map (· + 1)).find? fun s => majStateFast P e Z s).getD 0

theorem base_report_eq_fast (B : BaseListParams) (h : B.Seed) (Z : List Bool) :
    B.report h Z = ListFast.listReportFast (B.data h) Z :=
  ListFast.listReport_eq_fast (B.data h) Z

theorem majState_eq_fast (P : FlatListParams) (e : P.FlatSeed) (Z : List Bool) (s : ℕ) :
    P.majState e Z s = majStateFast P e Z s := by
  unfold FlatListParams.majState majStateFast
  simp only [base_report_eq_fast]

theorem flatReport_eq_fast (P : FlatListParams) (e : P.FlatSeed) (Z : List Bool) :
    P.flatReport e Z = flatReportFast P e Z := by
  unfold FlatListParams.flatReport flatReportFast
  simp only [majState_eq_fast]

section Sym
variable (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (Pl : FlatListParams)

/-- The lists' reports `(t_j^+, t_j^−)`, fast. -/
def symRepFast (el : Pl.FlatSeed) (c : BitInput P.n) (u v : P.Errors) : Fin a → ℕ × ℕ :=
  fun j => (flatReportFast Pl el (symZp P Cs c u v j), flatReportFast Pl el (symZm P Cs c u v j))

def symRhatFast (el : Pl.FlatSeed) (c : BitInput P.n) (u v : P.Errors) : Bool :=
  symReported (symM P Cs) (symG P Cs) (symScore P Cs c u v) (symRepFast P Cs Pl el c u v)

theorem symRhat_eq_fast (el : Pl.FlatSeed) (c : BitInput P.n) (u v : P.Errors) :
    symRhat P Cs Pl el c u v = symRhatFast P Cs Pl el c u v := by
  unfold symRhat symRhatFast symRep symRepFast FlatListParams.jointState
  simp only [flatReport_eq_fast]

end Sym

/-! ## The printed rational -/

section Value
variable (P : StarParams) (σ : P.Translation) {a : ℕ} {N Q : ℕ} (eqv : P.Errors ≃ Fin N)
  (S : Fin Q → Fin N × Fin N)

/-- **The SYM printed rational, computable**: `(Σ_zΣ_{(e,e')}Σ_ℓ M·R̂)/(|Z|·|E|·Q)` with the bit-level mask and the fast
lists. -/
def symValueBits (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) : ℚ :=
  (∑ c : {c // P.IsCenter σ c}, ∑ s : GapSeed FP × Pl.FlatSeed, ∑ l : Fin Q,
      bitQ (maskBits P σ carriers FP s.1 (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))) *
        bitQ (symRhatFast P Cs Pl s.2 c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))) /
    (Fintype.card {c // P.IsCenter σ c} * Fintype.card (GapSeed FP × Pl.FlatSeed) * Q)

/-- **The computable SYM value is the primitive's printed rational.** -/
theorem symValueBits_eq (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) :
    symValueBits P σ eqv S Cs carriers FP Pl = symValue P σ eqv S Cs carriers FP Pl := by
  unfold symValueBits symValue
  simp only [symMask_eq_maskBits, symRhat_eq_fast]

end Value

end NearCubicWires.WireExponent3_5.FinalPass
