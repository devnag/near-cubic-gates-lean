import Proof.Wire_3_5.PrimThrWTopFront
import Proof.Wire_3_5.PrimAsmRecords
import Proof.Wire_3_5.PrimAsmEnum
import Proof.Wire_3_5.FinalPassWords

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## The digit word -/

/-- **The digit populations' word**: per digit, each pool index `gi` as `true :: 1^gi 0`, then the
digit's closing `false`. -/
def digsWord (ls : List (List ℕ)) : List Bool :=
  ls.flatMap (fun gis => gis.flatMap (fun gi => true :: (List.replicate gi true ++ [false])) ++ [false])

theorem digsWord_nil : digsWord [] = [] := rfl

theorem digsWord_cons (gis : List ℕ) (ls : List (List ℕ)) :
    digsWord (gis :: ls) =
      gis.flatMap (fun gi => true :: (List.replicate gi true ++ [false])) ++ [false] ++ digsWord ls := by
  simp [digsWord, List.flatMap_cons]

/-- The word's length: `gi + 2` per index, `1` per digit. -/
theorem digsWord_length (ls : List (List ℕ)) :
    (digsWord ls).length = (ls.map fun gis => (gis.map fun gi => gi + 2).sum + 1).sum := by
  induction ls with
  | nil => rfl
  | cons gis ls ih =>
    rw [digsWord_cons, List.length_append, List.length_append, ih, List.length_flatMap, List.map_cons,
      List.sum_cons]
    simp only [List.length_cons, List.length_append, List.length_replicate]
    congr 2

/-! ## The layout and the entry -/

/-- The register count of `DigsW`'s layout. -/
abbrev digsK : ℕ := 48

section Entry
variable {ns nr : ℕ} (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (R : Fin digsK ↪ Fin nr)
  (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Stars.Carrier P.n)) (alg : DecompositionAlgorithm) (den : ℕ)

/-- **`DigsW`'s entry** at selection `g` and prime `pr`: circuit `i`'s payload on `Pay i` (blank for `i ≥ a'`) and
the output stream `Dg` blank, all these heads at `0`; registers `R 0, …, R 4` hold `a'`, `g`'s mixed-radix index
(`Enum.thrEqEquiv`), `p`, `τ₀ = thrDigits` and `oOff = thrOff`; the scratch registers `R 5, …` are zero. -/
structure DigsIn (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den))
    (σ : WState ns nr) : Prop where
  pay : ∀ i : Fin 4, σ.st (Pay i) = if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else []
  payH : ∀ i : Fin 4, σ.sh (Pay i) = 0
  dg : σ.st Dg = []
  dgH : σ.sh Dg = 0
  vA : σ.val (R 0) = a'
  vG : σ.val (R 1) = (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)
  vP : σ.val (R 2) = pr.val
  vTau : σ.val (R 3) = Primitive.thrDigits P Cs alg den
  vOff : σ.val (R 4) = PrimAsm.Records.thrOff P Cs carriers
  zero : ∀ j : Fin digsK, 5 ≤ j.val → σ.val (R j) = 0

/-- The entry size: the payload lengths, `p`, `τ₀` and `oOff`. -/
def digsN (p : ℕ) : ℕ :=
  (∑ i : Fin a', (PrimThrW.TopFront.payOf alg (Cs i)).length) + p + Primitive.thrDigits P Cs alg den +
    PrimAsm.Records.thrOff P Cs carriers

end Entry

/-! ## The program's type -/

/-- **The digit program** (W17): one word program per layout, with capacity `need` and cost `bound`
polynomial in the entry size. From every `DigsIn` entry (at most four circuits, pairwise distinct payload streams,
none of them `Dg`) it writes `digsWord` of row `(g, p)`'s digit populations on `Dg` and changes nothing else. -/
structure DigsW where
  prog : ∀ {ns nr : ℕ}, (Fin 4 → Fin (ns + 1)) → Fin (ns + 1) → (Fin digsK ↪ Fin nr) → WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ N, need N ≤ C * (N + 1) ^ D
  bound_le : ∀ N, bound N ≤ C * (N + 1) ^ D
  run : ∀ {ns nr : ℕ} (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (R : Fin digsK ↪ Fin nr),
    Function.Injective Pay → (∀ i, Pay i ≠ Dg) →
    ∀ (P : StarParams) {a' : ℕ}, a' ≤ 4 → ∀ (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
      (carriers : List (Stars.Carrier P.n)) (alg : DecompositionAlgorithm) (den : ℕ)
      (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den))
      (cap : ℕ) (σ : WState ns nr),
    DigsIn Pay Dg R P Cs carriers alg den g pr σ →
    need (digsN P Cs carriers alg den pr.val) ≤ cap →
    WExec cap (prog Pay Dg R) σ
      (σ.sets Dg (digsWord (List.ofFn fun d => PrimAsm.Records.thrDigGis P Cs carriers alg den g pr d)))
      (bound (digsN P Cs carriers alg den pr.val))

end NearCubicWires.WireExponent3_5.FinalPass.Digs
