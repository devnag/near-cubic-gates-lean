import Proof.Wire_3_5.FinalPassSeamsPt2
import Proof.Wire_3_5.PrimAsmS5SeamB

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

/-- **The SYM evaluator's words**: what the front writes for a SYM request (S5 needs nothing else). -/
structure SymWords where
  nw : ℕ
  nn : ℕ
  words : SymCall → Fin nw → List Bool
  nums : SymCall → Fin nn → ℕ

/-- A blank-cell SYM evaluator's words. -/
def SymPtEval2.toWords (E : SymPtEval2) : SymWords := ⟨E.nw, E.nn, E.words, E.nums⟩

/-- A SYM evaluator's words. -/
def symToWords (E : SymPtEval) : SymWords := ⟨E.nw, E.nn, E.words, E.nums⟩

section Req2
variable {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (Sw : SymWords)

/-- **The front's words at a request, over the SYM words**: `frontWordsOf`'s slots (S4's 8 words; the THR
evaluator's 7 words and its numbers; the SYM words and numbers). -/
def frontWordsOfW : PrimRequest → Fin (17 + Sw.nw) → List Bool
  | ⟨n, .sym, a, ha, Cs, carriers, translation⟩ => fun i =>
      if hs : I.StarAt n then
        if h8 : i.val < 8 then
          s4Core (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            ((SeedFix.greedySampler I alg).symS Cs carriers translation hs) carriers (I.filterParams .sym n) ⟨i.val, h8⟩
        else if i.val < 16 then []
        else if h : i.val - 16 < Sw.nw then Sw.words (symCallOf I hs ha Cs carriers) ⟨i.val - 16, h⟩
        else PrimAsm.Data.unaryList (List.ofFn (Sw.nums (symCallOf I hs ha Cs carriers)))
      else []
  | ⟨n, .thr, a, ha, Cs, carriers, translation⟩ => fun i =>
      if hs : I.StarAt n then
        if h8 : i.val < 8 then
          s4Core (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs) carriers (I.filterParams .thr n) ⟨i.val, h8⟩
        else if h15 : i.val < 15 then thrWords (thrCallOf I alg hs ha Cs carriers translation) ⟨i.val - 8, by omega⟩
        else if i.val = 15 then
          PrimAsm.Data.unaryList (List.ofFn (thrNums (thrCallOf I alg hs ha Cs carriers translation)))
        else []
      else []

/-- The frozen `frontWordsOf` is the case of a `SymPtEval`'s words. -/
theorem frontWordsOf_toWords (E3 : SymPtEval) : frontWordsOf I alg E3 = frontWordsOfW I alg (symToWords E3) := by
  funext req
  obtain ⟨n, mode, a, ha, Cs, carriers, translation⟩ := req
  cases mode <;> rfl

end Req2

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- The front's words at a request of the family (over the SYM words). -/
noncomputable abbrev frontWordsW (r : FReq l F kclk coef A a ha) : Fin (17 + Sw.nw) → List Bool :=
  frontWordsOfW (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw r.1

/-- **The seeds phase, v2**: `SeedsProg` over `frontWordsW`, with its cost functions bounded: per point polynomially
in the request's width `n`, per filter seed and overall in the preprocessing form `s5Bound` (`C·2^{D·ψ}·(|fpIn|+1)^D`). -/
structure SeedsProg2 where
  t : ℕ
  wd : Fin (17 + Sw.nw) → Fin t
  tN : Fin t
  tD : Fin t
  reg : Fin t → Bool
  Kc : ℕ
  Dc : ℕ
  s : ℕ
  M : Machine t s
  tab : FReq l F kclk coef A a ha → ℕ
  pt : FReq l F kclk coef A a ha → ℕ
  ov : FReq l F kclk coef A a ha → ℕ
  Cp : ℕ
  Dp : ℕ
  Ct : ℕ
  Dt : ℕ
  Co : ℕ
  Do : ℕ
  pt_le : ∀ r : FReq l F kclk coef A a ha, pt r ≤ Cp * (r.1.n + 1) ^ Dp
  tab_le : ∀ r, tab r ≤ PrimAsm.S5Seam.s5Bound l F kclk coef A a ha Ct Dt r
  ov_le : ∀ r, ov r ≤ PrimAsm.S5Seam.s5Bound l F kclk coef A a ha Co Do r
  exitA : (FReq l F kclk coef A a ha → Fin t → List Bool) → (FReq l F kclk coef A a ha → ℕ) →
    FReq l F kclk coef A a ha → Fin t → List Bool
  run : ∀ (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool)
    (W : FReq l F kclk coef A a ha → ℕ),
    FrontOut l F kclk coef A a ha wd ![tN, tD] (frontWordsW l F kclk coef A a ha Sw)
      (fun r => ![0, fpDen l F kclk coef A a ha r]) W
      (fun r j => if reg j then Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc + 1 else 0) H Ab →
    (∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r) →
    ∀ r, Step M (seedsShape (seedCount l F kclk coef A a ha r) (tab r) (ptCount l F kclk coef A a ha r) (pt r) (ov r))
        (H r) (Ab r) (fun _ => 0) (exitA Ab W r) ∧
      exitA Ab W r tN = frame (binary (W r) (fpNum l F kclk coef A a ha r)) ∧
      exitA Ab W r tD = frame (binary (W r) (fpDen l F kclk coef A a ha r)) ∧
      fpNum l F kclk coef A a ha r < 2 ^ W r

theorem SeedsProg2.cost_le (X : SeedsProg2 l F kclk coef A a ha Sw) (r : FReq l F kclk coef A a ha) :
    seedsShape (seedCount l F kclk coef A a ha r) (X.tab r) (ptCount l F kclk coef A a ha r) (X.pt r) (X.ov r) ≤
      seedsShape (seedCount l F kclk coef A a ha r) (PrimAsm.S5Seam.s5Bound l F kclk coef A a ha X.Ct X.Dt r)
        (ptCount l F kclk coef A a ha r) (X.Cp * (r.1.n + 1) ^ X.Dp)
        (PrimAsm.S5Seam.s5Bound l F kclk coef A a ha X.Co X.Do r) := by
  unfold seedsShape
  have h1 := Nat.mul_le_mul_left (seedCount l F kclk coef A a ha r) (X.tab_le r)
  have h2 := Nat.mul_le_mul_left (ptCount l F kclk coef A a ha r) (X.pt_le r)
  have h3 := X.ov_le r
  omega

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
