import Proof.Wire_3_5.FinalPassSeamsProg2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

variable {l F kclk coef A a ha}

/-- **S4's register length** at a request: `Kc·(|fpIn|+1)^{Dc} + 1` on register tapes, `0` elsewhere. -/
noncomputable def blOf2 {nw : ℕ} (L : S5Lay nw) (r : FReq l F kclk coef A a ha) (j : Fin L.t) : ℕ :=
  if L.reg j then L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1 else 0

variable (l F kclk coef A a ha)

/-- **The THR half** (C6b): from any bank with the input on tape `0` and the THR slots and scratch blank, every
head at `0`, it writes the THR slots of `frontWordsW`, leaves its scratch blank of length `≤ len r` (`len r` within
S4's register length), keeps every other tape, and returns every head to `0`. -/
structure S5Thr2 (L : S5Lay Sw.nw) where
  s : ℕ
  M : Machine L.t s
  cost : FReq l F kclk coef A a ha → ℕ
  len : FReq l F kclk coef A a ha → ℕ
  len_le : ∀ r, len r ≤ L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1
  run : ∀ (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool),
    Ab ⟨0, L.ht⟩ = frame (fpIn l F kclk coef A a ha r) →
    (∀ k, thrSlot k → Ab (L.wd k) = []) → (∀ j, L.thrSc j = true → Ab j = []) →
    ∃ Ab' : Fin L.t → List Bool, Step M (cost r) (fun _ => 0) Ab (fun _ => 0) Ab' ∧
      (∀ k, thrSlot k → Ab' (L.wd k) = frontWordsW l F kclk coef A a ha Sw r k) ∧
      (∀ j, L.thrSc j = true → ∃ ℓ ≤ len r, Ab' j = List.replicate ℓ false) ∧
      (∀ j, L.thrSc j = false → (∀ k, thrSlot k → j ≠ L.wd k) → Ab' j = Ab j)

/-- **The THR half's exit, the core half's entry**: the input on tape `0`, the THR slots written, every other word
and number tape and the core scratch blank, the THR scratch blank within S4's register length, every other tape
blank. -/
structure ThrExit2 (L : S5Lay Sw.nw) (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool) : Prop where
  input : Ab ⟨0, L.ht⟩ = frame (fpIn l F kclk coef A a ha r)
  thr : ∀ k, thrSlot k → Ab (L.wd k) = frontWordsW l F kclk coef A a ha Sw r k
  core : ∀ k, ¬ thrSlot k → Ab (L.wd k) = []
  num : Ab L.tN = [] ∧ Ab L.tD = []
  thrSc : ∀ j, L.thrSc j = true → ∃ ℓ ≤ L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1,
    Ab j = List.replicate ℓ false
  rest : ∀ j, j.val ≠ 0 → (∀ k, j ≠ L.wd k) → j ≠ L.tN → j ≠ L.tD → L.thrSc j = false → Ab j = []

/-- **The core half** (PA2): from the THR half's exit, every head at `0`, to `FrontOut` at `frontWordsW` with
`Num = 0`, `Den = fpDen` in `W`-bit binary (`ptCount·vmax < 2^W`) and S4's register lengths, every head at `0`. -/
structure S5Core2 (L : S5Lay Sw.nw) where
  s : ℕ
  M : Machine L.t s
  cost : FReq l F kclk coef A a ha → ℕ
  W : FReq l F kclk coef A a ha → ℕ
  hW : ∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r
  exitA : FReq l F kclk coef A a ha → Fin L.t → List Bool
  run : ∀ (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool), ThrExit2 l F kclk coef A a ha Sw L r Ab →
    Step M (cost r) (fun _ => 0) Ab (fun _ => 0) (exitA r)
  out : FrontOut l F kclk coef A a ha L.wd ![L.tN, L.tD] (frontWordsW l F kclk coef A a ha Sw)
    (fun r => ![0, fpDen l F kclk coef A a ha r]) W (fun r j => blOf2 L r j) (fun _ _ => 0) exitA

end Family

end NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
