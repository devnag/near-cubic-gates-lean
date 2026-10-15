import Proof.Wire_3_5.FinalPassSeamsProg

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (E3 : SymPtEval)

/-- The THR slots `8 … 15` of `frontWords`. -/
def thrSlot {nw : ℕ} (k : Fin (17 + nw)) : Prop := 8 ≤ k.val ∧ k.val < 16

instance {nw : ℕ} (k : Fin (17 + nw)) : Decidable (thrSlot k) := by unfold thrSlot; infer_instance

/-- **The front's layout** (S4's `SeedsProg` layout, plus the halves' scratch sets). -/
structure S5Lay (nw : ℕ) where
  t : ℕ
  ht : 1 ≤ t
  wd : Fin (17 + nw) → Fin t
  tN : Fin t
  tD : Fin t
  reg : Fin t → Bool
  Kc : ℕ
  Dc : ℕ
  thrSc : Fin t → Bool
  coreSc : Fin t → Bool
  wdInj : Function.Injective wd
  hND : tN ≠ tD
  wdN : ∀ k, wd k ≠ tN
  wdD : ∀ k, wd k ≠ tD
  in0 : ∀ k, (wd k).val ≠ 0
  inN : tN.val ≠ 0
  inD : tD.val ≠ 0
  reg0 : reg ⟨0, ht⟩ = true
  thrReg : ∀ j, thrSc j = true → reg j = true
  coreReg : ∀ j, coreSc j = true → reg j = true
  thrOff : ∀ j, thrSc j = true → j.val ≠ 0 ∧ (∀ k, j ≠ wd k) ∧ j ≠ tN ∧ j ≠ tD
  coreOff : ∀ j, coreSc j = true → j.val ≠ 0 ∧ (∀ k, j ≠ wd k) ∧ j ≠ tN ∧ j ≠ tD
  disj : ∀ j, thrSc j = true → coreSc j = false

variable {l F kclk coef A a ha E3}

/-- **S4's register length** at a request: `Kc·(|fpIn|+1)^{Dc} + 1` on register tapes, `0` elsewhere. -/
noncomputable def blOf (L : S5Lay E3.nw) (r : FReq l F kclk coef A a ha) (j : Fin L.t) : ℕ :=
  if L.reg j then L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1 else 0

variable (l F kclk coef A a ha E3)

structure S5Thr (L : S5Lay E3.nw) where
  s : ℕ
  M : Machine L.t s
  cost : FReq l F kclk coef A a ha → ℕ
  len : FReq l F kclk coef A a ha → ℕ
  len_le : ∀ r, len r ≤ L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1
  run : ∀ (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool),
    Ab ⟨0, L.ht⟩ = frame (fpIn l F kclk coef A a ha r) →
    (∀ k, thrSlot k → Ab (L.wd k) = []) → (∀ j, L.thrSc j = true → Ab j = []) →
    ∃ Ab' : Fin L.t → List Bool, Step M (cost r) (fun _ => 0) Ab (fun _ => 0) Ab' ∧
      (∀ k, thrSlot k → Ab' (L.wd k) = frontWords l F kclk coef A a ha E3 r k) ∧
      (∀ j, L.thrSc j = true → ∃ ℓ ≤ len r, Ab' j = List.replicate ℓ false) ∧
      (∀ j, L.thrSc j = false → (∀ k, thrSlot k → j ≠ L.wd k) → Ab' j = Ab j)

/-- **The THR half's exit, the core half's entry**: the input on tape `0`, the THR slots written, every other word
and number tape and the core scratch blank, the THR scratch blank within S4's register length, every other tape
blank. -/
structure ThrExit (L : S5Lay E3.nw) (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool) : Prop where
  input : Ab ⟨0, L.ht⟩ = frame (fpIn l F kclk coef A a ha r)
  thr : ∀ k, thrSlot k → Ab (L.wd k) = frontWords l F kclk coef A a ha E3 r k
  core : ∀ k, ¬ thrSlot k → Ab (L.wd k) = []
  num : Ab L.tN = [] ∧ Ab L.tD = []
  thrSc : ∀ j, L.thrSc j = true → ∃ ℓ ≤ L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc + 1,
    Ab j = List.replicate ℓ false
  rest : ∀ j, j.val ≠ 0 → (∀ k, j ≠ L.wd k) → j ≠ L.tN → j ≠ L.tD → L.thrSc j = false → Ab j = []

/-- **The core half** (PA2): from the THR half's exit, every head at `0`, to `FrontOut` at `frontWords` with
`Num = 0`, `Den = fpDen` in `W`-bit binary (`ptCount·vmax < 2^W`) and S4's register lengths, every head at `0`. -/
structure S5Core (L : S5Lay E3.nw) where
  s : ℕ
  M : Machine L.t s
  cost : FReq l F kclk coef A a ha → ℕ
  W : FReq l F kclk coef A a ha → ℕ
  hW : ∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r
  exitA : FReq l F kclk coef A a ha → Fin L.t → List Bool
  run : ∀ (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool), ThrExit l F kclk coef A a ha E3 L r Ab →
    Step M (cost r) (fun _ => 0) Ab (fun _ => 0) (exitA r)
  out : FrontOut l F kclk coef A a ha L.wd ![L.tN, L.tD] (frontWords l F kclk coef A a ha E3)
    (fun r => ![0, fpDen l F kclk coef A a ha r]) W (fun r j => blOf L r j) (fun _ _ => 0) exitA

end Family

end NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
