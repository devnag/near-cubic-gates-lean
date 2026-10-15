import Proof.Wire_3_5.FinalPassSeamsWS
import Proof.Wire_3_5.PrimAsmS5SeamB2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Bank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam NearCubicWires.WireExponent3_5.Split

/-- The THR half's scratch tapes. -/
abbrev roomT : ℕ := 4096

/-- The core half's scratch tapes. -/
abbrev roomC : ℕ := 4096

/-- **The front halves' room** in a bank layout: its THR and core scratch contain `roomT`, `roomC` named tapes. -/
structure HalfRoom {nw : ℕ} (L : S5Lay nw) where
  thrE : Fin roomT ↪ Fin L.t
  thrE_sc : ∀ i, L.thrSc (thrE i) = true
  coreE : Fin roomC ↪ Fin L.t
  coreE_sc : ∀ i, L.coreSc (coreE i) = true

/-- **A front half built generic in the bank**: its register-length need `K·(|fpIn|+1)^D` and, at every bank layout
with the halves' room and at least that register length, the half. -/
structure HalfGen {nw : ℕ} (P : S5Lay nw → Type) where
  K : ℕ
  D : ℕ
  half : ∀ L : S5Lay nw, HalfRoom L → K ≤ L.Kc → D ≤ L.Dc → P L

/-- **The THR half's target, generic in the bank** (C6b's), at every call family. -/
abbrev ThrHalfGen (Sw : SymWords) : Type :=
  ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    HalfGen fun L : S5Lay Sw.nw => S5ThrB2 l F kclk coef A a ha Sw L

/-! ## S4's bank -/

section Tapes
variable {ns nr : ℕ}

theorem sTape_val (i : Fin (ns + 1)) : (sTape (nr := nr) i).val = if i.val = 0 then 0 else i.val + 1 := rfl

theorem sTape_le (i : Fin (ns + 1)) : (sTape (nr := nr) i).val ≤ ns + 1 := by
  rw [sTape_val]
  have := i.isLt
  split <;> omega

theorem sTape_inj {i j : Fin (ns + 1)} (h : sTape (nr := nr) i = sTape (nr := nr) j) : i = j := by
  have e := congrArg Fin.val h
  rw [sTape_val, sTape_val] at e
  apply Fin.ext
  split_ifs at e <;> omega

end Tapes

variable (Sw : SymWords)

/-- **S4's bank at its word layout**: the word layout, S4's register capacity `Kc·(|fpIn|+1)^{Dc}`, the first of the
halves' scratch registers, and the facts the bank needs (the words, `Num`, `Den` off stream `0`). -/
structure BankLay where
  L : SdLay Sw
  Kc : ℕ
  Dc : ℕ
  base : ℕ
  room : base + roomT + roomC ≤ L.nr
  w0 : ∀ k, (L.wdS k).val ≠ 0
  n0 : L.sN.val ≠ 0
  d0 : L.sD.val ≠ 0

variable {Sw}

/-- **The bank's `S5Lay`**. -/
def BankLay.lay (B : BankLay Sw) : S5Lay Sw.nw where
  t := B.L.ns + 2 + B.L.nr
  ht := by omega
  wd := fun k => sTape (B.L.wdS k)
  tN := sTape B.L.sN
  tD := sTape B.L.sD
  reg := fun j => decide (j.val = 0 ∨ B.L.ns + 2 ≤ j.val)
  Kc := B.Kc
  Dc := B.Dc
  thrSc := fun j => decide (B.L.ns + 2 + B.base ≤ j.val ∧ j.val < B.L.ns + 2 + B.base + roomT)
  coreSc := fun j => decide (B.L.ns + 2 + B.base + roomT ≤ j.val ∧ j.val < B.L.ns + 2 + B.base + roomT + roomC)
  wdInj := fun _ _ h => B.L.wdInj (sTape_inj h)
  hND := fun h => B.L.nd (sTape_inj h)
  wdN := fun k h => B.L.wdN k (sTape_inj h)
  wdD := fun k h => B.L.wdD k (sTape_inj h)
  in0 := fun k => by rw [sTape_val, if_neg (B.w0 k)]; omega
  inN := by rw [sTape_val, if_neg B.n0]; omega
  inD := by rw [sTape_val, if_neg B.d0]; omega
  reg0 := by simp
  thrReg := fun j h => by simp only [decide_eq_true_eq] at h ⊢; omega
  coreReg := fun j h => by simp only [decide_eq_true_eq] at h ⊢; omega
  thrOff := fun j h => by
    simp only [decide_eq_true_eq] at h
    refine ⟨by omega, fun k e => ?_, fun e => ?_, fun e => ?_⟩ <;>
      (subst e; first | (have := sTape_le (nr := B.L.nr) (B.L.wdS k); omega) |
        (have := sTape_le (nr := B.L.nr) B.L.sN; omega) | (have := sTape_le (nr := B.L.nr) B.L.sD; omega))
  coreOff := fun j h => by
    simp only [decide_eq_true_eq] at h
    refine ⟨by omega, fun k e => ?_, fun e => ?_, fun e => ?_⟩ <;>
      (subst e; first | (have := sTape_le (nr := B.L.nr) (B.L.wdS k); omega) |
        (have := sTape_le (nr := B.L.nr) B.L.sN; omega) | (have := sTape_le (nr := B.L.nr) B.L.sD; omega))
  disj := fun j h => by simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega

/-- **The halves' room in S4's bank**: S4's registers `[base, base + roomT)` and `[base + roomT, … + roomC)`. -/
def BankLay.hroom (B : BankLay Sw) : HalfRoom B.lay where
  thrE := ⟨fun i => ⟨B.L.ns + 2 + B.base + i.val, by have := B.room; have := i.isLt; show _ < B.L.ns + 2 + B.L.nr; omega⟩,
    fun a b h => Fin.ext (by have := congrArg Fin.val h; simp only at this; omega)⟩
  thrE_sc := fun i => by
    show decide _ = true
    simp only [Function.Embedding.coeFn_mk, decide_eq_true_eq]
    have := i.isLt
    omega
  coreE := ⟨fun i => ⟨B.L.ns + 2 + B.base + roomT + i.val, by
      have := B.room; have := i.isLt; show _ < B.L.ns + 2 + B.L.nr; omega⟩,
    fun a b h => Fin.ext (by have := congrArg Fin.val h; simp only at this; omega)⟩
  coreE_sc := fun i => by
    show decide _ = true
    simp only [Function.Embedding.coeFn_mk, decide_eq_true_eq]
    have := i.isLt
    omega

end NearCubicWires.WireExponent3_5.FinalPass.Bank
