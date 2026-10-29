import SourceAdapters.RAMACSP.EmbedGuards

/-!
# Embedding theorem, part 2: the catalog lists

Paper: `app:affine-embedding`, "Placement". Each active slot and each
equation instance receives its own point. TIME and SORT templates are listed
in increasing tag order, with their active bit indices; the slot lists cover
exactly the semantic bits of their catalog blocks.-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMTrace Blocks

/-! ## TIME templates in increasing tag order -/

/-- **The TIME templates have distinct hosts** (`app:affine-embedding` TIME templates (exactly `3K+2L+32 = Ftags`), tags assigned
consecutively in the displayed order; `L ≥ 1`). -/
theorem timeEqList_blk (d : Dims) (hL : 1 ≤ d.L) :
    Blk (tTag d.K d.L) (fun q q' => (tTag d.K d.L q, tBit q) ≠ (tTag d.K d.L q', tBit q')) 0
      (3 * d.K + 2 * d.L + 32) (timeEqList d) := by
  have hR : ∀ a b : TEq, tTag d.K d.L a < tTag d.K d.L b →
      (tTag d.K d.L a, tBit a) ≠ (tTag d.K d.L b, tBit b) := fun a b h he => by
    simp only [Prod.mk.injEq] at he; omega
  unfold timeEqList
  exact
    (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.flatStep d.K d.w 0 TEq.flag (fun r j => by simp only [tTag]; omega) hR (fun r i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega))
        (Blk.single TEq.decFirst (d.K) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapStep (d.L - 1) (d.K + 1) (fun p => TEq.decRec (p + 1)) (fun p => by simp only [tTag]; omega) hR) hR (by omega) (by omega) (by omega))
        (Blk.mapStep (d.L - 1) (d.K + d.L) (fun p => TEq.decExcl (p + 1)) (fun p => by simp only [tTag]; omega) hR) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.decLast (d.K + 2 * d.L - 1) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 0) TEq.decPc (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 1) TEq.opX (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 2) TEq.opY (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.opXF (d.K + 2 * d.L + 3) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 4) TEq.sumAD (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst (d.w - 1) (d.K + 2 * d.L + 5) TEq.carry (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 6) TEq.sumSB (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 7) TEq.borrow (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 8) TEq.andAN (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.ozFirst (d.K + 2 * d.L + 9) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapConst (d.w - 1) (d.K + 2 * d.L + 10) (fun j => TEq.ozRec (j + 1)) (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.gt (d.K + 2 * d.L + 11) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 12) TEq.rfFlag (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 13) TEq.store (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (d.K + 2 * d.L + 14) TEq.res (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.resF (d.K + 2 * d.L + 15) rfl) hR (by omega) (by omega) (by omega))
        (Blk.flatStep d.K d.w (d.K + 2 * d.L + 16) TEq.reg (fun r j => by simp only [tTag]) hR (fun r i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapStep d.K (2 * d.K + 2 * d.L + 16) TEq.regF (fun r => by simp only [tTag]) hR) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (3 * d.K + 2 * d.L + 16) TEq.pcNext (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.app (Blk.single TEq.recAct (3 * d.K + 2 * d.L + 17) rfl) (Blk.single TEq.recRgn (3 * d.K + 2 * d.L + 18) rfl) hR (by omega) (by omega) (by omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (3 * d.K + 2 * d.L + 19) TEq.recAd (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.recPh (3 * d.K + 2 * d.L + 20) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.w (3 * d.K + 2 * d.L + 21) TEq.recVa (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.recSt (3 * d.K + 2 * d.L + 22) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.τ (3 * d.K + 2 * d.L + 23) TEq.tsn (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst (d.τ - 1) (3 * d.K + 2 * d.L + 24) TEq.tc (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.aA (3 * d.K + 2 * d.L + 25) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.τ (3 * d.K + 2 * d.L + 26) TEq.can (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst (d.τ - 1) (3 * d.K + 2 * d.L + 27) TEq.ac (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.aB (3 * d.K + 2 * d.L + 28) rfl) hR (by omega) (by omega) (by omega))
        (Blk.mapConst (d.β + 1) (3 * d.K + 2 * d.L + 29) TEq.cbn (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.mapConst d.β (3 * d.K + 2 * d.L + 30) TEq.bc (fun _ => rfl) (fun i j _ he => by simp only [tTag, tBit, Prod.mk.injEq] at he; omega)) hR (by omega) (by omega) (by omega))
        (Blk.single TEq.bound (3 * d.K + 2 * d.L + 31) rfl) hR (by omega) (by omega) (by omega))

/-! ## The time-row slots and the copies are listed without repetition -/

/-- The block index of a time-row slot in `timeSlotList` (list order). -/
def tslotCls : TSlot → ℕ
  | .pc _ => 0
  | .fl _ => 1
  | .rg _ _ => 2
  | .e _ => 3
  | .o _ => 4
  | .X _ => 5
  | .XF => 6
  | .Y _ => 7
  | .AD _ => 8
  | .CA _ => 9
  | .SB _ => 10
  | .BO _ => 11
  | .AN _ => 12
  | .OZ _ => 13
  | .GT => 14
  | .Z _ => 15
  | .ZF => 16
  | .RV _ => 17
  | .RF => 18
  | .MV _ => 19
  | .TC _ => 20
  | .cA _ => 21
  | .cB _ => 22
  | .AC _ => 23
  | .BC _ => 24
  | .aA => 25
  | .aB => 26
  | .npc _ => 27
  | .nfl _ => 28
  | .nrg _ _ => 29
  | .ncA _ => 30
  | .ncB _ => 31
  | .TSN _ => 32

theorem timeSlotList_nodup (d : Dims) : (timeSlotList d).Nodup := by
  have hR : ∀ a b : TSlot, tslotCls a < tslotCls b → a ≠ b := fun a b h he => by subst he; omega
  have h : Blk tslotCls (fun a b => a ≠ b) 0 33 (timeSlotList d) := by
    unfold timeSlotList
    exact
      (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.mapConst d.w 0 TSlot.pc (fun _ => rfl) (fun i j _ he => by injection he; omega))
          (Blk.mapConst d.K 1 TSlot.fl (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.flatConst d.K d.w 2 TSlot.rg (fun _ _ => rfl) (fun r r' i j h he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.L 3 TSlot.e (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.L 4 TSlot.o (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 5 TSlot.X (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.single TSlot.XF 6 rfl) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 7 TSlot.Y (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 8 TSlot.AD (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst (d.w - 1) 9 TSlot.CA (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 10 TSlot.SB (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 11 TSlot.BO (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 12 TSlot.AN (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 13 TSlot.OZ (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.single TSlot.GT 14 rfl) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 15 TSlot.Z (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.single TSlot.ZF 16 rfl) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 17 TSlot.RV (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.single TSlot.RF 18 rfl) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 19 TSlot.MV (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst (d.τ - 1) 20 TSlot.TC (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.τ 21 TSlot.cA (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst (d.β + 1) 22 TSlot.cB (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst (d.τ - 1) 23 TSlot.AC (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.β 24 TSlot.BC (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.app (Blk.single TSlot.aA 25 rfl) (Blk.single TSlot.aB 26 rfl) hR (by omega) (by omega) (by omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.w 27 TSlot.npc (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.K 28 TSlot.nfl (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.flatConst d.K d.w 29 TSlot.nrg (fun _ _ => rfl) (fun r r' i j h he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.τ 30 TSlot.ncA (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst (d.β + 1) 31 TSlot.ncB (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.τ 32 TSlot.TSN (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
  exact h.1

/-- The block index of a copy in `copyList` (list order). -/
def tcopyCls : TCopy → ℕ
  | .pc _ => 0
  | .fl _ => 1
  | .rg _ _ => 2
  | .ts _ => 3
  | .cA _ => 4
  | .cB _ => 5

theorem copyList_nodup (d : Dims) : (copyList d).Nodup := by
  have hR : ∀ a b : TCopy, tcopyCls a < tcopyCls b → a ≠ b := fun a b h he => by subst he; omega
  have h : Blk tcopyCls (fun a b => a ≠ b) 0 6 (copyList d) := by
    unfold copyList
    exact
      (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.mapConst d.w 0 TCopy.pc (fun _ => rfl) (fun i j _ he => by injection he; omega))
          (Blk.mapConst d.K 1 TCopy.fl (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.flatConst d.K d.w 2 TCopy.rg (fun _ _ => rfl) (fun r r' i j h he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.τ 3 TCopy.ts (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst d.τ 4 TCopy.cA (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
          (Blk.mapConst (d.β + 1) 5 TCopy.cB (fun _ => rfl) (fun i j _ he => by injection he; omega)) hR (by omega) (by omega) (by omega))
  exact h.1


/-! ## SORT templates and sorted slots in increasing tag order -/

theorem eq_of_div_mod {w l l' : ℕ} (h1 : l / w = l' / w) (h2 : l % w = l' % w) : l = l' := by
  rw [← Nat.div_add_mod l w, ← Nat.div_add_mod l' w, h1, h2]

/-- The `S2` borrow templates of key bits `l < κ` sit at tags `2 + ⌊l/w⌋ < 5`, bit `l mod w`. -/
theorem blk_borrow (d : Dims) (hw : 1 ≤ d.w) (hκ : d.κ ≤ 3 * d.w) :
    Blk (sTag d.w) (fun q q' => (sTag d.w q, sBit d.w q) ≠ (sTag d.w q', sBit d.w q')) 2 5
      ((List.range d.κ).map SEq.borrow) := by
  refine ⟨List.pairwise_map.mpr (List.pairwise_lt_range.imp fun {i j} h he => ?_), fun a ha => ?_⟩
  · simp only [sTag, sBit, Prod.mk.injEq] at he
    have := eq_of_div_mod (w := d.w) (by omega) he.2
    omega
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    have hl' := List.mem_range.mp hl
    have : l / d.w < 3 := by rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d.w)]; omega
    simp only [sTag]; generalize l / d.w = q at *; omega

/-- **The SORT templates have distinct hosts** (`app:affine-embedding` SORT templates (exactly 17)). -/
theorem sortEqList_blk (d : Dims) (hw : 1 ≤ d.w) (hκ : d.κ ≤ 3 * d.w) :
    Blk (sTag d.w) (fun q q' => (sTag d.w q, sBit d.w q) ≠ (sTag d.w q', sBit d.w q')) 0 17 (sortEqList d) := by
  have hR : ∀ a b : SEq, sTag d.w a < sTag d.w b → (sTag d.w a, sBit d.w a) ≠ (sTag d.w b, sBit d.w b) :=
    fun a b h he => by simp only [Prod.mk.injEq] at he; omega
  have RT : ∀ (C : ℕ → SEq), (∀ j, sBit d.w (C j) = j) → ∀ i j, i < j →
      (sTag d.w (C i), sBit d.w (C i)) ≠ (sTag d.w (C j), sBit d.w (C j)) := fun C hC i j h he => by
    simp only [Prod.mk.injEq, hC] at he; omega
  unfold sortEqList
  exact Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app
    (Blk.app (Blk.single SEq.act 0 rfl) (Blk.single SEq.both 1 rfl) hR (by omega) (by omega) (by omega))
    (blk_borrow d hw hκ) hR (by omega) (by omega) (by omega))
    (Blk.app (Blk.single SEq.strict 5 rfl) (Blk.single SEq.soFirst 6 rfl) hR (by omega) (by omega) (by omega))
      hR (by omega) (by omega) (by omega))
    (Blk.mapConst d.w 7 SEq.soNext (fun _ => rfl) (RT _ fun _ => rfl)) hR (by omega) (by omega) (by omega))
    (Blk.app (Blk.single SEq.u 8 rfl) (Blk.single SEq.g 9 rfl) hR (by omega) (by omega) (by omega))
      hR (by omega) (by omega) (by omega))
    (Blk.mapConst d.w 10 SEq.ev (fun _ => rfl) (RT _ fun _ => rfl)) hR (by omega) (by omega) (by omega))
    (Blk.mapConst d.w 11 SEq.load (fun _ => rfl) (RT _ fun _ => rfl)) hR (by omega) (by omega) (by omega))
    (Blk.app (Blk.app (Blk.app (Blk.single SEq.gA1 12 rfl) (Blk.single SEq.gA 13 rfl) hR (by omega) (by omega)
      (by omega)) (Blk.single SEq.same 14 rfl) hR (by omega) (by omega) (by omega))
      (Blk.single SEq.phase 15 rfl) hR (by omega) (by omega) (by omega)) hR (by omega) (by omega) (by omega))
    (Blk.mapConst d.w 16 SEq.value (fun _ => rfl) (RT _ fun _ => rfl)) hR (by omega) (by omega) (by omega)

/-- The sorted-slot relation: distinct column codes `(tag, bit)`. -/
abbrev SNe (w : ℕ) (s s' : SSlot) : Prop :=
  ((sCell w s).tag, (sCell w s).bit) ≠ ((sCell w s').tag, (sCell w s').bit)

theorem blk_ob (d : Dims) (hw : 1 ≤ d.w) (hκ : d.κ ≤ 3 * d.w) :
    Blk (fun s => (sCell d.w s).tag) (SNe d.w) 8 11 ((List.range d.κ).map SSlot.ob) := by
  refine ⟨List.pairwise_map.mpr (List.pairwise_lt_range.imp fun {i j} h he => ?_), fun a ha => ?_⟩
  · simp only [sCell, Prod.mk.injEq] at he
    have := eq_of_div_mod (w := d.w) (by omega) he.2
    omega
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    have hl' := List.mem_range.mp hl
    have : l / d.w < 3 := by rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d.w)]; omega
    simp only [sCell]; generalize l / d.w = q at *; omega

theorem sCell_so (w l : ℕ) : sCell w (.so l) = if l < w then ⟨12, l, 0, 1⟩ else ⟨13, 0, 0, 1⟩ := rfl

theorem blk_so (w : ℕ) : Blk (fun s => (sCell w s).tag) (SNe w) 12 14 ((List.range (w + 1)).map SSlot.so) := by
  refine ⟨List.pairwise_map.mpr ((List.Pairwise.and_mem.mp (List.pairwise_lt_range (n := w + 1))).imp
    fun {i j} h he => ?_), fun a ha => ?_⟩
  · obtain ⟨-, hj, h⟩ := h
    have hj' := List.mem_range.mp hj
    simp only [sCell_so] at he
    by_cases hi : i < w <;> by_cases hj : j < w <;> simp only [hi, hj, if_true, if_false, Prod.mk.injEq] at he <;>
      omega
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    simp only [sCell_so]
    by_cases hl : l < w <;> simp [hl]

/-- **The sorted slots have distinct column codes** (`app:affine-embedding` Sorted values: `PREV` at the record tags `0..5`, role `1`;
`OB_0..OB_2, BOTH, SO_0, SO_1, U, G, EV, GA1, GA` at tags `8..18`). -/
theorem sortSlotList_blk (d : Dims) (hw : 1 ≤ d.w) (hκ : d.κ ≤ 3 * d.w) :
    Blk (fun s => (sCell d.w s).tag) (SNe d.w) 0 19 (sortSlotList d) := by
  have hR : ∀ a b : SSlot, (sCell d.w a).tag < (sCell d.w b).tag → SNe d.w a b :=
    fun a b h he => by simp only [Prod.mk.injEq] at he; omega
  have RP : ∀ f : RecField, ∀ i j, i < j → SNe d.w (SSlot.prev f i) (SSlot.prev f j) := fun f i j h he => by
    simp only [sCell, Prod.mk.injEq] at he; omega
  have RT : ∀ (C : ℕ → SSlot), (∀ j, (sCell d.w (C j)).bit = j) → ∀ i j, i < j → SNe d.w (C i) (C j) :=
    fun C hC i j h he => by simp only [Prod.mk.injEq, hC] at he; omega
  have hprev : Blk (fun s => (sCell d.w s).tag) (SNe d.w) 0 6
      ([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
        (List.range (f.width d.w d.τ)).map fun j => SSlot.prev f j) := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact Blk.app (Blk.mapConst _ 0 _ (fun _ => rfl) (RP _)) (Blk.app (Blk.mapConst _ 1 _ (fun _ => rfl) (RP _))
      (Blk.app (Blk.mapConst _ 2 _ (fun _ => rfl) (RP _)) (Blk.app (Blk.mapConst _ 3 _ (fun _ => rfl) (RP _))
        (Blk.app (Blk.mapConst _ 4 _ (fun _ => rfl) (RP _)) (Blk.mapConst _ 5 _ (fun _ => rfl) (RP _))
          hR (by omega) (by omega) (by omega)) hR (by omega) (by omega) (by omega))
        hR (by omega) (by omega) (by omega)) hR (by omega) (by omega) (by omega)) hR (by omega) (by omega) (by omega)
  unfold sortSlotList
  exact Blk.app (Blk.app (Blk.app (Blk.app (Blk.app (Blk.app hprev (blk_ob d hw hκ) hR (by omega) (by omega)
    (by omega)) (Blk.single SSlot.both 11 rfl) hR (by omega) (by omega) (by omega)) (blk_so d.w) hR (by omega)
    (by omega) (by omega))
    (Blk.app (Blk.single SSlot.u 14 rfl) (Blk.single SSlot.g 15 rfl) hR (by omega) (by omega) (by omega))
      hR (by omega) (by omega) (by omega))
    (Blk.mapConst d.w 16 SSlot.ev (fun _ => rfl) (RT _ fun _ => rfl)) hR (by omega) (by omega) (by omega))
    (Blk.app (Blk.single SSlot.gA1 17 rfl) (Blk.single SSlot.gA 18 rfl) hR (by omega) (by omega) (by omega))
      hR (by omega) (by omega) (by omega)

/-! ## Record slots by field -/

/-- The record-slot relation: distinct `(tag, bit)`. -/
abbrev RNe (s s' : RecSlot) : Prop := (s.1.tag, s.2) ≠ (s'.1.tag, s'.2)

theorem fields_blk_aux (f : RecField) (n : ℕ) :
    Blk (fun s : RecSlot => s.1.tag) RNe f.tag (f.tag + 1) ((List.range n).map fun j => (f, j)) :=
  Blk.mapConst n f.tag _ (fun _ => rfl) fun i j h he => by simp only [Prod.mk.injEq] at he; omega

theorem rne_of_lt : ∀ a b : RecSlot, a.1.tag < b.1.tag → RNe a b :=
  fun a b h he => by simp only [Prod.mk.injEq] at he; omega

/-- **The six `PREV` fields have distinct cells** (`app:affine-embedding`: Role1 tags0..5 store PREV.va, …, PREV.act). -/
theorem fields6_blk (wd : RecField → ℕ) :
    Blk (fun s : RecSlot => s.1.tag) RNe 0 6
      ([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f => (List.range (wd f)).map fun j => (f, j)) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact Blk.app (fields_blk_aux .va _) (Blk.app (fields_blk_aux .ad _) (Blk.app (fields_blk_aux .ts _)
    (Blk.app (fields_blk_aux .ph _) (Blk.app (fields_blk_aux .rgn _) (fields_blk_aux .act _)
      rne_of_lt (by decide) (by decide) (by decide)) rne_of_lt (by decide) (by decide) (by decide))
      rne_of_lt (by decide) (by decide) (by decide)) rne_of_lt (by decide) (by decide) (by decide))
      rne_of_lt (by decide) (by decide) (by decide)

/-- **The seven record fields have distinct cells** (`app:affine-embedding` Routed REC, area0 role0). -/
theorem recSlotList_blk (d : Dims) : Blk (fun s : RecSlot => s.1.tag) RNe 0 7 (recSlotList d) := by
  unfold recSlotList recFields
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact Blk.app (fields_blk_aux .va _) (Blk.app (fields_blk_aux .ad _) (Blk.app (fields_blk_aux .ts _)
    (Blk.app (fields_blk_aux .ph _) (Blk.app (fields_blk_aux .rgn _) (Blk.app (fields_blk_aux .act _)
      (fields_blk_aux .st _) rne_of_lt (by decide) (by decide) (by decide))
      rne_of_lt (by decide) (by decide) (by decide)) rne_of_lt (by decide) (by decide) (by decide))
      rne_of_lt (by decide) (by decide) (by decide)) rne_of_lt (by decide) (by decide) (by decide))
      rne_of_lt (by decide) (by decide) (by decide)


/-! ## The catalog cell is injective on active slots -/

set_option maxHeartbeats 400000 in
/-- **Distinct active time-row slots occupy distinct cells** (`app:affine-embedding` Time values: an explicit ordered tag list). -/
theorem tCell_inj (d : Dims) (K L : ℕ) (hK : d.K = K) (hL : d.L = L) (s s' : TSlot) (hs : s.Active d)
    (hs' : s'.Active d) (h1 : (tCell K L s).tag = (tCell K L s').tag) (h2 : (tCell K L s).bit = (tCell K L s').bit)
    (h3 : (tCell K L s).role = (tCell K L s').role) : s = s' := by
  cases s <;> cases s' <;> simp only [tCell, blockBase, TSlot.Active, TSlot.pc.injEq, TSlot.fl.injEq,
    TSlot.rg.injEq, TSlot.e.injEq, TSlot.o.injEq, TSlot.X.injEq, TSlot.Y.injEq, TSlot.AD.injEq, TSlot.CA.injEq,
    TSlot.SB.injEq, TSlot.BO.injEq, TSlot.AN.injEq, TSlot.OZ.injEq, TSlot.Z.injEq, TSlot.RV.injEq, TSlot.MV.injEq,
    TSlot.TC.injEq, TSlot.cA.injEq, TSlot.cB.injEq, TSlot.AC.injEq, TSlot.BC.injEq, TSlot.npc.injEq,
    TSlot.nfl.injEq, TSlot.nrg.injEq, TSlot.ncA.injEq, TSlot.ncB.injEq, TSlot.TSN.injEq, reduceCtorEq] at * <;>
    omega

/-- **Distinct active copies have distinct destination columns** (`ts` is the routed tag `2`; the others are the
time role-`0` tags). -/
theorem dstCell_inj (d : Dims) (K L : ℕ) (hK : d.K = K) (hL : d.L = L) (cp cp' : TCopy) (hc : cp.Active d)
    (hc' : cp'.Active d) (h1 : (dstCell K L cp).tag = (dstCell K L cp').tag)
    (h2 : (dstCell K L cp).bit = (dstCell K L cp').bit) : cp = cp' := by
  cases cp <;> cases cp' <;> simp only [dstCell, TCopy.dst, tCell, recCell, RecField.tag, blockBase, TCopy.Active,
    TCopy.pc.injEq, TCopy.fl.injEq, TCopy.rg.injEq, TCopy.ts.injEq, TCopy.cA.injEq, TCopy.cB.injEq,
    reduceCtorEq] at * <;> omega

/-- The record field of a tag `0..5`. -/
def fieldOfTag : ℕ → RecField
  | 0 => .va
  | 1 => .ad
  | 2 => .ts
  | 3 => .ph
  | 4 => .rgn
  | 5 => .act
  | _ => .st

/-- The sorted slot of a cell `(tag, bit)` (inverse of `sCell` on active slots). -/
def decS (w tag bit : ℕ) : SSlot :=
  if tag < 6 then .prev (fieldOfTag tag) bit
  else if tag < 11 then .ob ((tag - 8) * w + bit)
  else if tag = 11 then .both
  else if tag = 12 then .so bit
  else if tag = 13 then .so w
  else if tag = 14 then .u
  else if tag = 15 then .g
  else if tag = 16 then .ev bit
  else if tag = 17 then .gA1
  else .gA

theorem decS_sCell (d : Dims) (hw : 1 ≤ d.w) (hκ : d.κ ≤ 3 * d.w) (s : SSlot) (hs : s.Active d) :
    decS d.w (sCell d.w s).tag (sCell d.w s).bit = s := by
  cases s with
  | prev f j =>
    obtain ⟨hf, -⟩ := hs
    cases f <;> first | exact absurd rfl hf | rfl
  | ob l =>
    have hl : l < d.κ := hs
    have h3 : l / d.w < 3 := by rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d.w)]; omega
    simp only [sCell, decS]
    have e6 : ¬ (8 + l / d.w < 6) := Nat.not_lt.mpr (Nat.le_add_right_of_le (by norm_num))
    have e11 : 8 + l / d.w < 11 := by generalize l / d.w = q at *; omega
    rw [if_neg e6, if_pos e11, Nat.add_sub_cancel_left, Nat.div_add_mod']
  | so l =>
    have hl : l ≤ d.w := hs
    simp only [sCell_so]
    by_cases h : l < d.w
    · simp only [h, if_true, decS]; rfl
    · have : l = d.w := by omega
      subst this
      simp only [h, if_false, decS]; rfl
  | _ => rfl

/-- **Distinct active sorted slots have distinct column codes** (`app:affine-embedding` Sorted values). -/
theorem sCell_inj (d : Dims) (hw : 1 ≤ d.w) (hκ : d.κ ≤ 3 * d.w) (s s' : SSlot) (hs : s.Active d)
    (hs' : s'.Active d) (h1 : (sCell d.w s).tag = (sCell d.w s').tag) (h2 : (sCell d.w s).bit = (sCell d.w s').bit) :
    s = s' := by
  rw [← decS_sCell d hw hκ s hs, ← decS_sCell d hw hκ s' hs', h1, h2]

/-! ## Every active instance is listed -/

theorem exists_pred_lt (p n : ℕ) (h1 : 1 ≤ p) (h2 : p < n) : ∃ a, a < n - 1 ∧ a + 1 = p :=
  ⟨p - 1, by omega, by omega⟩

/-- **The TIME catalog is complete**: every active equation instance is listed. -/
theorem mem_timeEqList_of_active (d : Dims) (q : TEq) (hq : q.Active d) : q ∈ timeEqList d := by
  cases q <;> simp only [TEq.Active] at hq <;>
    simp only [timeEqList, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, and_false, exists_false, or_false, false_or,
      TEq.flag.injEq, TEq.decRec.injEq, TEq.decExcl.injEq,
    TEq.decPc.injEq, TEq.opX.injEq, TEq.opY.injEq, TEq.sumAD.injEq, TEq.carry.injEq, TEq.sumSB.injEq,
    TEq.borrow.injEq, TEq.andAN.injEq, TEq.ozRec.injEq, TEq.rfFlag.injEq, TEq.store.injEq, TEq.res.injEq,
    TEq.reg.injEq, TEq.regF.injEq, TEq.pcNext.injEq, TEq.recAd.injEq, TEq.recVa.injEq, TEq.tsn.injEq,
    TEq.tc.injEq, TEq.can.injEq, TEq.ac.injEq, TEq.cbn.injEq, TEq.bc.injEq, exists_eq_right, exists_eq_right_right,
    or_true] <;> first | omega | exact exists_pred_lt _ _ (by omega) (by omega)

/-- **The time-row slots are complete**. -/
theorem mem_timeSlotList_of_active (d : Dims) (s : TSlot) (hs : s.Active d) : s ∈ timeSlotList d := by
  cases s <;> simp only [TSlot.Active] at hs <;>
    simp only [timeSlotList, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, and_false, exists_false, or_false, false_or, TSlot.pc.injEq,
      TSlot.fl.injEq, TSlot.rg.injEq, TSlot.e.injEq, TSlot.o.injEq, TSlot.X.injEq, TSlot.Y.injEq, TSlot.AD.injEq,
      TSlot.CA.injEq, TSlot.SB.injEq, TSlot.BO.injEq, TSlot.AN.injEq, TSlot.OZ.injEq, TSlot.Z.injEq,
      TSlot.RV.injEq, TSlot.MV.injEq, TSlot.TC.injEq, TSlot.cA.injEq, TSlot.cB.injEq, TSlot.AC.injEq,
      TSlot.BC.injEq, TSlot.npc.injEq, TSlot.nfl.injEq, TSlot.nrg.injEq, TSlot.ncA.injEq, TSlot.ncB.injEq,
      TSlot.TSN.injEq, exists_eq_right, exists_eq_right_right, or_true] <;> omega

/-- **The copies are complete**. -/
theorem mem_copyList_of_active (d : Dims) (c : TCopy) (hc : c.Active d) : c ∈ copyList d := by
  cases c <;> simp only [TCopy.Active] at hc <;>
    simp only [copyList, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
      reduceCtorEq, and_false, exists_false, or_false, false_or, TCopy.pc.injEq, TCopy.fl.injEq, TCopy.rg.injEq,
      TCopy.ts.injEq, TCopy.cA.injEq, TCopy.cB.injEq, exists_eq_right, exists_eq_right_right] <;> omega

/-- **The SORT catalog is complete**. -/
theorem mem_sortEqList_of_active (d : Dims) (q : SEq) (hq : q.Active d) : q ∈ sortEqList d := by
  cases q <;> simp only [SEq.Active] at hq <;>
    simp only [sortEqList, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, and_false, exists_false, or_false, false_or, SEq.borrow.injEq,
      SEq.soNext.injEq, SEq.ev.injEq, SEq.load.injEq, SEq.value.injEq, exists_eq_right, or_true] <;>
    omega

/-- **The record slots are complete**. -/
theorem mem_recSlotList_of_active (d : Dims) (s : RecSlot) (hs : s.Active d) : s ∈ recSlotList d := by
  obtain ⟨f, j⟩ := s
  simp only [recSlotList, recFields, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq]
  exact ⟨f, by cases f <;> simp, j, hs, rfl, rfl⟩

/-- **The `PREV` slots are complete** (the six fields other than `st`). -/
theorem mem_prevSlots_of_active (w τ : ℕ) (f : RecField) (j : ℕ) (hf : f ≠ .st) (hj : j < f.width w τ) :
    (f, j) ∈ [RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
      (List.range (f.width w τ)).map fun j => (f, j) := by
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  exact ⟨f, by cases f <;> simp_all, j, hj, rfl, rfl⟩

/-- **The sorted slots are complete**. -/
theorem mem_sortSlotList_of_active (d : Dims) (s : SSlot) (hs : s.Active d) : s ∈ sortSlotList d := by
  cases s with
  | prev f j =>
    obtain ⟨hf, hj⟩ := hs
    unfold sortSlotList
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ ?_)))))
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
      SSlot.prev.injEq]
    exact ⟨f, by cases f <;> simp_all, j, hj, rfl, rfl⟩
  | _ =>
    simp only [SSlot.Active] at hs
    simp only [sortSlotList, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, reduceCtorEq, and_false, exists_false, or_false, false_or, SSlot.ob.injEq, SSlot.so.injEq,
      SSlot.ev.injEq, exists_eq_right, or_true] <;> omega

end NearCubicGates.Adapters.RAMACSP
