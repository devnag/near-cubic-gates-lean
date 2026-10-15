import Proof.Wire_3_5.PrimTTabDock

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierPipeline

/-! ## Slots -/

def cellSl : Fin 1 → Fin 1789 := fun _ => 1721
def prepSl : Fin 13 → Fin 1789 := ![0, 1721, 1, 2, 7, 1714, 1680, 1704, 1705, 1715, 1716, 1717, 1722]
def polyV (j : ℕ) : ℕ := if j = 0 then 1714 else if j = 55 then 1700 else if j < 55 then 1724 + j else 1723 + j
def polySl (j : Fin 66) : Fin 1789 := ⟨polyV j.val, by have := j.isLt; unfold polyV; split_ifs <;> omega⟩
def chainSl (j : Fin 1708) : Fin 1789 := ⟨j.val + 6, by have := j.isLt; omega⟩
def scanSl : Fin 9 → Fin 1789 := ![1694, 1721, 1718, 1719, 1720, 5, 4, 1715, 1723]
def tabSl : Fin 11 → Fin 1789 := ![1718, 1721, 1719, 1, 1720, 3, 4, 1715, 1716, 1717, 1724]

theorem cellSl_inj : Function.Injective cellSl := fun a b _ => Subsingleton.elim a b
theorem prepSl_inj : Function.Injective prepSl := by decide
theorem scanSl_inj : Function.Injective scanSl := by decide
theorem tabSl_inj : Function.Injective tabSl := by decide
theorem polySl_inj : Function.Injective polySl := by
  intro a b h
  have hv : polyV a.val = polyV b.val := congrArg Fin.val h
  have := a.isLt; have := b.isLt
  apply Fin.ext; unfold polyV at hv; split_ifs at hv <;> omega
theorem chainSl_inj : Function.Injective chainSl := by
  intro a b h
  have hv : a.val + 6 = b.val + 6 := congrArg Fin.val h
  exact Fin.ext (by omega)

/-! ## The word stages' layouts -/

def spP : Fin 11 ↪ Fin 11 := ⟨id, fun _ _ h => h⟩
def scS : Fin 6 ↪ Fin 6 := ⟨id, fun _ _ h => h⟩
def smT : Fin 5 ↪ Fin 6 := ⟨fun i => i.castSucc, fun _ _ h => Fin.castSucc_injective _ h⟩
def rgT : Fin 3 ↪ Fin 3 := ⟨id, fun _ _ h => h⟩
def rgS : Fin 1 := 0

/-- The last word stage: the unary width, then the table. -/
def tabW2 : WM 5 3 := .seq (onesW scS) (tableW smT rgT)

/-- The capacity polynomial's coefficient (base's `CloseoutRowsCircuitCapacity.capacity`). -/
abbrev cC : ℕ := 1000000000000000000000000000000

/-- The machines of the stages. -/
noncomputable def cellD := RecoveryFocus.machine cellSl cellM
noncomputable def prepD := RecoveryFocus.machine prepSl (Rewind.machine (prepW (nr := 0) spP).toProg.compile)
noncomputable def polyD := RecoveryFocus.machine polySl (PCPSerializerCapacity.Power.machine 26 cC)
noncomputable def chainD := RecoveryFocus.machine chainSl SourceRequest.SymOriginal.chainA
noncomputable def scanD := RecoveryFocus.machine scanSl (Rewind.machine (scanW scS rgS).toProg.compile)
noncomputable def tabD := RecoveryFocus.machine tabSl (Rewind.machine tabW2.toProg.compile)

/-- **The SYM table machine.** -/
noncomputable def symTableM :=
  Composition.machine cellD (Composition.machine prepD (Composition.machine polyD
    (Composition.machine chainD (Composition.machine scanD tabD))))

/-! ## The entry states of the word stages -/

/-- The preparation's entry: the framed `natWord`, `1^n`, `1^L`, blank outputs. -/
def σP (code n L : ℕ) : WState 10 0 :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame (natWord code) else if i.val = 1 then List.replicate n true
    else if i.val = 2 then List.replicate L true else [], fun r => r.elim0, false⟩

/-- The scan's entry: the native word, blank outputs, the count register `0`. -/
def σS (w : List Bool) : WState 5 1 := ⟨fun _ => 0, fun i => if i.val = 0 then w else [], fun _ => 0, false⟩

/-- The table's entry: the two copies, `1^n`, the ruler, blank outputs, registers `0`. -/
def σT (seg : List Bool) (n h : ℕ) : WState 5 3 :=
  ⟨fun _ => 0, fun i => if i.val = 0 then seg else if i.val = 1 then seg else if i.val = 2 then List.replicate n true
    else if i.val = 3 then false :: List.replicate h true else [], fun _ => 0, false⟩

end NearCubicWires.WireExponent3_5.PrimT.SymTab
