import Proof.Gates.Cells.Loop
import Proof.Gates.CounterMachine.TabCallSpec

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.CellTables

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairOrdinary (SignedSortKey.binary)

/-- Input variables of the fragments. -/
def vS : Fin VV := ⟨40, by decide⟩    -- `s` (outer width)
def vH1 : Fin VV := ⟨41, by decide⟩   -- `2^⌈s/2⌉` (rows: low bits of the outer index)
def vH0 : Fin VV := ⟨42, by decide⟩   -- `2^⌊s/2⌋` (columns: high bits)
def vSH : Fin VV := ⟨43, by decide⟩   -- the index multiplier
def vKY : Fin VV := ⟨44, by decide⟩   -- the key part of the record
def vQE : Fin VV := ⟨45, by decide⟩   -- `q^e` (residue requests)
def vRS : Fin VV := ⟨46, by decide⟩   -- `1` residue request, `0` moment request
def vRW : Fin VV := ⟨47, by decide⟩   -- record width (`finP`)

/-- Scratch variables of the fragments. -/
def scr : List (Fin VV) := (List.range 16).map fun j => ⟨48 + j % 16, by have := Nat.mod_lt j (show 0 < 16 by decide); unfold VV; omega⟩

/-- The record store and the fragments' scratch store. -/
def sREC : Fin MM := ⟨2, by decide⟩
def sTMP : Fin MM := ⟨3, by decide⟩

/-- The record of outer index `i` with table entry `z`. -/
def recOf (SH KY QE : ℕ) (res : Bool) (i : ℕ) (z : ℤ) : ℕ :=
  i * SH + KY + (if res then (z % (QE : ℤ)).toNat else z.toNat)

/-- The frame of a fragment: only the scratch variables, `sREC`, `sTMP` and the named cursor change. -/
structure Frame (a b : DS VV MM) : Prop where
  fr : Fr a b scr
  ip : b.ip = a.ip
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  ram : ∀ m, m ≠ sREC → m ≠ sTMP → b.ram m = a.ram m
  rc : ∀ m, m ≠ sREC → m ≠ sTMP → b.rc m = a.rc m

def ConvSpec (convP : St VV MM) : Prop :=
  ∀ (C : Ctx) (a : DS VV MM) (s w SH KY QE : ℕ) (res : Bool) (z : ℕ → ℤ),
    Valid C a → Cst a → a.env vS = s → a.env vH1 = 2 ^ ((s + 1) / 2) → a.env vH0 = 2 ^ (s / 2) →
    a.env vSH = SH → a.env vKY = KY → a.env vQE = QE → a.env vRS = (if res then 1 else 0) → (res = true → 0 < QE) →
    a.kout = WordPrograms.recStream ((printerOrder s).map fun i => SignedSortKey.binary w (WordPrograms.SInt.encS (z i))) →
    a.kc = 0 → 1 ≤ w → (∀ i < 2 ^ s, WordPrograms.SInt.encS (z i) < 2 ^ w) →
    w + s + 2 ≤ C.Wd → 2 * QE < 2 ^ C.Wd → (∀ i < 2 ^ s, recOf SH KY QE res i (z i) < 2 ^ C.Wd) →
    a.rc sREC = (a.ram sREC).length →
    Hs C convP a (100 * 2 ^ s * (w + 10) + 100) (fun b =>
      b.ram sREC = a.ram sREC ++ (printerOrder s).map (fun i => recOf SH KY QE res i (z i)) ∧
      b.rc sREC = (b.ram sREC).length ∧ b.out = a.out ∧ Frame a b)

def FinSpec (finP : St VV MM) : Prop :=
  ∀ (C : Ctx) (a : DS VV MM) (RW : ℕ) (recs : List ℕ),
    Valid C a → Cst a → a.env vRW = RW → 1 ≤ RW → RW + 2 ≤ C.Wd → a.ram sREC = recs → a.rc sREC = recs.length →
    (∀ v ∈ recs, v < 2 ^ RW) →
    Hs C finP a (100 * (recs.length + 1) * (RW + 10)) (fun b =>
      b.out = a.out ++ WordPrograms.recStream ((recs.insertionSort (· ≤ ·)).map (SignedSortKey.binary RW)) ∧
      b.kc = a.kc ∧ Frame a b)

end NearCubicGates.Close.CounterMachine.CellTables
