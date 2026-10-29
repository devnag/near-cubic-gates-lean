import SourceAdapters.Proximity.AuxiliaryAddress
import SourceAdapters.Proximity.OriginalAddress
import SourceAdapters.Proximity.QueryStep

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the odd-address branch in the
constructor's fixed register bank, preserving the current block output. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.AuxiliaryCase

open NearCubicWires NearCubicGates.Close.Cells
open SourceRequests (State Script)
open QueryStep (rowReg boundReg)
open SourceResults (resultReg)
open OriginalAddress (kindReg addressReg)

def auxiliaryReg : Fin VV := 35
def squareReg : Fin VV := 36
def registers : Fin 6 ↪ Fin VV := ⟨![rowReg, resultReg, boundReg, auxiliaryReg, squareReg, addressReg], by decide⟩
def scratch : List (Fin VV) := [auxiliaryReg, squareReg, addressReg, kindReg]

def auxiliaryCase : Script :=
  .seq (Pairing.auxiliaryProgram registers) (.op (.copy kindReg v1))

theorem auxiliary_case (C : Ctx) (a : State) (hc : Cst a) (row localIndex q : ℕ)
    (hr : a.env rowReg = row) (hi : a.env resultReg = localIndex) (hq : a.env boundReg = q)
    (hle : q ≤ localIndex) (hW : 2 * Nat.pair row (localIndex - q) + 1 < 2 ^ C.Wd) :
    Hs C auxiliaryCase a 18 (fun b =>
      b.env kindReg = 1 ∧ b.env addressReg = 2 * Nat.pair row (localIndex - q) + 1 ∧
      Same a b ∧ Fr a b scratch) := by
  have e1 := Pairing.auxiliary_program C registers a row localIndex q hr hi hq hle hW
  let b := (((a.set auxiliaryReg (localIndex - q)).set squareReg (max row (localIndex - q))).set
    addressReg (2 * Nat.pair row (localIndex - q) + 1))
  change Ex C (Pairing.auxiliaryProgram registers) a b 16 at e1
  have hb1 : b.env v1 = 1 := by
    change (((a.set auxiliaryReg (localIndex - q)).set squareReg (max row (localIndex - q))).set
      addressReg (2 * Nat.pair row (localIndex - q) + 1)).env v1 = 1
    rw [DS.set_env_ne _ _ (by decide : v1 ≠ addressReg),
      DS.set_env_ne _ _ (by decide : v1 ≠ squareReg), DS.set_env_ne _ _ (by decide : v1 ≠ auxiliaryReg)]
    exact hc.one
  have e2 := Ex.op (OpEx.copy (C := C) kindReg v1 b (by decide))
  rw [hb1] at e2
  refine ⟨_, _, Ex.seq e1 e2, le_rfl, by simp, ?_, ?_, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide : addressReg ≠ kindReg)]
    simp [b]
  · exact (Same.set a _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans (Same.set _ _ _)))
  · intro x hx
    have ha : x ≠ auxiliaryReg := fun h => hx (by simp [scratch, h])
    have hs : x ≠ squareReg := fun h => hx (by simp [scratch, h])
    have hv : x ≠ addressReg := fun h => hx (by simp [scratch, h])
    have hk : x ≠ kindReg := fun h => hx (by simp [scratch, h])
    simp [b, DS.set, ha, hs, hv, hk]

end NearCubicGates.Adapters.Proximity.AuxiliaryCase
