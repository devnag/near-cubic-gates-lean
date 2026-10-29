import SourceAdapters.Routing.TermsMachineItemsProgram
import SourceAdapters.Routing.CoordinateMachineInput

/-! # Flag-controlled iteration over the serialized item list -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Items

open NearCubicWires NearCubicWires.RepairRepresentation
open ShortPCP.Machines.FL CoordinateMachine Joins ACSP Circuit

/-- The final zero flag follows the ordered item words. -/
def itemsWord {F : Type} {m : ℕ} (encode : F → ℕ) (items : List (Item m F)) : List Bool :=
  items.flatMap (itemWord encode) ++ natWord 0

def readFlag : S := storeNat 40

def flagWrites : List Var := 40 :: pNatW

theorem readFlag_spec (G : Glob) (s : FS) (v pos Bd : ℕ)
    (hat : At (s.env 10) pos (natWord v)) (h14 : s.env 14 = pos)
    (hend : pos + (natWord v).length ≤ Bd) (hBd : BdOk G Bd) :
    let t := evalS G readFlag s
    t.env 40 = v ∧ t.env 14 = pos + (natWord v).length ∧ Appends flagWrites s t [] := by
  obtain ⟨h40, ht14, htW⟩ := storeNat_spec G s 40 v pos Bd hat h14 hend hBd (by decide)
  exact ⟨h40, ht14, ⟨htW.env, by simpa only [readFlag, List.append_nil] using htW.out, htW.fl, htW.fp,
    ip_rdFree G readFlag s (by decide), htW.bad⟩⟩

/-- A nonzero flag starts one item; the next iteration reads the next flag. -/
def itemBody : S := .seq readFlag
  (.ite (.v 40) (.seq itemPrint (.set 40 (.k 1))) .skip)

def itemLoop : S := .whl (.v 40) itemBody

def itemsPrint : S := .seq (.set 40 (.k 1)) itemLoop

theorem while_stopped (G : Glob) (fuel : ℕ) (s : FS) (h40 : s.env 40 = 0) :
    whileN (fun t => t.env 40 != 0) (evalS G itemBody) fuel s = s := by
  cases fuel <;> simp [whileN, h40]

theorem itemsWord_cons {F : Type} {m : ℕ} (encode : F → ℕ) (item : Item m F)
    (items : List (Item m F)) :
    itemsWord encode (item :: items) = natWord 1 ++
      ((patternWord item.1 ++ exprWord encode item.2) ++ itemsWord encode items) := by
  simp only [itemsWord, List.flatMap_cons, itemWord, List.append_assoc]

theorem readFlag_wf (d : ℕ) (hd : d ≤ 7) : wfS readFlag d = true := by
  simp [readFlag, storeNat, pNat, pNatOnes, pNatBits, bitE, wfS, dE]
  omega

theorem itemBody_wf (d : ℕ) (hd : d ≤ 6) : wfS itemBody d = true := by
  simp [itemBody, wfS, dE, readFlag_wf d (by omega), itemPrint_wf d hd]

theorem itemsPrint_wf (d : ℕ) (hd : d ≤ 5) : wfS itemsPrint d = true := by
  simp [itemsPrint, itemLoop, wfS, dE, itemBody_wf (d + 1) (by omega)]
  omega

end NearCubicGates.Adapters.Routing.TermsMachine.Items
