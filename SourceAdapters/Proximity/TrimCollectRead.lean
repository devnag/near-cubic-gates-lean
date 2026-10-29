import SourceAdapters.Proximity.TrimLoad
import SourceAdapters.Code.DistinctRecordsFrame
import Proof.Gates.Cells.Idx

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid three-field query reads for proof-address collection.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code

variable {C : Ctx}

def proofStore : Fin MM := 1
def distinctStore : Fin MM := 2
def proofCountReg : Fin VV := 45
def tagReg : Fin VV := 46
def addressReg : Fin VV := 47

def collectRegisters : DistinctRecords.Registers :=
  ⟨fieldsReg, proofCountReg, tagReg, addressReg, countLoop⟩

theorem collectRegisters_valid : collectRegisters.Valid := by
  unfold DistinctRecords.Registers.Valid
  decide

abbrev CollectFrame := DistinctRecords.Frame collectRegisters sN proofStore

def readThree : St VV MM := .seq (.op (.rdM sN tagReg))
  (.seq (.op (.rdM sN addressReg)) (.op (.rdM sN vJ)))

def afterRead (a : DS VV MM) (reg : Fin VV) (value : ℕ) : DS VV MM :=
  (a.set reg value).adv sN

theorem read_head (a : DS VV MM) (reg : Fin VV) (value : ℕ) (tail : List ℕ)
    (h : (a.ram sN).drop (a.rc sN) = value :: tail) :
    Ex C (.op (.rdM sN reg)) a (afterRead a reg value) 1 ∧
    ((afterRead a reg value).ram sN).drop ((afterRead a reg value).rc sN) = tail := by
  have hl := congrArg List.length h
  simp only [List.length_drop, List.length_cons] at hl
  have hv : (a.ram sN).getD (a.rc sN) 0 = value := fld_of_drop h
  constructor
  · have he := Ex.op (OpEx.rdM (C := C) sN reg a (by omega))
    simpa only [afterRead, hv] using he
  · change (a.ram sN).drop (a.rc sN + 1) = tail
    rw [← List.drop_drop, h]
    rfl

theorem afterRead_frame (a : DS VV MM) (reg : Fin VV) (value : ℕ)
    (hr : reg ∈ DistinctRecords.scratch collectRegisters) :
    CollectFrame a (afterRead a reg value) :=
  (DistinctRecords.Frame.set _ _ _ a reg value hr).trans
    (DistinctRecords.Frame.advance _ _ _ _)

def ReadThreePost (a : DS VV MM) (x y : ℕ) (tail : List ℕ) (b : DS VV MM) : Prop :=
  b.env tagReg = x ∧ b.env addressReg = y ∧ b.rc sN = a.rc sN + 3 ∧
  (b.ram sN).drop (b.rc sN) = tail ∧ b.ram = a.ram ∧
  b.rc proofStore = a.rc proofStore ∧ Fr a b [tagReg, addressReg, vJ] ∧ CollectFrame a b

theorem read_three (a : DS VV MM) (x y z : ℕ) (tail : List ℕ)
    (h : (a.ram sN).drop (a.rc sN) = x :: y :: z :: tail) :
    Hs C readThree a 5 (ReadThreePost a x y tail) := by
  obtain ⟨e1, h1⟩ := read_head (C := C) a tagReg x (y :: z :: tail) h
  let b := afterRead a tagReg x
  obtain ⟨e2, h2⟩ := read_head (C := C) b addressReg y (z :: tail) h1
  let d := afterRead b addressReg y
  obtain ⟨e3, h3⟩ := read_head (C := C) d vJ z tail h2
  refine ⟨afterRead d vJ z, 5, Ex.seq e1 (Ex.seq e2 e3), le_rfl, ?_⟩
  refine ⟨?_, ?_, ?_, h3, rfl, ?_, ?_, ?_⟩
  · vsimp [afterRead, d, b, DS.adv]
  · vsimp [afterRead, d, DS.adv]
  · simp [afterRead, d, b, DS.adv]
  · vsimp [afterRead, d, b, DS.adv]
  · intro reg hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
    simp [afterRead, d, b, DS.adv, DS.set, hreg.1, hreg.2.1, hreg.2.2]
  · exact (afterRead_frame a tagReg x (by decide)).trans
      ((afterRead_frame b addressReg y (by decide)).trans
        (afterRead_frame d vJ z (by decide)))

end NearCubicGates.Adapters.Proximity.Trim
