import SourceAdapters.Proximity.SourceResults
import Proof.Gates.Cells.Blk

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": paid replacement of the next query-address record.
A reused row store is overwritten in place, so its length stays bounded by
the fixed maximum query count even after polynomially many source rows. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.QueryStore

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults (tagReg resultReg)

def storePair (m : Fin MM) : Script :=
  .seq (.op (.wrM m tagReg)) (.op (.wrM m resultReg))

def storedPair (m : Fin MM) (a : State) (tag n : ℕ) : State :=
  (a.put m tag).put m n

theorem store_pair (C : Ctx) (m : Fin MM) (a : State) (tag n : ℕ)
    (htag : a.env tagReg = tag) (hn : a.env resultReg = n) (hroom : a.rc m ≤ (a.ram m).length) :
    Ex C (storePair m) a (storedPair m a tag n) 3 := by
  have e1 := Ex.op (OpEx.wrM (C := C) m tagReg a hroom)
  rw [htag] at e1
  have e2 := Ex.op (OpEx.wrM (C := C) m resultReg (a.put m tag) (by
    simp only [DS.put, Function.update_self]
    rw [putAt_length _ _ _ hroom]
    omega))
  change Ex C (.op (.wrM m resultReg)) (a.put m tag) ((a.put m tag).put m (a.env resultReg)) 1 at e2
  rw [hn] at e2
  exact Ex.seq e1 e2

theorem storedPair_ram (m : Fin MM) (a : State) (tag n : ℕ) (pre tail : List ℕ)
    (hram : a.ram m = pre ++ tail) (hcursor : a.rc m = pre.length) :
    (storedPair m a tag n).ram = Function.update a.ram m (pre ++ [tag, n] ++ tail.drop 2) := by
  have hp1 : putAt (a.ram m) (a.rc m) tag = pre ++ tag :: tail.drop 1 := by
    rw [hram, hcursor, putAt_split]
  have hp2 : putAt (pre ++ tag :: tail.drop 1) (pre.length + 1) n = pre ++ [tag, n] ++ tail.drop 2 := by
    have hh := putAt_split (pre ++ [tag]) (tail.drop 1) n
    simpa [List.append_assoc, List.drop_drop] using hh
  simp only [storedPair, DS.put, Function.update_self, Function.update_idem]
  rw [hp1, hcursor, hp2]

@[simp] theorem storedPair_cursor (m : Fin MM) (a : State) (tag n : ℕ) :
    (storedPair m a tag n).rc = Function.update a.rc m (a.rc m + 2) := by
  simp [storedPair, DS.put, Nat.add_assoc]

@[simp] theorem storedPair_env (m : Fin MM) (a : State) (tag n : ℕ) :
    (storedPair m a tag n).env = a.env := rfl

@[simp] theorem storedPair_other (m : Fin MM) (a : State) (tag n : ℕ) :
    ((storedPair m a tag n).ip, (storedPair m a tag n).out, (storedPair m a tag n).kin,
      (storedPair m a tag n).kout, (storedPair m a tag n).kc) =
    (a.ip, a.out, a.kin, a.kout, a.kc) := rfl

end NearCubicGates.Adapters.Proximity.QueryStore
