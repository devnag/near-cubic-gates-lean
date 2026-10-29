import SourceAdapters.Proximity.DecisionCalls
import Proof.Gates.Cells.Blk

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": one actual source predicate evaluation and its paid
truth-table record write. Reused table storage is overwritten in place. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecisionRecord

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults (resultReg)
open DecisionCalls QueryStep

structure Recorded (m : Fin MM) (a b : State) (pre tail : List ℕ) (bit : Bool) : Prop where
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out
  kin_nil : b.kin = []
  ram_eq : b.ram = Function.update a.ram m (pre ++ [bit.toNat] ++ tail.drop 1)
  cursor_eq : b.rc = Function.update a.rc m (pre.length + 1)
  vars : Fr a b DecisionCalls.scratch

def recordDecision (m : Fin MM) (bits : List Bool) : Script :=
  .seq (decisionCall bits) (.op (.wrM m resultReg))

theorem record_decision (C : Ctx) (m : Fin MM) (source pre tail bits : List Bool) (row N : ℕ)
    (request : C.K.Req) (bit : Bool) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hrow : a.env rowReg = row) (hcount : a.env countReg = N)
    (hl : a.env SourceRequests.lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hrequest : C.K.inw request = decisionTag ++ source ++ frame row.bits ++ bits.take N)
    (hroom : (C.K.inw request).length ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = [bit]) (oldPre oldTail : List ℕ)
    (hram : a.ram m = oldPre ++ oldTail) (hcursor : a.rc m = oldPre.length) :
    Hs C (recordDecision m bits) a
      (15 * source.length + 10 * row.bits.length + 6 * bits.length + C.Lk + C.Bk + 43)
      (fun b => Recorded m a b oldPre oldTail bit) := by
  have e := decision_call C source pre tail bits row N request bit a hc hW hrow hcount
    hl hin hip hempty hrequest hroom hbudget hout
  refine Hs.mono (Hs.seq (t2 := 1) e (fun b hb => ?_)) (by omega) (fun _ h => h)
  have hr := hb.rest_eq
  simp only [SourceResults.rest, Prod.mk.injEq] at hr
  have hbram : b.ram m = oldPre ++ oldTail := by rw [hr.2.2.1, hram]
  have hbcur : b.rc m = oldPre.length := by rw [hr.2.2.2, hcursor]
  have ex := Ex.op (OpEx.wrM (C := C) m resultReg b (by rw [hbram, hbcur]; simp))
  rw [hb.value_eq] at ex
  refine ⟨_, _, ex, le_rfl, ⟨hr.1, hr.2.1, hb.kin_nil, ?_, ?_, hb.vars⟩⟩
  · simp only [DS.put, hbram, hbcur, putAt_split]
    rw [hr.2.2.1]
    simp only [List.append_assoc, List.singleton_append]
  · simp only [DS.put, hbcur, hr.2.2.2]

end NearCubicGates.Adapters.Proximity.DecisionRecord
