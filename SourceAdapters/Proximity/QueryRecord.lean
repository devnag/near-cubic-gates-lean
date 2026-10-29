import SourceAdapters.Proximity.SourceInvocation
import SourceAdapters.Proximity.QueryStore

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": one real source query, or one ignored padding query,
written into the current finite row. All source requests have their exact
source-domain witnesses; the padding branch makes no source call. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.QueryRecord

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults QueryStore

structure Recorded (m : Fin MM) (a b : State) (pre tail : List ℕ) (tag n : ℕ) : Prop where
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out
  kin_nil : b.kin = []
  ram_eq : b.ram = Function.update a.ram m (pre ++ [tag, n] ++ tail.drop 2)
  cursor_eq : b.rc = Function.update a.rc m (pre.length + 2)
  vars : Fr a b SourceResults.scratch

def realQuery (m : Fin MM) (tag : List Bool) (xs : List (Fin VV)) : Script :=
  .seq (SourceInvocation.address tag xs) (storePair m)

theorem real_query (C : Ctx) (m : Fin MM) (tag source pre tail : List Bool) (xs : List (Fin VV))
    (request : C.K.Req) (proof : Bool) (n : ℕ) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hxs : ∀ x ∈ xs, x ∉ SourceRequests.scratch)
    (hl : a.env SourceRequests.lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hrequest : C.K.inw request = tag ++ source ++ SourceRequests.fieldsWord a xs)
    (hroom : (C.K.inw request).length ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = proof :: frame n.bits) (hwidth : n.bits.length + 1 ≤ C.Wd)
    (oldPre oldTail : List ℕ) (hram : a.ram m = oldPre ++ oldTail) (hcursor : a.rc m = oldPre.length) :
    Hs C (realQuery m tag xs) a
      (2 * tag.length + 15 * source.length + SourceRequests.fieldsCost a xs +
        C.Lk + C.Bk + 10 * n.bits.length + 33)
      (fun b => Recorded m a b oldPre oldTail proof.toNat n) := by
  have e := SourceInvocation.address_run C tag source pre tail xs request proof n a hc hW hxs
    hl hin hip hempty hrequest hroom hbudget hout hwidth
  refine Hs.mono (Hs.seq (t2 := 3) e (fun b hb => ?_)) (by omega) (fun _ h => h)
  have hr := hb.1.rest_eq
  simp only [SourceResults.rest, Prod.mk.injEq] at hr
  have hbram : b.ram m = oldPre ++ oldTail := by rw [hr.2.2.1, hram]
  have hbcur : b.rc m = oldPre.length := by rw [hr.2.2.2, hcursor]
  have e' := store_pair C m b proof.toNat n hb.2.2 hb.2.1 (by rw [hbram, hbcur]; simp)
  refine ⟨_, _, e', le_rfl, ⟨hr.1, hr.2.1, hb.1.kin_nil, ?_, ?_, hb.1.vars⟩⟩
  · rw [storedPair_ram m b proof.toNat n oldPre oldTail hbram hbcur, hr.2.2.1]
  · rw [storedPair_cursor, hr.2.2.2, hcursor]

def dummyQuery (m : Fin MM) : Script :=
  .seq (.op (.zero resultReg)) (.seq (.op (.copy tagReg v1)) (storePair m))

theorem dummy_query (C : Ctx) (m : Fin MM) (a : State) (hc : Cst a) (hempty : a.kin = [])
    (pre tail : List ℕ) (hram : a.ram m = pre ++ tail) (hcursor : a.rc m = pre.length) :
    Hs C (dummyQuery m) a 7 (fun b => Recorded m a b pre tail 1 0) := by
  have e1 := Ex.op (OpEx.zero (C := C) resultReg a)
  let b := a.set resultReg 0
  have e2 := Ex.op (OpEx.copy (C := C) tagReg v1 b (by decide))
  have hb : b.env v1 = 1 := by
    rw [DS.set_env_ne _ _ (by decide : v1 ≠ resultReg)]
    exact hc.one
  rw [hb] at e2
  let c := b.set tagReg 1
  have e3 := store_pair C m c 1 0 (by simp [c])
    (by simp [c, b, DS.set, tagReg, resultReg]) (by change a.rc m ≤ (a.ram m).length; rw [hram, hcursor]; simp)
  refine ⟨_, _, Ex.seq e1 (Ex.seq e2 e3), le_rfl, ⟨rfl, rfl, hempty, ?_, ?_, ?_⟩⟩
  · exact storedPair_ram m c 1 0 pre tail hram hcursor
  · simp [c, b, hcursor]
  · intro x hx
    have ht : x ≠ tagReg := fun he => hx (by simp [SourceResults.scratch, he])
    have hv : x ≠ resultReg := fun he => hx (by simp [SourceResults.scratch, he])
    simp [storedPair, c, b, DS.put, DS.set, ht, hv]

end NearCubicGates.Adapters.Proximity.QueryRecord
