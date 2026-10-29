import SourceAdapters.Proximity.SourceInvocation
import SourceAdapters.Proximity.SourceQueryRows

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": source scalar calls followed by a paid move into
retained constructor registers. The source input cursor and stores survive. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceScalars

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults (resultReg)

def scalarTo (destination : Fin VV) (tag : List Bool) (xs : List (Fin VV)) : Script :=
  .seq (SourceInvocation.scalar tag xs) (.op (.copy destination resultReg))

structure Retained (destination : Fin VV) (a b : State) (value : ℕ) : Prop where
  rest_eq : SourceResults.rest b = SourceResults.rest a
  kin_nil : b.kin = []
  value_eq : b.env destination = value
  vars : Fr a b (destination :: SourceResults.scratch)

theorem scalar_to (C : Ctx) (destination : Fin VV) (hd : destination ≠ resultReg)
    (tag source pre tail : List Bool) (xs : List (Fin VV)) (request : C.K.Req) (n : ℕ)
    (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ C.Wd) (hxs : ∀ x ∈ xs, x ∉ SourceRequests.scratch)
    (hl : a.env SourceRequests.lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hrequest : C.K.inw request = tag ++ source ++ SourceRequests.fieldsWord a xs)
    (hroom : (C.K.inw request).length ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = frame n.bits) (hwidth : n.bits.length + 1 ≤ C.Wd) :
    Hs C (scalarTo destination tag xs) a
      (2 * tag.length + 15 * source.length + SourceRequests.fieldsCost a xs +
        C.Lk + C.Bk + 10 * n.bits.length + 29)
      (fun b => Retained destination a b n) := by
  have e := SourceInvocation.scalar_run C tag source pre tail xs request n a hc hW hxs
    hl hin hip hempty hrequest hroom hbudget hout hwidth
  obtain ⟨b, cost, he, hcost, hb⟩ := e
  have ec := Ex.op (OpEx.copy (C := C) destination resultReg b hd)
  rw [hb.2] at ec
  refine ⟨_, cost + 1 + 1, Ex.seq he ec, by omega, ?_⟩
  exact ⟨hb.1.rest_eq, hb.1.kin_nil, by simp,
    (hb.1.vars.weaken (fun _ h => List.mem_cons_of_mem destination h)).trans
      (Fr.set b n (List.mem_cons_self ..))⟩

end NearCubicGates.Adapters.Proximity.SourceScalars
