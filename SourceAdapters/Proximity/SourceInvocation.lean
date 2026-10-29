import SourceAdapters.Proximity.SourceResults

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": complete source request/call/read operations with
exact tuple words and charged costs. The original circuit cursor is retained. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceInvocation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults

def scalar (tag : List Bool) (xs : List (Fin VV)) : Script :=
  .seq (SourceRequests.writeRequest tag xs) scalarCall

theorem scalar_run (C : Ctx) (tag source pre tail : List Bool) (xs : List (Fin VV))
    (request : C.K.Req) (n : ℕ) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hxs : ∀ x ∈ xs, x ∉ SourceRequests.scratch)
    (hl : a.env SourceRequests.lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hrequest : C.K.inw request = tag ++ source ++ SourceRequests.fieldsWord a xs)
    (hroom : (C.K.inw request).length ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = frame n.bits) (hwidth : n.bits.length + 1 ≤ C.Wd) :
    Hs C (scalar tag xs) a
      (2 * tag.length + 15 * source.length + SourceRequests.fieldsCost a xs +
        C.Lk + C.Bk + 10 * n.bits.length + 27)
      (fun b => Returned a b ∧ b.env resultReg = n) := by
  have e := SourceRequests.write_request C tag source pre tail xs a hc hW hxs hl hin hip (by
    rw [hrequest] at hroom
    simpa [hempty, List.length_append, Nat.add_assoc] using hroom)
  refine Hs.mono (Hs.seq (t2 := C.Lk + C.Bk + 10 * n.bits.length + 12) e (fun b hb => ?_)) (by omega) (fun _ h => h)
  have e' := scalar_call C request n b (hb.constants hc)
    (by rw [hb.kin_eq, hempty, List.nil_append, hrequest]) hbudget hout hwidth
  exact e'.mono le_rfl (fun _ hd => ⟨hd.1.after_request hb, hd.2⟩)

def address (tag : List Bool) (xs : List (Fin VV)) : Script :=
  .seq (SourceRequests.writeRequest tag xs) addressCall

theorem address_run (C : Ctx) (tag source pre tail : List Bool) (xs : List (Fin VV))
    (request : C.K.Req) (proof : Bool) (n : ℕ) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hxs : ∀ x ∈ xs, x ∉ SourceRequests.scratch)
    (hl : a.env SourceRequests.lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hrequest : C.K.inw request = tag ++ source ++ SourceRequests.fieldsWord a xs)
    (hroom : (C.K.inw request).length ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = proof :: frame n.bits) (hwidth : n.bits.length + 1 ≤ C.Wd) :
    Hs C (address tag xs) a
      (2 * tag.length + 15 * source.length + SourceRequests.fieldsCost a xs +
        C.Lk + C.Bk + 10 * n.bits.length + 29)
      (fun b => Returned a b ∧ b.env resultReg = n ∧ b.env tagReg = proof.toNat) := by
  have e := SourceRequests.write_request C tag source pre tail xs a hc hW hxs hl hin hip (by
    rw [hrequest] at hroom
    simpa [hempty, List.length_append, Nat.add_assoc] using hroom)
  refine Hs.mono (Hs.seq (t2 := C.Lk + C.Bk + 10 * n.bits.length + 14) e (fun b hb => ?_)) (by omega) (fun _ h => h)
  have e' := address_call C request proof n b (hb.constants hc)
    (by rw [hb.kin_eq, hempty, List.nil_append, hrequest]) hbudget hout hwidth
  exact e'.mono le_rfl (fun _ hd => ⟨hd.1.after_request hb, hd.2⟩)

end NearCubicGates.Adapters.Proximity.SourceInvocation
