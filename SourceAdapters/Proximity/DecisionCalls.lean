import SourceAdapters.Proximity.DecisionSending
import SourceAdapters.Proximity.SourceResults
import SourceAdapters.Proximity.QueryStep

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": actual source-decision calls on the first N bits of a
fixed assignment. The source query count and current coin row are retained. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecisionCalls

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CellSending
open SourceRequests (State Script)
open SourceResults DecisionSending QueryStep

def decisionTag : List Bool := [false, true, true, true, false]
def scratch : List (Fin VV) := remaining :: SourceResults.scratch

def decisionCall (bits : List Bool) : Script :=
  .seq (SourceRequests.writeRequest decisionTag [rowReg])
    (.seq (.op (.copy remaining countReg)) (.seq (sendPrefix bits) booleanCall))

structure Decided (a b : State) (bit : Bool) : Prop where
  rest_eq : SourceResults.rest b = SourceResults.rest a
  kin_nil : b.kin = []
  vars : Fr a b scratch
  value_eq : b.env resultReg = bit.toNat

theorem decision_call (C : Ctx) (source pre tail bits : List Bool) (row N : ℕ)
    (request : C.K.Req) (bit : Bool) (a : State) (hc : Cst a)
    (hW : 4 ≤ 2 ^ C.Wd) (hrow : a.env rowReg = row) (hcount : a.env countReg = N)
    (hl : a.env SourceRequests.lengthReg = source.length) (hin : C.inp = pre ++ source ++ tail)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hrequest : C.K.inw request = decisionTag ++ source ++ frame row.bits ++ bits.take N)
    (hroom : (C.K.inw request).length ≤ C.Lk) (hbudget : C.K.bud request ≤ C.Bk)
    (hout : C.K.outw request = [bit]) :
    Hs C (decisionCall bits) a
      (15 * source.length + 10 * row.bits.length + 6 * bits.length + C.Lk + C.Bk + 41)
      (fun b => Decided a b bit) := by
  have htotal : decisionTag.length + source.length + (frame row.bits).length + (bits.take N).length ≤ C.Lk := by
    rw [hrequest] at hroom
    simpa only [List.length_append, Nat.add_assoc] using hroom
  have e1 := SourceRequests.write_request C decisionTag source pre tail [rowReg] a hc hW (by decide)
    hl hin hip (by
      simp [hempty, SourceRequests.fieldsWord, hrow]
      simp only [frame_length] at htotal
      omega)
  obtain ⟨b, cost1, ex1, hc1, hb⟩ := e1
  have hbconst := hb.constants hc
  have hbN : b.env countReg = N := (hb.vars countReg (by decide)).trans hcount
  have ex2 := Ex.op (OpEx.copy (C := C) remaining countReg b (by decide))
  rw [hbN] at ex2
  let c := b.set remaining N
  have hcconst : Cst c := Cst.of_fr hbconst (Fr.set b N (T := [remaining]) (by simp)) (by decide)
  have ex3 := send_prefix C bits c N hcconst (by simp [c]) (by
    rw [DS.set_kin, hb.kin_eq]
    simpa [hempty, SourceRequests.fieldsWord, hrow, List.length_append, Nat.add_assoc] using htotal)
  let d := sentPrefix c bits N
  have hdkin : d.kin = C.K.inw request := by
    rw [hrequest]
    simp [d, sentPrefix, sent, c, hb.kin_eq, hempty, SourceRequests.fieldsWord, hrow, List.append_assoc]
  have ex4 := boolean_call C request bit d hdkin hbudget hout
  obtain ⟨e, cost4, he4, hc4, he⟩ := ex4
  refine ⟨e, cost1 + (1 + (6 * bits.length + 2 + cost4 + 1) + 1) + 1,
    Ex.seq ex1 (Ex.seq ex2 (Ex.seq ex3 he4)), ?_, ?_⟩
  · simp only [decisionTag, List.length_cons, List.length_nil, SourceRequests.fieldsCost,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrow] at hc1
    omega
  · refine ⟨he.1.rest_eq.trans ?_, he.1.kin_nil, ?_, he.2⟩
    · have hr := hb.rest_eq
      simp only [SourceRequests.rest, Prod.mk.injEq] at hr
      simp [SourceResults.rest, d, sentPrefix, sent, c, DS.set, hr]
    · have h1 : Fr a b scratch := hb.vars.weaken (by
        intro x hx
        exact List.mem_cons_of_mem remaining (List.mem_append_left _ hx))
      have h2 : Fr b c scratch := Fr.set b N (List.mem_cons_self ..)
      have h3 : Fr c d scratch := by
        intro x hx
        have hxR : x ≠ remaining := fun h => hx (by simp [scratch, h])
        have hx0 : x ≠ t0 := fun h => hx (by simp [scratch, SourceResults.scratch, SourceRequests.scratch, h])
        simp [d, sentPrefix, sent, DS.set, hxR, hx0]
      have h4 : Fr d e scratch := he.1.vars.weaken (fun _ h => List.mem_cons_of_mem remaining h)
      exact h1.trans (h2.trans (h3.trans h4))

end NearCubicGates.Adapters.Proximity.DecisionCalls
