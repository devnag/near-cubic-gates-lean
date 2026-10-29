import SourceAdapters.Code.BitSending
import SourceAdapters.Proximity.RequestWriting

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": a finite table call receives its exact raw bits from
RAM, after a paid tag writer and paid rewind/scan. The call output is retained
at cursor zero for the following literal parser. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.StoredCall

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code NearCubicGates.Adapters.Code.CellSending

def callStored (m : Fin MM) (len : Fin VV) (tag : List Bool) : St VV MM :=
  .seq (RequestWriting.callLiteral t0 tag) (.seq (BitSending.script m len) (.op .kcall))

theorem call_stored (C : Ctx) (m : Fin MM) (len : Fin VV) (tag bits output : List Bool)
    (hl0 : len ≠ c0) (hlj : len ≠ vJ) (hlt : len ≠ t0)
    (a : DS VV MM) (hc : Cst a) (request : C.K.Req)
    (hstore : a.ram m = bits.map Bool.toNat) (hlen : a.env len = bits.length)
    (hwidth : bits.length < 2 ^ C.Wd) (hempty : a.kin = [])
    (hrequest : C.K.inw request = tag ++ bits) (hroom : (C.K.inw request).length ≤ C.Lk)
    (hbudget : C.K.bud request ≤ C.Bk) (hout : C.K.outw request = output) :
    Hs C (callStored m len tag) a
      (2 * tag.length + a.rc m + 8 * bits.length + C.Lk + C.Bk + 10) (fun b =>
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc m = bits.length ∧
      (∀ s, s ≠ m → b.rc s = a.rc s) ∧ b.kin = [] ∧ b.kout = output ∧ b.kc = 0 ∧
      Cst b ∧ Fr a b [t0, c0, vJ]) := by
  have hlenroom : tag.length + bits.length ≤ C.Lk := by simpa only [hrequest, List.length_append] using hroom
  have e1 := RequestWriting.call_literal C t0 tag a (by simp [hempty]; omega)
  let b := sent true (a.set t0 0) tag
  have hbC : Cst b := by
    have hset : Cst (a.set t0 0) := Cst.of_fr hc (Fr.set a 0 (T := [t0]) (by simp)) (by decide)
    exact ⟨by simpa [b, sent] using hset.z, by simpa [b, sent] using hset.one,
      by simpa [b, sent] using hset.two⟩
  have e2 := BitSending.runs C m len hl0 hlj b hbC bits hstore
    (by simp [b, sent, DS.set, hlt, hlen]) hwidth (by simpa [b, sent, hempty] using hlenroom)
  obtain ⟨d, cost, he2, hcost, hd⟩ := e2
  rcases hd with ⟨hkin, _, hdc, hip, ho, hm, hcursor, hother, _, _, hfr⟩
  have hdrequest : d.kin = C.K.inw request := by simpa [hrequest, b, sent, hempty] using hkin
  have e3 := Ex.op (OpEx.kcall request d hdrequest hbudget)
  rw [hout] at e3
  refine ⟨d.called output, (2 * tag.length + 1) + (cost + (1 + C.Lk + C.Bk) + 1) + 1,
    Ex.seq e1 (Ex.seq he2 e3), by change cost ≤ a.rc m + 8 * bits.length + 6 at hcost; omega,
    hip, ho, hm, hcursor, hother, rfl, rfl, rfl, ⟨hdc.z, hdc.one, hdc.two⟩, ?_⟩
  intro x hx
  have hxt : x ≠ t0 := fun h => hx (by simp [h])
  have hxfr : x ∉ [c0, vJ] := fun h => hx (List.mem_cons_of_mem t0 h)
  change d.env x = a.env x
  rw [hfr x hxfr]
  simp [b, sent, DS.set, hxt]

end NearCubicGates.Adapters.Proximity.StoredCall
