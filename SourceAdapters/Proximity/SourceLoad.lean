import SourceAdapters.Proximity.SourceConfiguration
import SourceAdapters.Proximity.HeaderReading
import SourceAdapters.Proximity.DescriptorParsing
import SourceAdapters.Proximity.PrefixSizes
import Proof.Gates.Cells.Prelude

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": initialize constants and stores, parse the paid
physical length prefix, retain source arity, and restore the source cursor. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script lengthReg)
open SourceHeader (arityReg)
open QueryStep (boundReg)

def loadSource (q : ℕ) : Script := .seq initP (.seq (configure q)
  (.seq (SourcePrinting.readInto lengthReg) SourceHeader.readArity))

structure SourceLoaded (q : ℕ) (S : SourceCircuit) (a : State) : Prop where
  constants : Cst a
  bound_eq : a.env boundReg = q
  truth_length : a.env truthLengthReg = 2 ^ q
  source_length : a.env lengthReg = (sourceCircuitWord S).length
  arity_eq : a.env arityReg = S.arity
  input_cursor : a.ip = (natWord (sourceCircuitWord S).length).length
  out_nil : a.out = []
  ram_nil : a.ram = fun _ => []
  cursor_zero : a.rc = fun _ => 0
  kin_nil : a.kin = []

theorem load_source (C : Ctx) (q : ℕ) (S : SourceCircuit)
    (hin : C.inp = LengthPrefix.wrapped (sourceCircuitWord S))
    (hW : 2 < 2 ^ C.Wd) (hq : q < 2 ^ C.Wd) (ht : 2 ^ q < 2 ^ C.Wd)
    (hL : natBitLength (sourceCircuitWord S).length + 2 ≤ C.Wd)
    (hn : S.arity.bits.length + 1 ≤ C.Wd) (hrew : 2 * S.arity.bits.length + 1 < 2 ^ C.Wd) :
    Hs C (loadSource q) (a0 : State)
      (2 * q + 2 * 2 ^ q + 30 * natBitLength (sourceCircuitWord S).length + 25 * S.arity.bits.length + 80)
      (fun b => SourceLoaded q S b) := by
  obtain ⟨b, cost1, he1, hc1, hbC, hbm, hbrc, hbi, hbo, hbki, _, _, _⟩ :=
    initP_spec (C := C) (a0 : State) rfl rfl rfl hW
  obtain ⟨d, cost2, he2, hc2, hdq, hdt, hds, hdf⟩ := configure_run C q b hq ht
  have hdC := Cst.of_fr hbC hdf (by decide)
  have hdip : d.ip = 0 := hds.ip.trans hbi
  have hread : C.inp.drop d.ip = natWord (sourceCircuitWord S).length ++ sourceCircuitWord S := by
    rw [hdip, List.drop_zero, hin]
    rfl
  obtain ⟨e, cost3, he3, hc3, he⟩ := SourcePrinting.read_into (C := C) lengthReg (by decide) d hdC
    (sourceCircuitWord S).length (sourceCircuitWord S) hread hL
  have heC := he.constants hdC (by decide)
  have heip : e.ip = (natWord (sourceCircuitWord S).length).length := by rw [he.cursor, hdip, Nat.zero_add]
  have heother := he.other
  simp only [Prod.mk.injEq] at heother
  have hhead : C.inp = natWord (sourceCircuitWord S).length ++ frame S.arity.bits ++
      (frame S.circuit.nodes.length.bits ++ frame S.circuit.output.val.bits ++
        S.circuit.nodes.flatMap sourceNodeWord) := by
    rw [hin]
    simp only [LengthPrefix.wrapped, sourceCircuitWord, List.append_assoc]
  obtain ⟨f, cost4, he4, hc4, hfn, hfs, hff⟩ := SourceHeader.read_arity C e heC S.arity
    (natWord (sourceCircuitWord S).length)
    (frame S.circuit.nodes.length.bits ++ frame S.circuit.output.val.bits ++
      S.circuit.nodes.flatMap sourceNodeWord) hhead heip hn hrew
  refine ⟨f, cost1 + (cost2 + (cost3 + cost4 + 1) + 1) + 1,
    Ex.seq he1 (Ex.seq he2 (Ex.seq he3 he4)), by omega, ?_⟩
  refine ⟨Cst.of_fr heC hff (by decide),
    (hff boundReg (by decide)).trans ((he.vars boundReg (by decide)).trans hdq),
    (hff truthLengthReg (by decide)).trans ((he.vars truthLengthReg (by decide)).trans hdt),
    (hff lengthReg (by decide)).trans he.value, hfn, hfs.ip.trans heip,
    hfs.out.trans (heother.1.trans (hds.out.trans hbo)),
    hfs.ram.trans (heother.2.1.trans (hds.ram.trans hbm)),
    hfs.rc.trans (heother.2.2.1.trans (hds.rc.trans hbrc)),
    hfs.kin.trans (heother.2.2.2.1.trans (hds.kin.trans hbki))⟩

end NearCubicGates.Adapters.Proximity.SourceCallee
