import SourceAdapters.Proximity.HonestPreparedHeader
import SourceAdapters.Code.InputBitLoading

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": skip the charged source description, load the
exact framed input bits, and read the serialized schedule count. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open SourceRequests (State Script lengthReg)
open TrimHonest (inputStore inputLength scheduleLength)

def inputScript : Script := .seq skipSource (.seq (InputBitLoading.script inputStore inputLength)
  (SourcePrinting.readInto scheduleLength))

def inputScratch : List (Fin VV) := [c0, t0, vJ, inputLength, scheduleLength] ++ rdNatT

structure InputLoaded (a b : State) (source bits : List Bool) (count : ℕ) : Prop where
  input_store : b.ram inputStore = bits.map Bool.toNat
  input_length : b.env inputLength = bits.length
  input_cursor : b.rc inputStore = bits.length
  schedule_count : b.env scheduleLength = count
  cursor : b.ip = a.ip + source.length + (frame bits).length + (natWord count).length
  constants : Cst b
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  others : ∀ m, m ≠ inputStore → b.ram m = a.ram m ∧ b.rc m = a.rc m
  vars : Fr a b inputScratch

theorem input_run (C : Ctx) (a : State) (hc : Cst a) (source bits pre tail : List Bool) (count : ℕ)
    (hin : C.inp = pre ++ source ++ frame bits ++ natWord count ++ tail)
    (hip : a.ip = pre.length) (hlen : a.env lengthReg = source.length)
    (hempty : a.ram inputStore = []) (hcursor : a.rc inputStore = 0)
    (hs : source.length < 2 ^ C.Wd) (hi : bits.length < 2 ^ C.Wd)
    (hn : natBitLength count + 2 ≤ C.Wd) :
    Hs C inputScript a (5 * source.length + 9 * bits.length + 30 * natBitLength count + 44)
      (fun b => InputLoaded a b source bits count) := by
  obtain ⟨b, nb, eb, hb, bip, bout, bram, brc, bkin, bkout, bkc, bf⟩ :=
    skip_source C a source pre (frame bits ++ natWord count ++ tail)
      (by simpa only [List.append_assoc] using hin) hip hlen hs
  have cb := Cst.of_fr hc bf (by decide)
  obtain ⟨d, nd, ed, hd, dm, dlen, dc, dip, cd, dout, dkin, dkout, dkc, dother, df⟩ :=
    InputBitLoading.spec C inputStore inputLength (by decide) (by decide) b cb bits
      (pre ++ source) (natWord count ++ tail) (by simpa only [List.append_assoc] using hin)
      (by rw [bip, hip, List.length_append]) (by rw [bram, hempty]) (by rw [brc, hcursor]) hi
  have hread : C.inp.drop d.ip = natWord count ++ tail := by
    rw [dip, ← List.length_append]
    have hh : C.inp = ((pre ++ source) ++ frame bits) ++ (natWord count ++ tail) := by
      simpa only [List.append_assoc] using hin
    rw [hh, List.drop_left]
  obtain ⟨e, ne, ee, he, re⟩ := SourcePrinting.read_into (C := C) scheduleLength (by decide)
    d cd count tail hread hn
  have ro := re.other
  simp only [Prod.mk.injEq] at ro
  refine ⟨e, _, Ex.seq eb (Ex.seq ed ee), by omega, ?_⟩
  refine ⟨?_, ?_, ?_, re.value, ?_, re.constants cd (by decide), ro.1.trans (dout.trans bout),
    ro.2.2.2.1.trans (dkin.trans bkin), ro.2.2.2.2.1.trans (dkout.trans bkout),
    ro.2.2.2.2.2.trans (dkc.trans bkc), ?_, ?_⟩
  · rw [ro.2.1, dm]
  · rw [re.vars inputLength (by decide), dlen]
  · rw [ro.2.2.1, dc]
  · rw [re.cursor, dip, hip, List.length_append]
  · intro m hm
    rw [ro.2.1, ro.2.2.1, (dother m hm).1, (dother m hm).2, bram, brc]
    exact ⟨rfl, rfl⟩
  · exact (bf.weaken (by decide)).trans ((df.weaken (by decide)).trans (re.vars.weaken (by decide)))

end NearCubicGates.Adapters.Proximity.HonestPrepared
