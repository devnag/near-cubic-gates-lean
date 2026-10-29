import SourceAdapters.Proximity.HonestPreparedSizes
import SourceAdapters.Code.NaturalLoading

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": all prepared input data are loaded by actual
parsers. Every address is charged by its binary field width. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open SourceRequests (State Script lengthReg)
open TrimHonest (inputStore inputLength scheduleStore scheduleLength)

def loadScript : Script := .seq header (.seq inputScript (NaturalLoading.script scheduleStore scheduleLength))
def loadScratch : List (Fin VV) := headerScratch ++ inputScratch ++ readT

structure DataLoaded (a b : State) (source bits : List Bool) (records : List ℕ) : Prop where
  source_length : b.env lengthReg = source.length
  remaining : b.env totalReg = (word source bits records).length - (natWord source.length).length
  input_length : b.env inputLength = bits.length
  schedule_count : b.env scheduleLength = records.length
  input_ram : b.ram inputStore = bits.map Bool.toNat
  schedule_ram : b.ram scheduleStore = records
  input_cursor : b.rc inputStore = bits.length
  schedule_cursor : b.rc scheduleStore = records.length
  cursor : b.ip = (natWord (word source bits records).length).length + (word source bits records).length
  constants : Cst b
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  others : ∀ m, m ≠ inputStore → m ≠ scheduleStore → b.ram m = a.ram m ∧ b.rc m = a.rc m
  vars : Fr a b loadScratch

theorem load_run (C : Ctx) (a : State) (hc : Cst a) (source bits : List Bool) (records : List ℕ)
    (hin : C.inp = LengthPrefix.wrapped (word source bits records)) (hip : a.ip = 0)
    (hi : a.ram inputStore = []) (hic : a.rc inputStore = 0)
    (hs : a.ram scheduleStore = []) (hsc : a.rc scheduleStore = 0)
    (hW : (word source bits records).length + 3 ≤ C.Wd) :
    Hs C loadScript a (1000 * ((word source bits records).length + 1) ^ 2)
      (fun b => DataLoaded a b source bits records) := by
  let N := (word source bits records).length
  obtain ⟨hsource, hbits, hrecords, hprefix, _, hfields⟩ := word_bounds source bits records
  change source.length ≤ N at hsource
  change bits.length ≤ N at hbits
  change records.length ≤ N at hrecords
  change (natWord source.length).length ≤ N at hprefix
  change ∀ x ∈ records, natBitLength x ≤ N at hfields
  change N + 3 ≤ C.Wd at hW
  have hexp := Nat.lt_two_pow_self (n := C.Wd)
  have hNb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le N
  have hSb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le source.length
  have hRb := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le records.length
  obtain ⟨b, nb, eb, hb, rb⟩ := header_run C a hc N source.length
    (source ++ frame bits ++ natWord records.length ++ records.flatMap natWord)
    (by rw [hin]; simp only [N, LengthPrefix.wrapped, word, List.append_assoc]) hip
    (by omega) (by omega) (by omega) hprefix
  have cb := Cst.of_fr hc rb.vars (by decide)
  have rbother := rb.other
  simp only [Prod.mk.injEq] at rbother
  have hbip : b.ip = (sourcePrefix source bits records).length := by
    simpa only [sourcePrefix, List.length_append] using rb.cursor
  have hshape : C.inp = sourcePrefix source bits records ++ source ++ frame bits ++
      natWord records.length ++ records.flatMap natWord := by
    rw [hin]
    simp only [LengthPrefix.wrapped, word, sourcePrefix, List.append_assoc]
  obtain ⟨c, nc, ec, hcCost, rc⟩ := input_run C b cb source bits (sourcePrefix source bits records)
    (records.flatMap natWord) records.length hshape hbip rb.source_length
    (by rw [rbother.2.1, hi]) (by rw [rbother.2.2.1, hic]) (by omega) (by omega) (by omega)
  have hcpos : c.ip = (sourcePrefix source bits records ++ source ++ frame bits ++ natWord records.length).length := by
    rw [rc.cursor, hbip]
    simp only [List.length_append]
  have hread : C.inp.drop c.ip = records.flatMap natWord ++ [] := by
    rw [hcpos, hshape, List.drop_left, List.append_nil]
  have cm : c.ram scheduleStore = [] := by
    rw [(rc.others scheduleStore (by decide)).1, rbother.2.1, hs]
  have cc : c.rc scheduleStore = 0 := by
    rw [(rc.others scheduleStore (by decide)).2, rbother.2.2.1, hsc]
  obtain ⟨d, nd, ed, hd, dm, dc, dn, dip, cd, dout, dkin, dkout, dkc, dother, df⟩ :=
    NaturalLoading.runs C scheduleStore scheduleLength (by decide) c rc.constants records [] N hread
      rc.schedule_count hfields (by omega) (by omega) cm cc
  refine ⟨d, _, Ex.seq eb (Ex.seq ec ed), ?_, ?_⟩
  · have hproduct := Nat.mul_le_mul_right (30 * N + 36) hrecords
    change nb ≤ 30 * natBitLength N + 30 * natBitLength source.length + 73 at hb
    change nc ≤ 5 * source.length + 9 * bits.length + 30 * natBitLength records.length + 44 at hcCost
    change nd ≤ records.length * (30 * N + 36) + 4 at hd
    change nb + (nc + nd + 1) + 1 ≤ 1000 * (N + 1) ^ 2
    nlinarith
  refine ⟨?_, ?_, ?_, dn, ?_, dm, ?_, dc, ?_, cd, dout.trans (rc.out.trans rbother.1),
    dkin.trans (rc.kin.trans rbother.2.2.2.1), dkout.trans (rc.kout.trans rbother.2.2.2.2.1),
    dkc.trans (rc.kc.trans rbother.2.2.2.2.2), ?_, ?_⟩
  · rw [df lengthReg (by decide), rc.vars lengthReg (by decide), rb.source_length]
  · rw [df totalReg (by decide), rc.vars totalReg (by decide), rb.remaining]
  · rw [df inputLength (by decide), rc.input_length]
  · rw [(dother inputStore (by decide)).1, rc.input_store]
  · rw [(dother inputStore (by decide)).2, rc.input_cursor]
  · rw [dip, rc.cursor, rb.cursor]
    simp only [N, word, List.length_append]
    omega
  · intro m hmi hms
    rw [(dother m hms).1, (dother m hms).2, (rc.others m hmi).1, (rc.others m hmi).2,
      rbother.2.1, rbother.2.2.1]
    exact ⟨rfl, rfl⟩
  · exact (rb.vars.weaken (by decide)).trans ((rc.vars.weaken (by decide)).trans (df.weaken (by decide)))

end NearCubicGates.Adapters.Proximity.HonestPrepared
