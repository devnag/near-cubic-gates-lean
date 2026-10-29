import SourceAdapters.Proximity.HonestPreparedLoad

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": restore the source cursor by the physically parsed
remaining length. The rewind pays one step per consumed input bit. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open SourceRequests (State Script lengthReg)
open TrimHonest (inputStore inputLength scheduleStore scheduleLength)
open CountedParsing

def readyScript : Script := .seq loadScript (rewindCount vZ v1 totalReg)

structure DataReady (a b : State) (source bits : List Bool) (records : List ℕ) : Prop where
  source_length : b.env lengthReg = source.length
  input_length : b.env inputLength = bits.length
  schedule_count : b.env scheduleLength = records.length
  input_ram : b.ram inputStore = bits.map Bool.toNat
  schedule_ram : b.ram scheduleStore = records
  input_cursor : b.rc inputStore = bits.length
  schedule_cursor : b.rc scheduleStore = records.length
  cursor : b.ip = (sourcePrefix source bits records).length
  constants : Cst b
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  others : ∀ m, m ≠ inputStore → m ≠ scheduleStore → b.ram m = a.ram m ∧ b.rc m = a.rc m
  vars : Fr a b loadScratch

theorem ready_run (C : Ctx) (a : State) (hc : Cst a) (source bits : List Bool) (records : List ℕ)
    (hin : C.inp = LengthPrefix.wrapped (word source bits records)) (hip : a.ip = 0)
    (hi : a.ram inputStore = []) (hic : a.rc inputStore = 0)
    (hs : a.ram scheduleStore = []) (hsc : a.rc scheduleStore = 0)
    (hW : (word source bits records).length + 3 ≤ C.Wd) :
    Hs C readyScript a (1100 * ((word source bits records).length + 1) ^ 2)
      (fun b => DataReady a b source bits records) := by
  obtain ⟨b, nb, eb, hb, rb⟩ := load_run C a hc source bits records hin hip hi hic hs hsc hW
  let N := (word source bits records).length
  let base := (sourcePrefix source bits records).length
  let remaining := N - (natWord source.length).length
  have hp := (word_bounds source bits records).2.2.2.1
  have he := rewind_count C vZ v1 totalReg (by decide) (by decide) b
    rb.constants.z rb.constants.one base remaining
  have hstart : rewindState totalReg b (base + remaining) remaining = b := by
    apply state_ext
    · funext i
      by_cases h : i = totalReg
      · subst i; simpa only [rewindState, DS.set_env_self] using rb.remaining.symm
      · simp [rewindState, DS.set, h]
    · simp only [rewindState, DS.set]
      dsimp only [base, remaining, N, sourcePrefix]
      simp only [List.length_append]
      rw [rb.cursor]
      omega
    all_goals rfl
  rw [hstart] at he
  let d := rewindState totalReg b base 0
  have df : Fr b d [totalReg] := by
    intro i hi
    have h : i ≠ totalReg := by simpa using hi
    simp only [d, rewindState, DS.set_env_ne _ _ h]
  have dc : Cst d := Cst.of_fr rb.constants df (by decide)
  refine ⟨d, _, Ex.seq eb he, ?_, ?_⟩
  · have hr : remaining ≤ N := Nat.sub_le _ _
    change nb + (5 * remaining + 2) + 1 ≤ 1100 * (N + 1) ^ 2
    change nb ≤ 1000 * (N + 1) ^ 2 at hb
    nlinarith
  refine ⟨(df lengthReg (by decide)).trans rb.source_length,
    (df inputLength (by decide)).trans rb.input_length,
    (df scheduleLength (by decide)).trans rb.schedule_count,
    rb.input_ram, rb.schedule_ram, rb.input_cursor, rb.schedule_cursor, rfl, dc,
    rb.out, rb.kin, rb.kout, rb.kc, rb.others, ?_⟩
  exact rb.vars.trans (df.weaken (by decide))

end NearCubicGates.Adapters.Proximity.HonestPrepared
