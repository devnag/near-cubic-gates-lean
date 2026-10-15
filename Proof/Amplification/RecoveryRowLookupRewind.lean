import Proof.Amplification.RecoveryRowLookupPosition

/-! The reusable bounded prior-row lookup, including actual flag clearing,
driver positioning, the full scan and paid rewind of every local head. Its
source prefix and row-count driver are explicit physical input tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowLookupStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rewindMachine := Rewind.machine positionedMachine
noncomputable def readyTapes (d : Data) (total capacity : Nat) : Fin 16→List Bool :=
  Fin.addCases (m:=15) (n:=1) (motive:=fun _=>List Bool) (inputTapes d total)
    (fun _=>List.replicate capacity false)
def resetPos (d : Data) : Data := {d with row:={d.row with pos:=0}}
def output (total : Nat) (d : Data) (bits : List Bool) : Data :=
  resetPos (RepeatMachine.iterate next total ⟨clean d,bits⟩).2.data

theorem ready_run (width total capacity : Nat) (d : Data) (bits : List Bool)
    (hx : Inv width ⟨d,bits⟩) (hp : d.row.pos=0)
    (hcapacity : total*(budget width+3)+5≤capacity) :
    ∃ r,run rewindMachine (2*total*(budget width+3)+12) (readyTapes d total capacity)=some r ∧
      r.steps≤2*total*(budget width+3)+12 ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 6=[(readMany (readRow d.row.width) total bits).isSome] ∧
      ((readMany (readRow d.row.width) total bits).isSome=true →
        r.final.tapes=readyTapes (output total d bits) total capacity) := by
  obtain ⟨base,hr,ht,_,hflag,hout⟩ := positioned_run width total d bits hx hp
  obtain ⟨r,hrun,htapes,hreset,hheads,hsteps,_⟩ := Rewind.Workspace.reset_workspace positionedMachine _ _ base hr capacity
  have hbase : base.steps≤capacity := ht.trans hcapacity
  have hn : 2*base.steps+2≤2*total*(budget width+3)+12 := by nlinarith only [ht]
  have hm := runFrom_moreFuel rewindMachine (2*base.steps+2)
    (2*total*(budget width+3)+12-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hsteps.le.trans hn,hheads,?_,?_⟩
  · exact (htapes 6).trans hflag
  · intro ha
    funext i
    refine Fin.addCases (m:=15) (n:=1) (motive:=fun j=>r.final.tapes j=
      readyTapes (output total d bits) total capacity j) ?_ ?_ i
    · intro j
      simp only [readyTapes,Fin.addCases_left]
      rw [htapes j,hout ha]
      rfl
    · intro j
      fin_cases j
      change r.final.tapes (Fin.natAdd 15 (0 : Fin 1))=List.replicate capacity false
      simpa only [Nat.max_eq_left hbase] using hreset

theorem advance_source (x : Cursor) : (advance x).data.row.source=x.data.row.source :=
  RecoveryRowFields.afterReads_source x.data.row 0 4 x.rest

theorem iterate_retained (total : Nat) (x : Cursor) :
    (RepeatMachine.iterate next total x).2.data.row.width=x.data.row.width ∧
    (RepeatMachine.iterate next total x).2.data.key=x.data.key ∧
    (RepeatMachine.iterate next total x).2.data.row.source=x.data.row.source := by
  induction total generalizing x with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ total ih =>
    cases hh : (next x).1 with
    | false =>
      simp only [RepeatMachine.iterate,hh,Bool.false_eq_true,↓reduceIte]
      exact ⟨advance_width x,advance_key x,advance_source x⟩
    | true =>
      simp only [RepeatMachine.iterate,hh,↓reduceIte]
      obtain ⟨hw,hk,hs⟩ := ih (next x).2
      exact ⟨hw.trans (advance_width x),hk.trans (advance_key x),hs.trans (advance_source x)⟩

theorem output_valid (width total : Nat) (d : Data) (bits : List Bool)
    (hx : Inv width ⟨d,bits⟩) (ha : (readMany (readRow d.row.width) total bits).isSome=true) :
    (output total d bits).Valid ∧ (output total d bits).row.pos=0 ∧
      (output total d bits).row.width=d.row.width ∧ (output total d bits).key=d.key ∧
      (output total d bits).row.source=d.row.source := by
  have hiter : (RepeatMachine.iterate next total ⟨clean d,bits⟩).1=true := by rw [iterate_accepts]; exact ha
  have hi := iterate_inv width total ⟨clean d,bits⟩ (clean_inv width ⟨d,bits⟩ hx) hiter
  have hr := iterate_retained total ⟨clean d,bits⟩
  exact ⟨hi.1,rfl,hr⟩

theorem output_lookup (total : Nat) (d : Data) (bits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow d.row.width) total bits=some (rows,rest)) :
    (output total d bits).found=rows.any (fun row=>decide (value d.key=row.code)) ∧
      value (output total d bits).saved=lookupOr rows (value d.key) (value d.saved) := by
  have h := iterate_accumulator total ⟨clean d,bits⟩ rows rest hp
  have hf := congrArg Prod.fst h
  have hv := congrArg Prod.snd h
  rw [fold_found] at hf
  rw [fold_selected] at hv
  simp only [accumulator,clean,Bool.false_or] at hf
  simp only [accumulator,clean,Bool.false_eq_true,↓reduceIte] at hv
  change (RepeatMachine.iterate next total ⟨clean d,bits⟩).2.data.found=_ ∧ _
  refine ⟨?_,hv⟩
  convert hf using 1 <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
