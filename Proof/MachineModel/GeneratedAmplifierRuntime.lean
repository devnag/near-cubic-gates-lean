import Proof.MachineModel.GeneratedAmplifierEntry
import Proof.MachineModel.GeneratedAmplifierLookupBlank

/-! One fixed18-tape ordinary program evaluates the supplied complete truth
table at its supplied address, including every physical input/field stage. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Runtime
open LocalBitMultitape RadixSemantics SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5→Fin 18 := ![13,15,16,3,17]
noncomputable def lookup := RecoveryFocus.machine slots Lookup.machine
noncomputable def machine := Composition.machine Entry.machine lookup
def budget {n : ℕ} (f : BoolFunction n) (address : BitInput n) :=
  Entry.budget n (boolFunctionTable f) (List.ofFn address)+1+Lookup.cost n (value (List.ofFn address))

theorem runtime_run {n : ℕ} (f : BoolFunction n) (address : BitInput n) :
    ∃ r,run machine (budget f address) (Entry.input (payload f address))=some r ∧
      r.steps≤budget f address ∧ r.final.tapes 17=[f address] ∧ r.final.heads 17=0 := by
  let word := payload f address
  let query := List.ofFn address
  let table := boolFunctionTable f
  let index := value query
  have hi : index<table.length := by simpa [index,query,table] using address_lt address
  obtain ⟨base,hb,hbs,ready⟩ := Entry.entry_run n table query (by simp [query])
  have hsplit : table.take index++table[index]::table.drop (index+1)=table := by
    have h := List.take_append_drop index table
    rw [List.drop_eq_getElem_cons hi] at h
    exact h
  have hlen : (table.take index).length=index := by simp [List.length_take,Nat.min_eq_left hi.le]
  obtain ⟨localRun,hl,hls,hout,hhead⟩ := Lookup.blank_run query (frame n.bits) (table.take index)
    table[index] (table.drop (index+1)++frame query) (by rw [hlen])
  have hword : frame n.bits++table.take index++table[index]::(table.drop (index+1)++frame query)=word := by
    change _=frame n.bits++table++frame query
    simpa only [List.append_assoc,List.cons_append] using
      congrArg (fun xs => frame n.bits++xs++frame query) hsplit
  rw [hword,hlen] at hl
  have hq : query.length=n := by simp [query]
  rw [hq,hlen] at hls
  rw [hq] at hl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) Lookup.machine
    base.final.heads base.final.tapes _ _ localRun hl
  have he : RecoveryFocus.config slots base.final.heads base.final.tapes
      (Lookup.entry query word (frame n.bits).length)=Composition.restart base.final lookup.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact ready.queryHead
      · exact ready.flagHead
      · exact ready.scratchHead
      · change base.final.heads 3=(frame n.bits).length
        simpa using ready.sourceHead
      · exact ready.outputHead
    · intro i; fin_cases i
      · exact ready.query
      · exact ready.flag
      · exact ready.scratch
      · exact ready.source
      · exact ready.output
  rw [he] at hfocus
  have hj := Composition.run_join Entry.machine lookup _ _ _ base focused hb hfocus
  have ho : table[index]=f address := table_lookup f address
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_,?_⟩
  · change base.steps+1+focused.steps≤_
    rw [hfs]
    change base.steps+1+localRun.steps≤Entry.budget n table query+1+Lookup.cost n index
    omega
  · change focused.final.tapes (slots 4)=_
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact hout.trans (congrArg (fun b => [b]) ho)
  · change focused.final.heads (slots 4)=_
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact hhead

noncomputable def program : Program where
  tapeCount := 18
  stateCount := _
  twoTapes := by decide
  machine := machine
  outputTape := 17
  outputFresh := by decide

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Runtime
