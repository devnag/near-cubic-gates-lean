import Proof.Amplification.RecoveryRowLookupCell

/-! Shared streamed prior-row workspace. The reader's witness cursor and
width driver keep their physical positions during code comparison and count
copying; no implicit rewind of the global witness stream is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ReadyRun.focus_at {t u s n : Nat} {p : Machine t s}
    {input output : Fin t→List Bool} (h : ReadyRun p n input output)
    (slot : Fin t→Fin u) (hi : Function.Injective slot)
    (heads : Fin u→Nat) (ambient : Fin u→List Bool)
    (hin : ∀ j,ambient (slot j)=input j) (hh0 : ∀ j,heads (slot j)=0) :
    ∃ r,runFrom (RecoveryFocus.machine slot p) n ⟨p.start,heads,ambient⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=install slot ambient output ∧ r.steps=n := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config slot hi p heads ambient n
    (initialConfiguration p input) base hr
  have hinit : RecoveryFocus.config slot heads ambient (initialConfiguration p input)=
      (⟨p.start,heads,ambient⟩ : Configuration u s) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp]
      | some j =>
        have he := RecoveryFocus.slot_of_pick slot hp
        simpa only [RecoveryFocus.config,hp,initialConfiguration] using
          (hh0 j).symm.trans (congrArg heads he)
    · exact install_existing slot ambient input hin
  rw [hinit] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [hf,RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simpa only [hf,RecoveryFocus.config,hp] using
        (hh j).trans ((hh0 j).symm.trans (congrArg heads he))
  · rw [hf]
    change install slot ambient base.final.tapes=install slot ambient output
    rw [ht]

end NearCubicWires.RepairOrdinary.RecoveryRootRound

namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  row : RecoveryRowFields.Data
  key : List Bool
  saved : List Bool
  found : Bool
  same : Bool
  aux : Bool
  copyCapacity : Nat
  resetCapacity : Nat

def Data.extra (d : Data) : Fin 7→List Bool :=
  ![frame d.key,frame d.saved,[d.found],[d.same],[d.aux],
    List.replicate d.copyCapacity false,List.replicate d.resetCapacity false]
def Data.cfg {s : Nat} (d : Data) (q : Fin s) : Configuration 14 s :=
  ⟨q,Fin.addCases (m:=7) (n:=7) (motive:=fun _=>Nat) (d.row.cfg q).heads (fun _=>0),
    Fin.addCases (m:=7) (n:=7) (motive:=fun _=>List Bool) (d.row.cfg q).tapes d.extra⟩
def Data.Valid (d : Data) : Prop :=
  d.row.Valid ∧ d.key.length=d.row.width ∧ d.saved.length≤d.row.width ∧
    2*d.row.width+1≤d.copyCapacity ∧ 4*d.row.width+3≤d.resetCapacity

def cellSlots : Fin 9→Fin 14 := ![7,2,10,11,13,3,8,9,12]
theorem cellSlots_injective : Function.Injective cellSlots := by decide
noncomputable def cellMachine := RecoveryFocus.machine cellSlots RecoveryRowLookupCell.machine
noncomputable def readMachine := TapeEmbedding.machine 7 RecoveryRowFields.machine

def Data.cell (d : Data) (code count : List Bool) : RecoveryRowLookupCell.Data :=
  ⟨d.key,code,count,d.saved,d.found,d.same,d.aux,d.copyCapacity,d.resetCapacity⟩
def Data.afterCell (d : Data) (code count : List Bool) : Data :=
  let out := (d.cell code count).done
  {d with saved:=out.saved,found:=out.found,same:=out.same,aux:=out.aux}
def Data.afterRead (d : Data) (bits : List Bool) : Data :=
  {d with row:={RecoveryRowFields.afterReads d.row 0 4 bits with valid:=true}}

theorem cell_valid (d : Data) (code count : List Bool) (hd : d.Valid)
    (hc : code.length=d.row.width) (hn : count.length=d.row.width) : (d.cell code count).Valid :=
  ⟨hc.trans hd.2.1.symm,hn.trans hd.2.1.symm,by simpa only [Data.cell,hd.2.1] using hd.2.2.1,
    by simpa only [Data.cell,hd.2.1] using hd.2.2.2⟩

theorem cell_input (d : Data) (code count : List Bool)
    (hc : d.row.fields 1=frame code) (hn : d.row.fields 2=frame count) (j : Fin 9) :
    (d.cfg cellMachine.start).tapes (cellSlots j)=(d.cell code count).tapes j := by
  match j with
  | ⟨0,_⟩ => rfl
  | ⟨1,_⟩ => exact hc
  | ⟨2,_⟩ => rfl
  | ⟨3,_⟩ => rfl
  | ⟨4,_⟩ => rfl
  | ⟨5,_⟩ => exact hn
  | ⟨6,_⟩ => rfl
  | ⟨7,_⟩ => rfl
  | ⟨8,_⟩ => rfl
  | ⟨n+9,h⟩ => exact False.elim (by omega)

theorem cell_heads (d : Data) (j : Fin 9) : (d.cfg cellMachine.start).heads (cellSlots j)=0 := by
  match j with
  | ⟨0,_⟩ => rfl
  | ⟨1,_⟩ => rfl
  | ⟨2,_⟩ => rfl
  | ⟨3,_⟩ => rfl
  | ⟨4,_⟩ => rfl
  | ⟨5,_⟩ => rfl
  | ⟨6,_⟩ => rfl
  | ⟨7,_⟩ => rfl
  | ⟨8,_⟩ => rfl
  | ⟨n+9,h⟩ => exact False.elim (by omega)

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

private theorem cell_routing (base old fresh : Fin 7→List Bool) :
    install cellSlots (Fin.addCases (m:=7) (n:=7) (motive:=fun _=>List Bool) base old)
      (Fin.addCases (m:=5) (n:=4) (motive:=fun _=>List Bool)
        ![fresh 0,base 2,fresh 3,fresh 4,fresh 6] ![base 3,fresh 1,fresh 2,fresh 5])=
      Fin.addCases (m:=7) (n:=7) (motive:=fun _=>List Bool) base fresh := by
  apply install_eq cellSlots cellSlots_injective
  · intro j
    fin_cases j <;> rfl
  · intro i hi
    refine Fin.addCases (m:=7) (n:=7) (motive:=fun k=>(∀ j,cellSlots j≠k) →
      Fin.addCases (m:=7) (n:=7) (motive:=fun _=>List Bool) base old k=
        Fin.addCases (m:=7) (n:=7) (motive:=fun _=>List Bool) base fresh k) ?_ ?_ i hi
    · intro j _
      simp only [Fin.addCases_left]
    · intro j hj
      fin_cases j
      · exact False.elim (hj 0 rfl)
      · exact False.elim (hj 6 rfl)
      · exact False.elim (hj 7 rfl)
      · exact False.elim (hj 2 rfl)
      · exact False.elim (hj 3 rfl)
      · exact False.elim (hj 8 rfl)
      · exact False.elim (hj 4 rfl)

theorem cell_output (d : Data) (code count : List Bool)
    (hfc : d.row.fields 1=frame code) (hfn : d.row.fields 2=frame count) :
    install cellSlots (d.cfg cellMachine.start).tapes (d.cell code count).done.tapes=
      ((d.afterCell code count).cfg cellMachine.start).tapes := by
  have hk : (d.cell code count).done.key=d.key := by
    unfold RecoveryRowLookupCell.Data.done
    split <;> try rfl
    split <;> rfl
  have hc : (d.cell code count).done.code=code := by
    unfold RecoveryRowLookupCell.Data.done
    split <;> try rfl
    split <;> rfl
  have hn : (d.cell code count).done.count=count := by
    unfold RecoveryRowLookupCell.Data.done
    split <;> try rfl
    split <;> rfl
  have hcopy : (d.cell code count).done.copyCapacity=d.copyCapacity := by
    unfold RecoveryRowLookupCell.Data.done
    split <;> try rfl
    split <;> rfl
  have hreset : (d.cell code count).done.resetCapacity=d.resetCapacity := by
    unfold RecoveryRowLookupCell.Data.done
    split <;> try rfl
    split <;> rfl
  let base := (d.row.cfg (0 : Fin 1)).tapes
  let fresh := (d.afterCell code count).extra
  have hout : (d.cell code count).done.tapes=
      Fin.addCases (m:=5) (n:=4) (motive:=fun _=>List Bool)
        ![fresh 0,base 2,fresh 3,fresh 4,fresh 6] ![base 3,fresh 1,fresh 2,fresh 5] := by
    change Fin.addCases (m:=5) (n:=4) (motive:=fun _=>List Bool)
      ![frame (d.cell code count).done.key,frame (d.cell code count).done.code,
        [(d.cell code count).done.same],[(d.cell code count).done.aux],
        List.replicate (d.cell code count).done.resetCapacity false]
      ![frame (d.cell code count).done.count,frame (d.cell code count).done.saved,
        [(d.cell code count).done.found],List.replicate (d.cell code count).done.copyCapacity false]=_
    rw [hk,hc,hn,hcopy,hreset]
    simp only [fresh,base,Data.afterCell,Data.extra,RecoveryRowFields.Data.cfg,hfc,hfn]
    rfl
  change install cellSlots (Fin.addCases (m:=7) (n:=7) (motive:=fun _=>List Bool) base d.extra)
    (d.cell code count).done.tapes=Fin.addCases (m:=7) (n:=7) (motive:=fun _=>List Bool) base fresh
  rw [hout]
  exact cell_routing base d.extra fresh

theorem cell_run (d : Data) (code count : List Bool) (hd : d.Valid)
    (hc : code.length=d.row.width) (hn : count.length=d.row.width)
    (hfc : d.row.fields 1=frame code) (hfn : d.row.fields 2=frame count) :
    ∃ r,runFrom cellMachine (16*d.row.width+32) (d.cfg cellMachine.start)=some r ∧
      r.final=((d.afterCell code count).cfg r.final.control) ∧ r.steps≤16*d.row.width+32 := by
  obtain ⟨base,hr,ht,hh,hsteps⟩ := RecoveryRowLookupCell.cell_run (d.cell code count)
    (cell_valid d code count hd hc hn)
  have hready := ready_of_run RecoveryRowLookupCell.machine _ _ base hr hh
  rw [ht] at hready
  obtain ⟨r,hrun,hheads,htapes,hcount⟩ := hready.focus_at cellSlots cellSlots_injective
    (d.cfg cellMachine.start).heads (d.cfg cellMachine.start).tapes
    (cell_input d code count hfc hfn) (cell_heads d)
  have hbound : base.steps≤16*d.row.width+32 := by
    simpa only [Data.cell,hd.2.1] using hsteps
  have hm := runFrom_moreFuel cellMachine base.steps (16*d.row.width+32-base.steps)
    (d.cfg cellMachine.start) r hrun
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨r,hm,?_,hcount.le.trans hbound⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans (cell_output d code count hfc hfn)

theorem afterCell_valid (d : Data) (code count : List Bool) (hd : d.Valid)
    (hc : code.length=d.row.width) (hn : count.length=d.row.width) :
    (d.afterCell code count).Valid := by
  have hdone := RecoveryRowLookupCell.done_valid (d.cell code count) (cell_valid d code count hd hc hn)
  have hkey : (d.cell code count).done.key=d.key := by
    unfold RecoveryRowLookupCell.Data.done
    split <;> try rfl
    split <;> rfl
  refine ⟨hd.1,hd.2.1,?_,hd.2.2.2⟩
  change (d.cell code count).done.saved.length≤d.row.width
  exact hdone.2.2.1.trans (by rw [hkey,hd.2.1])

end NearCubicWires.RepairOrdinary.RecoveryRowLookupStream
