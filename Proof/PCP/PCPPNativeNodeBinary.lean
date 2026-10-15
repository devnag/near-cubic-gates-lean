import Proof.PCP.PCPPNativeNodeNot

/-! Whole AND/OR paths: both parser-produced indices are converted on
disjoint physical banks, then the shared-address emitter runs and halts. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem arg_disjoint (i j : Fin 5) : argSlots false i≠argSlots true j := by
  fin_cases i <;> fin_cases j <;> decide
theorem field_right_away (i : Fin 24) : ∀ j,argSlots true j≠fieldSlots false i := by
  fin_cases i <;> decide

def binaryTag (isOr : Bool) : Fin 5 := if isOr then 4 else 3
def binaryBudget (isOr : Bool) (left right base C : ℕ) :=
  PCPPNativeNodeClassify.budget (binaryTag isOr) left right+(4*left+16)+(4*right+16)+
    PCPPNativeBinary.budget isOr base left right C+4

theorem binary_run (pre tail queries : List Bool) (isOr : Bool) (left right base position C : ℕ)
    (out : List Bool) (hleft : PCPPNativeAddressAppend.budget base left+1 ≤ C)
    (hright : PCPPNativeAddressAppend.budget base right+1 ≤ C) :
    ∃ r,runFrom machine (binaryBudget isOr left right base C)
      (entry (PCPPNativeNodeRead.source pre tail (binaryTag isOr).val left right) queries pre.length base position C out)=some r ∧
      r.steps ≤ binaryBudget isOr left right base C ∧
      r.final.tapes 0=PCPPNativeNodeRead.source pre tail (binaryTag isOr).val left right ∧
      r.final.heads 0=pre.length+(natWord (binaryTag isOr).val).length+(natWord left).length+(natWord right).length ∧
      (∀ i,r.final.heads (binarySlots i)=PCPPNativeBinary.heads (out++PCPPNativeBinary.emitted isOr base left right) i ∧
        r.final.tapes (binarySlots i)=PCPPNativeBinary.data base left right C (out++PCPPNativeBinary.emitted isOr base left right) i) ∧
      (∀ i,(∀ j,readSlots j≠i) → (∀ j,argSlots false j≠i) → (∀ j,argSlots true j≠i) →
        (∀ j,binarySlots j≠i) → r.final.heads i=initialHeads pre.length out i ∧
          r.final.tapes i=initialData (PCPPNativeNodeRead.source pre tail (binaryTag isOr).val left right) queries base position C out i) := by
  obtain ⟨a,ha,as,ac,a0,ah0,_,_,a7,ah7,a8,ah8,akeep⟩ :=
    reader_run pre tail queries (binaryTag isOr) left right base position C out
  have awork (rgt : Bool) (i : Fin 5) (hi : i≠0) :
      a.final.heads (argSlots rgt i)=0 ∧ a.final.tapes (argSlots rgt i)=[] := by
    have k := akeep (argSlots rgt i) (arg_work_away rgt i hi).1
    have z := arg_work_initial rgt i hi (PCPPNativeNodeRead.source pre tail (binaryTag isOr).val left right) queries pre.length base position C out
    exact ⟨k.1.trans z.1,k.2.trans z.2⟩
  have ready := argument_input false left a.final.heads a.final.tapes ah7 a7 (awork false)
  obtain ⟨b,hb,bs,bh,_,bt,bkeep⟩ := arg_run false left a.final.heads a.final.tapes ready.1 ready.2
  have b8 := bkeep 8 (by decide)
  have bwork (i : Fin 5) (hi : i≠0) : b.final.heads (argSlots true i)=0 ∧ b.final.tapes (argSlots true i)=[] := by
    have k := bkeep (argSlots true i) (fun j => arg_disjoint j i)
    exact ⟨k.1.trans (awork true i hi).1,k.2.trans (awork true i hi).2⟩
  have readyRight := argument_input true right b.final.heads b.final.tapes
    (b8.1.trans ah8) (b8.2.trans a8) bwork
  obtain ⟨c,hc,cs,ch,_,ct,ckeep⟩ := arg_run true right b.final.heads b.final.tapes readyRight.1 readyRight.2
  have fieldReady (i : Fin 24) :
      c.final.heads (fieldSlots false i)=PCPPNativeAddressReusable.heads out i ∧
      c.final.tapes (fieldSlots false i)=PCPPNativeAddressReusable.data base left C out i := by
    have ck := ckeep (fieldSlots false i) (field_right_away i)
    by_cases hi : i=1
    · subst i; exact ⟨ck.1.trans (bh 1),ck.2.trans bt⟩
    · have k := bkeep (fieldSlots false i) (field_arg_away i hi)
      have ar := akeep (fieldSlots false i) (field_read_away false i)
      have ini := initial_field false i hi (PCPPNativeNodeRead.source pre tail (binaryTag isOr).val left right) queries pre.length base position left C out
      exact ⟨ck.1.trans (k.1.trans (ar.1.trans ini.1)),ck.2.trans (k.2.trans (ar.2.trans ini.2))⟩
  have binaryReady (i : Fin 25) : c.final.heads (binarySlots i)=PCPPNativeBinary.heads out i ∧
      c.final.tapes (binarySlots i)=PCPPNativeBinary.data base left right C out i := by
    refine Fin.addCases (m := 24) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simpa only [binarySlots,PCPPNativeBinary.heads,PCPPNativeBinary.data,Fin.addCases_left] using fieldReady j
    · fin_cases j; exact ⟨ch 1,ct⟩
  obtain ⟨raw,hraw,raws,rawh,rawt⟩ := PCPPNativeBinary.node_run isOr base left right C out hleft hright
  obtain ⟨d,hd,_,ds,dh,dt,dkeep⟩ := RecoveryFocus.dock binarySlots binary_injective
    (PCPPNativeBinary.machine isOr) _ c.final.heads c.final.tapes (PCPPNativeBinary.entry isOr base left right C out)
    (fun i => (binaryReady i).1) (fun i => (binaryReady i).2) raw hraw
  have full : Timed machine ((a.steps+1)+(b.steps+1)+(c.steps+1)+(d.steps+1))
      (entry (PCPPNativeNodeRead.source pre tail (binaryTag isOr).val left right) queries pre.length base position C out)
      (RecoveryCalls.stopped sizes d.final.heads d.final.tapes) := by
    cases isOr
    · have p0 := call_run 0 6 _ _ _ a ha (parsed_next 3 a.final.control a.final.scanned ac)
      have p1 := call_run 6 7 _ _ _ b hb (by rfl)
      have p2 := call_run 7 8 _ _ _ c hc (by rfl)
      have p3 := stop_run 8 _ _ _ d hd (by rfl)
      exact ((p0.trans p1).trans p2).trans p3
    · have p0 := call_run 0 9 _ _ _ a ha (parsed_next 4 a.final.control a.final.scanned ac)
      have p1 := call_run 9 10 _ _ _ b hb (by rfl)
      have p2 := call_run 10 11 _ _ _ c hc (by rfl)
      have p3 := stop_run 11 _ _ _ d hd (by rfl)
      exact ((p0.trans p1).trans p2).trans p3
  obtain ⟨result,hresult,rf,rs⟩ := full.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have timeBound : (a.steps+1)+(b.steps+1)+(c.steps+1)+(d.steps+1) ≤ binaryBudget isOr left right base C := by
    unfold binaryBudget; omega
  have more := runFrom_moreFuel machine _
    (binaryBudget isOr left right base C-((a.steps+1)+(b.steps+1)+(c.steps+1)+(d.steps+1))) _ result hresult
  rw [Nat.add_sub_of_le timeBound] at more
  have d0 := dkeep 0 (by decide)
  have c0 := ckeep 0 (by decide)
  have b0 := bkeep 0 (by decide)
  refine ⟨result,more,by omega,?_,?_,?_,?_⟩
  · rw [rf]; exact d0.2.trans (c0.2.trans (b0.2.trans a0))
  · rw [rf]; exact d0.1.trans (c0.1.trans (b0.1.trans ah0))
  · intro i
    rw [rf]
    exact ⟨(dh i).trans (congrFun rawh i),(dt i).trans (congrFun rawt i)⟩
  · intro i hir hil hia hif
    rw [rf]
    exact ⟨(dkeep i hif).1.trans ((ckeep i hia).1.trans ((bkeep i hil).1.trans (akeep i hir).1)),
      (dkeep i hif).2.trans ((ckeep i hia).2.trans ((bkeep i hil).2.trans (akeep i hir).2))⟩

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
