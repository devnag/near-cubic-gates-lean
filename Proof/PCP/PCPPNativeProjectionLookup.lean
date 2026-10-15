import Proof.PCP.PCPPNativeProjectionRead
import Proof.PCP.ProjectionNormalizationFieldList
import Proof.PCP.PCPFieldMoves

/-! Paid lookup of one raw projection code. A real unary index drives the
skipped scan; only the selected field enters the existing binary unpair.
The original stream is retained, with its precise advanced cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeProjectionLookup
open LocalBitMultitape RadixSemantics RepairSource.ProjectionNormalization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def skipSlots : Fin 3 → Fin 28 := ![0,1,2]
def copySlots : Fin 3 → Fin 28 := ![0,3,4]
def readSlots (i : Fin 24) : Fin 28 := if i=0 then 3 else ⟨i.val+4,by omega⟩
theorem read_injective : Function.Injective readSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [readSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega
theorem read_away (i : Fin 24) : 3≤(readSlots i).val := by
  unfold readSlots
  split_ifs
  · decide
  · change 3 ≤ i.val+4
    omega
noncomputable def skip := RecoveryFocus.machine skipSlots FieldList.machine
noncomputable def copy := RecoveryFocus.machine copySlots PCPFieldMoves.advanceMachine
noncomputable def read := RecoveryFocus.machine readSlots PCPPNativeProjectionRead.machine
noncomputable def machine := Composition.machine (Composition.machine skip copy) read
def data (source : List Bool) (count : ℕ) (i : Fin 28) : List Bool :=
  if i=0 then source else if i=2 then CompareMachine.word count else []
def heads (pos : ℕ) (i : Fin 28) : ℕ := if i=0 then pos else if i=2 then 1 else 0
noncomputable def entry (source : List Bool) (pos count : ℕ) :=
  (⟨machine.start,heads pos,data source count⟩ : Configuration 28 _)
def budget (skipped : List (List Bool)) (bits : List Bool) :=
  (FieldList.stream skipped).length+3*skipped.length+3+1+
    (4*bits.length+4)+1+PCPPNativeProjectionRead.budget bits

theorem lookup_run (pre : List Bool) (skipped : List (List Bool)) (bits suffix : List Bool) :
    ∃ r,runFrom machine (budget skipped bits)
      (entry (pre++FieldList.stream skipped++frame bits++suffix) pre.length skipped.length)=some r ∧
      r.steps≤budget skipped bits ∧
      r.final.tapes 0=pre++FieldList.stream skipped++frame bits++suffix ∧
      r.final.heads 0=pre.length+(FieldList.stream skipped).length+2*bits.length+1 ∧
      r.final.tapes 2=CompareMachine.word skipped.length ∧ r.final.heads 2=1 ∧
      r.final.tapes 22=CompareMachine.word (Nat.unpair (value bits)).1 ∧
      r.final.tapes 26=CompareMachine.word (Nat.unpair (value bits)).2 ∧
      r.final.heads 22=1 ∧ r.final.heads 26=1 := by
  let source := pre++FieldList.stream skipped++frame bits++suffix
  obtain ⟨sk,hsk,skf,sks⟩ := FieldList.copy_run pre skipped (frame bits++suffix) []
  obtain ⟨first,hfirst,_,firstSteps,firstHeads,firstTapes,firstKeep⟩ := RecoveryFocus.dock
    skipSlots (by decide) FieldList.machine _ (heads pre.length) (data source skipped.length)
    (FieldList.cfg 0 (pre++FieldList.stream skipped++(frame bits++suffix)) pre.length [] skipped.length 1)
    (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i
        · simp only [source,data,List.append_assoc]; rfl
        all_goals rfl) sk hsk
  obtain ⟨cp,hcp,cpt,cph,cps⟩ := PCPFieldMoves.advance_run
    (pre++FieldList.stream skipped) bits suffix 0 0
  obtain ⟨second,hsecond,_,secondSteps,secondHeads,secondTapes,secondKeep⟩ := RecoveryFocus.dock
    copySlots (by decide) PCPFieldMoves.advanceMachine _ first.final.heads first.final.tapes
    (PCPFieldMoves.entry (pre++FieldList.stream skipped) bits suffix 0 0)
    (by intro i; fin_cases i
        · have h := firstHeads 0; rw [skf] at h
          change first.final.heads 0=pre.length+(FieldList.stream skipped).length at h
          change first.final.heads 0=(pre++FieldList.stream skipped).length
          simpa only [List.length_append] using h
        · exact (firstKeep 3 (by decide)).1
        · exact (firstKeep 4 (by decide)).1)
    (by intro i; fin_cases i
        · have h := firstTapes 0; rw [skf] at h
          change first.final.tapes 0=pre++FieldList.stream skipped++(frame bits++suffix) at h
          change first.final.tapes 0=ZeroPadding.pad 0 ((pre++FieldList.stream skipped)++frame bits++suffix)
          simpa only [List.append_assoc,ZeroPadding.pad_zero] using h
        · exact (firstKeep 3 (by decide)).2
        · exact (firstKeep 4 (by decide)).2) cp hcp
  obtain ⟨rd,hrd,rds,rdl,rdr,rdlh,rdrh⟩ := PCPPNativeProjectionRead.read_run bits
  have outside (i : Fin 24) (hi : i≠0) :
      second.final.heads (readSlots i)=0 ∧ second.final.tapes (readSlots i)=[] := by
    have hval : 5≤(readSlots i).val := by
      have hiv : i.val≠0 := fun h => hi (Fin.ext h)
      simp only [readSlots,hi,ite_false,Fin.val_mk]
      omega
    have hc := secondKeep (readSlots i) (by
      intro j
      have hj : (copySlots j).val≤4 := by fin_cases j <;> decide
      apply Fin.ne_of_val_ne
      omega)
    have hs := firstKeep (readSlots i) (by
      intro j
      have hj : (skipSlots j).val≤2 := by fin_cases j <;> decide
      apply Fin.ne_of_val_ne
      omega)
    have h0 : readSlots i≠0 := fun h => by
      have hv := congrArg Fin.val h
      change (readSlots i).val=0 at hv
      omega
    have h2 : readSlots i≠2 := fun h => by
      have hv := congrArg Fin.val h
      change (readSlots i).val=2 at hv
      omega
    exact ⟨hc.1.trans (hs.1.trans (by simp only [heads,h0,h2,ite_false])),
      hc.2.trans (hs.2.trans (by simp only [data,h0,h2,ite_false]))⟩
  obtain ⟨third,hthird,_,thirdSteps,thirdHeads,thirdTapes,thirdKeep⟩ := RecoveryFocus.dock
    readSlots read_injective PCPPNativeProjectionRead.machine _ second.final.heads second.final.tapes
    (initialConfiguration PCPPNativeProjectionRead.machine (PCPPNativeProjectionRead.input bits))
    (by intro i; by_cases hi : i=0
        · subst i; exact (secondHeads 1).trans (by rw [cph]; rfl)
        · exact (outside i hi).1)
    (by intro i; by_cases hi : i=0
        · subst i; exact (secondTapes 1).trans (by rw [cpt]; exact ZeroPadding.pad_zero _)
        · simpa only [initialConfiguration,PCPPNativeProjectionRead.input,hi,ite_false] using (outside i hi).2)
    rd hrd
  obtain ⟨result,hresult,resultHeads,resultTapes,resultSteps⟩ := PCPPRequestNodeFields.join_three_run
    skip copy read _ _ _ _ first second third hfirst hsecond hthird
  refine ⟨result,hresult,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [resultSteps,firstSteps,secondSteps,thirdSteps,sks,cps]
    unfold budget
    omega
  · rw [resultTapes,(thirdKeep 0 (by intro i; have := read_away i; apply Fin.ne_of_val_ne; omega)).2]
    exact (secondTapes 0).trans (by rw [cpt]; rfl)
  · rw [resultHeads,(thirdKeep 0 (by intro i; have := read_away i; apply Fin.ne_of_val_ne; omega)).1]
    have h := secondHeads 0
    rw [cph] at h
    change second.final.heads 0=(pre++FieldList.stream skipped).length+2*bits.length+1 at h
    simpa only [List.length_append] using h
  · rw [resultTapes,(thirdKeep 2 (by intro i; have := read_away i; apply Fin.ne_of_val_ne; omega)).2,
      (secondKeep 2 (by decide)).2]
    exact (firstTapes 2).trans (by rw [skf]; rfl)
  · rw [resultHeads,(thirdKeep 2 (by intro i; have := read_away i; apply Fin.ne_of_val_ne; omega)).1,
      (secondKeep 2 (by decide)).1]
    exact (firstHeads 2).trans (by rw [skf]; rfl)
  · rw [resultTapes]; exact (thirdTapes 18).trans rdl
  · rw [resultTapes]; exact (thirdTapes 22).trans rdr
  · rw [resultHeads]; exact (thirdHeads 18).trans rdlh
  · rw [resultHeads]; exact (thirdHeads 22).trans rdrh

end NearCubicWires.RepairOrdinary.PCPPNativeProjectionLookup
