import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.Amplification.RecoveryCursorCalls
import Proof.Amplification.RecoveryRowLookupTapes
import Proof.Hierarchy.HierarchyAllocation

/-! Six existing bounded-copy calls reload exactly the degree worker's
short metadata. Native row heads and the accumulated output cursor remain
at their physical positions. The C driver and log are shared and retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsMetadataReload
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dest : Fin 6→Fin 112 := ![51,52,61,66,89,90]
def source (i : Fin 6) : Fin 112 := i.natAdd 106
theorem dest_injective : Function.Injective dest := by decide
def slots (j : Fin 6) : Fin 4→Fin 112 := ![source j,dest j,104,105]
theorem injective (j : Fin 6) : Function.Injective (slots j) := by fin_cases j <;> decide
def sizes : Fin 6→ℕ := fun _=>4
noncomputable def programs (j : Fin 6) : Machine 112 (sizes j) :=
  RecoveryFocus.machine (slots j) RecoveryBoundedTapeCopy.machine
def next (j : Fin 6) (_q : Fin (sizes j)) (_bits : Fin 112→Bool) : Option (Fin 6) :=
  if h : j.val<5 then some ⟨j.val+1,by omega⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

noncomputable def data (A : Fin 112→List Bool) (C : ℕ)
    (templates : Fin 6→List Bool) (done : ℕ) : Fin 112→List Bool := fun i=>
  match RecoveryFocus.pick dest i with
  | none=>A i
  | some j=>if j.val<done then ZeroPadding.pad C (templates j) else List.replicate C false

theorem data_dest (A : Fin 112→List Bool) (C : ℕ) (templates : Fin 6→List Bool)
    (done : ℕ) (j : Fin 6) : data A C templates done (dest j)=
      if j.val<done then ZeroPadding.pad C (templates j) else List.replicate C false := by
  simp only [data,RecoveryFocus.pick_slot dest dest_injective]
theorem data_other (A : Fin 112→List Bool) (C : ℕ) (templates : Fin 6→List Bool)
    (done : ℕ) (i : Fin 112) (hi : ∀ j,dest j≠i) : data A C templates done i=A i := by
  have hn : ¬∃ j,dest j=i := by rintro ⟨j,hj⟩; exact hi j hj
  simp [data,RecoveryFocus.pick,hn]
theorem source_outside (i j : Fin 6) : dest i≠source j := by fin_cases i <;> fin_cases j <;> decide
theorem driver_outside (i : Fin 6) : dest i≠104 := by fin_cases i <;> decide
theorem log_outside (i : Fin 6) : dest i≠105 := by fin_cases i <;> decide

theorem data_next_other (A : Fin 112→List Bool) (C : ℕ) (templates : Fin 6→List Bool)
    (j : Fin 6) (i : Fin 112) (hi : dest j≠i) :
    data A C templates (j.val+1) i=data A C templates j.val i := by
  cases hp : RecoveryFocus.pick dest i with
  | none=>simp only [data,hp]
  | some k=>
    have hk : k≠j := by
      intro he
      exact hi (he ▸ RecoveryFocus.slot_of_pick dest hp)
    have hn : k.val≠j.val := fun h=>hk (Fin.ext h)
    have he : (k.val<j.val+1)=(k.val<j.val) := by apply propext; omega
    simp only [data,hp,he]

theorem copy_run (A : Fin 112→List Bool) (H : Fin 112→ℕ) (C : ℕ)
    (templates : Fin 6→List Bool) (j : Fin 6)
    (hA : ∀ i,A (source i)=templates i) (hc : ∀ i,(templates i).length≤C)
    (hd : A 104=List.replicate C true) (hl : A 105=List.replicate (C+1) false)
    (hH : ∀ i,H (slots j i)=0) :
    ∃ actual,runFrom (programs j) (2*C+4)
      ⟨(programs j).start,H,data A C templates j.val⟩=some actual ∧
      actual.final.heads=H ∧ actual.final.tapes=data A C templates (j.val+1) ∧
      actual.steps=2*C+4 := by
  have hin : ∀ i,data A C templates j.val (slots j i)=
      CloseoutRowsMetadataCopy.input (templates j) C i := by
    intro i
    fin_cases i
    · exact (data_other A C templates j.val (source j) (fun k=>source_outside k j)).trans (hA j)
    · change data A C templates j.val (dest j)=List.replicate C false
      simp only [data_dest,lt_self_iff_false,↓reduceIte]
    · exact (data_other A C templates j.val 104 driver_outside).trans hd
    · exact (data_other A C templates j.val 105 log_outside).trans hl
  obtain ⟨r,hr,rh,rt,rs⟩ := (CloseoutRowsMetadataCopy.copy_ready (templates j) C (hc j)).focus_at
    (slots j) (injective j) H (data A C templates j.val) hin hH
  have hout : install (slots j) (data A C templates j.val)
      (CloseoutRowsMetadataCopy.output (templates j) C)=data A C templates (j.val+1) := by
    apply HierarchyAllocation.install_eq (slots j) (injective j)
    · intro i
      fin_cases i
      · exact (data_other A C templates (j.val+1) (source j) (fun k=>source_outside k j)).trans (hA j)
      · change data A C templates (j.val+1) (dest j)=ZeroPadding.pad C (templates j)
        simp only [data_dest,Nat.lt_succ_self,↓reduceIte]
      · exact (data_other A C templates (j.val+1) 104 driver_outside).trans hd
      · exact (data_other A C templates (j.val+1) 105 log_outside).trans hl
    · intro i hi
      exact data_next_other A C templates j i (hi 1)
  exact ⟨r,hr,rh,rt.trans hout,rs⟩

noncomputable def atNode (j : Fin 6) (H : Fin 112→ℕ) (A : Fin 112→List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (RecoveryCalls.restarted (programs j) H A)

theorem call (A : Fin 112→List Bool) (H : Fin 112→ℕ) (C : ℕ)
    (templates : Fin 6→List Bool) (j k : Fin 6)
    (hn : ∀ q bits,next j q bits=some k)
    (hA : ∀ i,A (source i)=templates i) (hc : ∀ i,(templates i).length≤C)
    (hd : A 104=List.replicate C true) (hl : A 105=List.replicate (C+1) false)
    (hH : ∀ i,H (slots j i)=0) :
    ∃ n≤2*C+5,Timed machine n (atNode j H (data A C templates j.val))
      (atNode k H (data A C templates (j.val+1))) := by
  obtain ⟨r,hr,rh,rt,_⟩ := copy_run A H C templates j hA hc hd hl hH
  obtain ⟨n,hb,h⟩ := call_receipt sizes programs 0 next j k (2*C+4) _ r hr (hn _ _)
  rw [rh,rt] at h
  exact ⟨n,by omega,h⟩

theorem reload_run (A : Fin 112→List Bool) (H : Fin 112→ℕ) (C : ℕ)
    (templates : Fin 6→List Bool)
    (hA : ∀ i,A (source i)=templates i) (hc : ∀ i,(templates i).length≤C)
    (hd : A 104=List.replicate C true) (hl : A 105=List.replicate (C+1) false)
    (hH : ∀ j i,H (slots j i)=0) :
    ∃ actual,runFrom machine (6*(2*C+5))
      ⟨machine.start,H,data A C templates 0⟩=some actual ∧
      actual.final.heads=H ∧ actual.final.tapes=data A C templates 6 ∧
      actual.steps≤6*(2*C+5) := by
  obtain ⟨n0,h0,t0⟩ := call A H C templates 0 1 (by intro q bits; rfl) hA hc hd hl (hH 0)
  obtain ⟨n1,h1,t1⟩ := call A H C templates 1 2 (by intro q bits; rfl) hA hc hd hl (hH 1)
  obtain ⟨n2,h2,t2⟩ := call A H C templates 2 3 (by intro q bits; rfl) hA hc hd hl (hH 2)
  obtain ⟨n3,h3,t3⟩ := call A H C templates 3 4 (by intro q bits; rfl) hA hc hd hl (hH 3)
  obtain ⟨n4,h4,t4⟩ := call A H C templates 4 5 (by intro q bits; rfl) hA hc hd hl (hH 4)
  obtain ⟨r,hr,rh,rt,_⟩ := copy_run A H C templates 5 hA hc hd hl (hH 5)
  obtain ⟨n5,h5,t5⟩ := stop_receipt sizes programs 0 next 5 (2*C+4) _ r hr (by rfl)
  rw [rh,rt] at t5
  have whole := (((((t0.trans t1).trans t2).trans t3).trans t4).trans t5)
  obtain ⟨actual,ha,hf,hs⟩ := whole.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb : n0+n1+n2+n3+n4+n5≤6*(2*C+5) := by omega
  have more := runFrom_moreFuel machine _ (6*(2*C+5)-(n0+n1+n2+n3+n4+n5)) _ actual ha
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨actual,more,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le.trans hb⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsMetadataReload
