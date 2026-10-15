import Proof.MachineModel.Padded

/-! Execute the ordered incidence stream directly into native table36, using
the existing child template38 and paid bank driver104/log105. New slots are
stream113, scratch114, and the actual raw row count115. -/
namespace NearCubicWires.ExtIncidence.BankExecution
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 116 := ![113,38,114,36,115]
noncomputable def printer:=RecoveryFocus.machine slots ExtIncidence.machine
def changedHeads (H : Fin 116 → ℕ) (pos size count : ℕ):=
  Function.update (Function.update (Function.update H 113 pos) 36 size) 115 count
def changedTapes (A : Fin 116 → List Bool) (C : ℕ) (table : List Bool) (count : ℕ):=
  Function.update (Function.update A 36 (ZeroPadding.pad C table)) 115
    (ZeroPadding.pad C (List.replicate count true))

theorem printer_run {B : ℕ} (ms : List (List (Fin B))) (C : ℕ) (hB : B ≤ C)
    (pre tail : List Bool) (H : Fin 116 → ℕ) (A : Fin 116 → List Bool)
    (hh : ∀ j,H (slots j)=Padded.heads pre.length 0 0 j)
    (ht : ∀ j,A (slots j)=Padded.tapes C B (pre++stream (rawIndices ms)++tail) [] 0 j) :
    PCPOuter.Exact printer (cost B (rawIndices ms)) H A
      (changedHeads H (pre.length+(stream (rawIndices ms)).length) (rawRows ms).flatten.length ms.length)
      (changedTapes A C (rawRows ms).flatten ms.length) := by
  obtain ⟨base,hbase,bh,bt,bs⟩:=Padded.raw_run ms C hB pre tail
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots (by decide) ExtIncidence.machine
    _ H A _ hh ht base hbase
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · funext i
    by_cases inside : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=inside
      rw [rh,bh]
      fin_cases j <;> simp [slots,changedHeads,Padded.heads]
      · exact (hh 1).symm
      · exact (hh 2).symm
    · have outside:∀ j,slots j≠i:=by simpa only [not_exists] using inside
      have n113 : i≠113:=Ne.symm (outside 0)
      have n36 : i≠36:=Ne.symm (outside 3)
      have n115 : i≠115:=Ne.symm (outside 4)
      simpa only [changedHeads,Function.update_of_ne n115,Function.update_of_ne n36,
        Function.update_of_ne n113] using (keep i outside).1
  · funext i
    by_cases inside : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=inside
      rw [rt,bt]
      fin_cases j <;> simp [slots,changedTapes,Padded.tapes]
      · have hsource : A 113=pre++stream (rawIndices ms)++tail:=ht 0
        rw [List.append_assoc] at hsource
        exact hsource.symm
      · exact (ht 1).symm
      · exact (ht 2).symm
    · have outside:∀ j,slots j≠i:=by simpa only [not_exists] using inside
      have n36 : i≠36:=Ne.symm (outside 3)
      have n115 : i≠115:=Ne.symm (outside 4)
      simpa only [changedTapes,Function.update_of_ne n115,Function.update_of_ne n36]
        using (keep i outside).2

def returnSlots (i : Fin 116) : Fin 3 → Fin 116 := ![i,104,105]
noncomputable def returning (i : Fin 116):=
  RecoveryFocus.machine (returnSlots i) CompetitorRecordRewind.machine
noncomputable def tableReady:=Composition.machine printer (returning 36)
noncomputable def machine:=Composition.machine tableReady (returning 115)
def budget (B C : ℕ) (ms : List (List ℕ)):=cost B ms+4*C+6

theorem return_run (i : Fin 116) (hi : i≠104 ∧ i≠105) (C : ℕ)
    (H : Fin 116 → ℕ) (A : Fin 116 → List Bool) (hp : H i ≤ C)
    (hdh : H 104=0) (hlh : H 105=0)
    (hd : A 104=List.replicate C true) (hl : A 105=List.replicate (C+1) false) :
    PCPOuter.Exact (returning i) (2*C+2) H A (Function.update H i 0) A := by
  have inj:Function.Injective (returnSlots i):=by
    intro j k h;fin_cases j <;> fin_cases k <;> simp_all [returnSlots]
  obtain ⟨base,hb,bh,bt,bs⟩:=CloseoutRowsCircuitCounterReturn.return_run C (H i) (A i) hp
  have heads:∀ j,H (returnSlots i j)=(![H i,0,0] : Fin 3 → ℕ) j:=by
    intro j;fin_cases j
    · rfl
    · exact hdh
    · exact hlh
  have tapes:∀ j,A (returnSlots i j)=CloseoutRowsCircuitCounterReturn.input C (A i) j:=by
    intro j;fin_cases j
    · rfl
    · exact hd
    · exact hl
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock (returnSlots i) inj CompetitorRecordRewind.machine
    _ H A _ heads tapes base hb
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · apply Function.eq_update_iff.mpr
    refine ⟨(rh 0).trans (congrFun bh 0),?_⟩
    intro j hj
    by_cases inside:∃ k,returnSlots i k=j
    · obtain ⟨k,rfl⟩:=inside
      rw [rh,bh,heads]
      fin_cases k
      · exact False.elim (hj rfl)
      · rfl
      · rfl
    · exact (keep j (by simpa only [not_exists] using inside)).1
  · funext j
    by_cases inside:∃ k,returnSlots i k=j
    · obtain ⟨k,rfl⟩:=inside
      rw [rt,bt]
      exact (tapes k).symm
    · exact (keep j (by simpa only [not_exists] using inside)).2

theorem raw_run {B : ℕ} (ms : List (List (Fin B))) (C : ℕ) (hB : B ≤ C)
    (pre tail : List Bool) (H : Fin 116 → ℕ) (A : Fin 116 → List Bool)
    (hh : ∀ j,H (slots j)=Padded.heads pre.length 0 0 j)
    (ht : ∀ j,A (slots j)=Padded.tapes C B (pre++stream (rawIndices ms)++tail) [] 0 j)
    (hsize : (rawRows ms).flatten.length ≤ C) (hcount : ms.length ≤ C)
    (hdh : H 104=0) (hlh : H 105=0)
    (hd : A 104=List.replicate C true) (hl : A 105=List.replicate (C+1) false) :
    PCPOuter.Exact machine (budget B C (rawIndices ms)) H A
      (changedHeads H (pre.length+(stream (rawIndices ms)).length) 0 0)
      (changedTapes A C (rawRows ms).flatten ms.length) := by
  let midH:=changedHeads H (pre.length+(stream (rawIndices ms)).length) (rawRows ms).flatten.length ms.length
  let midA:=changedTapes A C (rawRows ms).flatten ms.length
  have first:=printer_run ms C hB pre tail H A hh ht
  have second:=return_run 36 (by decide) C midH midA
    (by simpa [midH,changedHeads] using hsize)
    (by simpa [midH,changedHeads] using hdh) (by simpa [midH,changedHeads] using hlh)
    (by simpa [midA,changedTapes] using hd) (by simpa [midA,changedTapes] using hl)
  have third:=return_run 115 (by decide) C (Function.update midH 36 0) midA
    (by simpa [midH,changedHeads] using hcount)
    (by simpa [midH,changedHeads] using hdh) (by simpa [midH,changedHeads] using hlh)
    (by simpa [midA,changedTapes] using hd) (by simpa [midA,changedTapes] using hl)
  have whole:=PCPOuter.exact_join (PCPOuter.exact_join first second) third
  have time:cost B (rawIndices ms)+1+(2*C+2)+1+(2*C+2)=budget B C (rawIndices ms):=by
    unfold budget;omega
  have finalHeads:Function.update (Function.update midH 36 0) 115 0=
      changedHeads H (pre.length+(stream (rawIndices ms)).length) 0 0:=by
    funext i
    by_cases h36:i=36 <;> by_cases h115:i=115 <;> simp_all [midH,changedHeads]
  rw [time,finalHeads] at whole
  exact whole

end NearCubicWires.ExtIncidence.BankExecution
