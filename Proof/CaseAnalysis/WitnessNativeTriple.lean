import Proof.CaseAnalysis.WitnessNativeAppend

/-! Three existing native-field copies share one scratch tape and the live
descriptor cursor. All three original words remain present; only the final
whole-node reset is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeTriple
open LocalBitMultitape RecoveryExecution RadixSemantics StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 3) : Fin 3 → Fin 5:=![j.castAdd 2,3,4]
theorem slots_injective (j : Fin 3) : Function.Injective (slots j):=by fin_cases j <;> decide
noncomputable def part (j : Fin 3):=RecoveryFocus.machine (slots j) NativeAppend.machine
noncomputable def first:=Composition.machine (part 0) (part 1)
noncomputable def machine:=Composition.machine first (part 2)

def accumulated (bits : Fin 3 → List Bool) (out : List Bool) : ℕ → List Bool
  | 0=>out
  | k+1=>if h:k<3 then accumulated bits out k++NativeWord.word (bits ⟨k,h⟩) else accumulated bits out k
def backing (bits : Fin 3 → List Bool) (old : List Bool) : ℕ → List Bool
  | 0=>old
  | k+1=>if h:k<3 then overlay (UnaryTemplate.tape (NativeAppend.payload (bits ⟨k,h⟩)).length)
      (backing bits old k) else backing bits old k
def heads (bits : Fin 3 → List Bool) (out : List Bool) (k : ℕ) (i : Fin 5) : ℕ:=
  if h:i.val<3 then if i.val<k then (NativeWord.word (bits ⟨i.val,h⟩)).length else 0
  else if i.val=3 then 0 else (accumulated bits out k).length
def data (bits : Fin 3 → List Bool) (old out : List Bool) (k : ℕ) (i : Fin 5) : List Bool:=
  if h:i.val<3 then NativeWord.word (bits ⟨i.val,h⟩)
  else if i.val=3 then backing bits old k else accumulated bits out k
def stage (bits : Fin 3 → List Bool) (old out : List Bool) (k : ℕ) : Configuration 5 4:=
  ⟨0,heads bits out k,data bits old out k⟩
def finish (bits : Fin 3 → List Bool) (old out : List Bool) (k : ℕ) : Configuration 5 4:=
  ⟨3,heads bits out k,data bits old out k⟩
noncomputable def entry (bits : Fin 3 → List Bool) (old out : List Bool) : Configuration 5 12:=
  ⟨machine.start,heads bits out 0,data bits old out 0⟩
def budget (bits : Fin 3 → List Bool):=2*((bits 0).length+(bits 1).length+(bits 2).length)+17

theorem local_heads (bits : Fin 3 → List Bool) (old out : List Bool) (j : Fin 3) :
    ∀ i,(stage bits old out j.val).heads (slots j i)=
      (NativeAppend.entry (bits j) (backing bits old j.val) (accumulated bits out j.val)).heads i:=by
  intro i
  fin_cases j <;> fin_cases i <;> simp [stage,slots,heads,NativeAppend.entry,PCPPQueryField.cfg]
theorem local_data (bits : Fin 3 → List Bool) (old out : List Bool) (j : Fin 3) :
    ∀ i,(stage bits old out j.val).tapes (slots j i)=
      (NativeAppend.entry (bits j) (backing bits old j.val) (accumulated bits out j.val)).tapes i:=by
  intro i
  fin_cases j <;> fin_cases i <;> simp [stage,slots,data,NativeAppend.entry,PCPPQueryField.cfg]

theorem local_final (bits : Fin 3 → List Bool) (old out : List Bool) (j : Fin 3) :
    RecoveryFocus.config (slots j) (heads bits out j.val) (data bits old out j.val)
      (NativeAppend.result (bits j) (backing bits old j.val) (accumulated bits out j.val))=
        finish bits old out (j.val+1):=by
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi:∃ k,slots j k=i
    · obtain ⟨k,rfl⟩:=hi
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot _ (slots_injective j)]
      fin_cases j <;> fin_cases k <;> simp [NativeAppend.result,finish,heads,slots,accumulated]
    · have h0:slots j 0≠i:=by intro h;exact hi ⟨0,h⟩
      have h3:slots j 1≠i:=by intro h;exact hi ⟨1,h⟩
      have h4:slots j 2≠i:=by intro h;exact hi ⟨2,h⟩
      have hs3:i.val≠3:=by intro h;exact h3 (Fin.ext h.symm)
      have hs4:i.val≠4:=by intro h;exact h4 (Fin.ext h.symm)
      have hil:i.val<3:=by omega
      have hn:i.val≠j.val:=by intro h;exact h0 (Fin.ext h.symm)
      have he:(i.val<j.val+1) ↔ i.val<j.val:=by omega
      simp [RecoveryFocus.config,RecoveryFocus.pick,hi,finish,heads,hil,he]
  · funext i
    by_cases hi:∃ k,slots j k=i
    · obtain ⟨k,rfl⟩:=hi
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot _ (slots_injective j)]
      fin_cases j <;> fin_cases k <;> simp [NativeAppend.result,finish,data,slots,accumulated,backing]
    · have h3:slots j 1≠i:=by intro h;exact hi ⟨1,h⟩
      have h4:slots j 2≠i:=by intro h;exact hi ⟨2,h⟩
      have hs3:i.val≠3:=by intro h;exact h3 (Fin.ext h.symm)
      have hs4:i.val≠4:=by intro h;exact h4 (Fin.ext h.symm)
      have hil:i.val<3:=by omega
      simp [RecoveryFocus.config,RecoveryFocus.pick,hi,finish,data,hil]

theorem part_run (bits : Fin 3 → List Bool) (old out : List Bool) (j : Fin 3) : ∃ r,
    runFrom (part j) (2*(bits j).length+5) (stage bits old out j.val)=some r ∧
      r.final=finish bits old out (j.val+1) ∧ r.steps ≤ 2*(bits j).length+5:=by
  obtain ⟨raw,hr,hf,hs⟩:=NativeAppend.append_run (bits j) (backing bits old j.val) (accumulated bits out j.val)
  obtain ⟨r,h,he,ht⟩:=RecoveryFocus.run_config (slots j) (slots_injective j) NativeAppend.machine
    (heads bits out j.val) (data bits old out j.val) _ _ raw hr
  have hi:=WilliamsSourceCrop.focus_same (slots j) (stage bits old out j.val)
    (NativeAppend.entry (bits j) (backing bits old j.val) (accumulated bits out j.val))
    (local_heads bits old out j) (local_data bits old out j)
  dsimp only [stage] at hi
  rw [hi] at h
  refine ⟨r,h,?_,ht.trans_le hs⟩
  rw [he,hf,local_final]

theorem triple_run (bits : Fin 3 → List Bool) (old out : List Bool) : ∃ r,
    runFrom machine (budget bits) (entry bits old out)=some r ∧ r.steps ≤ budget bits ∧
      r.final.heads=heads bits out 3 ∧ r.final.tapes=data bits old out 3:=by
  obtain ⟨a,ha,af,as⟩:=part_run bits old out 0
  obtain ⟨b,hb,bf,bs⟩:=part_run bits old out 1
  obtain ⟨c,hc,cf,cs⟩:=part_run bits old out 2
  have hb':runFrom (part 1) (2*(bits 1).length+5) (Composition.restart a.final (part 1).start)=some b:=by
    rw [af];exact hb
  have hab:=Composition.run_join (part 0) (part 1) _ _ _ a b ha hb'
  have hc':runFrom (part 2) (2*(bits 2).length+5)
      (Composition.restart (Composition.joinedReceipt a b).final (part 2).start)=some c:=by
    change runFrom (part 2) _ (Composition.restart b.final (part 2).start)=some c
    rw [bf];exact hc
  have h:=Composition.run_join first (part 2) _ _ _ (Composition.joinedReceipt a b) c hab hc'
  change runFrom machine (((2*(bits 0).length+5)+1+(2*(bits 1).length+5))+1+(2*(bits 2).length+5))
    (entry bits old out)=some (Composition.joinedReceipt (Composition.joinedReceipt a b) c) at h
  have ht:((2*(bits 0).length+5)+1+(2*(bits 1).length+5))+1+(2*(bits 2).length+5)=budget bits:=by
    unfold budget;omega
  rw [ht] at h
  refine ⟨_,h,?_,?_,?_⟩
  · change (a.steps+1+b.steps)+1+c.steps ≤ _
    unfold budget;omega
  · change c.final.heads=_
    rw [cf];rfl
  · change c.final.tapes=_
    rw [cf];rfl

theorem prefix_three (bits : Fin 3 → List Bool) (out : List Bool) : accumulated bits out 3=
    out++(List.ofFn (fun j=>NativeWord.word (bits j))).flatten:=by
  simp [accumulated,List.ofFn_succ,List.append_assoc]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeTriple
