import Proof.CaseAnalysis.RowsRawAtomReset

/-! One actual native count is consumed and its ordered child-index atom
is appended, followed by a paid private-bank erase. Only the four live
cursor fields survive; the same supplied preprocessing capacity is reused. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomReuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratch (i : Fin 10) : Fin 17 := ⟨i.val+1,by omega⟩
def eraseSlots : Fin 12→Fin 17:=![1,2,3,4,5,6,7,8,9,10,15,16]
theorem erase_injective : Function.Injective eraseSlots:=by decide
noncomputable def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 10)
noncomputable def first:=TapeEmbedding.machine 2 CloseoutRowsRawAtomReset.machine
noncomputable def machine:=Composition.machine first erase
def budget (C offset n : ℕ):=CloseoutRowsRawAtomReset.budget offset n+1+(2*C+4)
def extra (C : ℕ) : Fin 2→List Bool:=![List.replicate C true,List.replicate (C+1) false]
def heads (pos count : ℕ) (out : List Bool) (i : Fin 17) : ℕ:=
  if i=0 then pos else if i=11 then 1 else if i=12 then out.length
  else if i=13 then count+1 else 0
def data (C : ℕ) (source : List Bool) (offset count : ℕ) (out : List Bool)
    (i : Fin 17) : List Bool:=
  if i=0 then source else if i=11 then UnaryTemplate.tape (offset+1)
  else if i=12 then out else if i=13 then RepairSource.VerifierDecoding.CompareMachine.word count
  else if i=15 then List.replicate C true else if i=16 then List.replicate (C+1) false
  else List.replicate C false
noncomputable def entry (C : ℕ) (source : List Bool) (pos offset count : ℕ) (out : List Bool):=
  Composition.leftConfig 4 (TapeEmbedding.config (fun _ : Fin 2=>0) (extra C)
    (CloseoutRowsRawAtomReset.input C source pos offset count out))

theorem entry_fields (C : ℕ) (source : List Bool) (pos offset count : ℕ) (out : List Bool) :
    entry C source pos offset count out=⟨machine.start,heads pos count out,data C source offset count out⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;>
      simp [entry,CloseoutRowsRawAtomReset.input,ZeroPadding.config,Rewind.recording,Rewind.config,
        TapeEmbedding.config,Composition.leftConfig,Rewind.Workspace.capacities,Fin.addCases,
        CloseoutRowsRawAtomReset.caps,CloseoutRowsRawAtomReset.selected,data,extra,ZeroPadding.pad]
    all_goals rfl

theorem erase_run (C : ℕ) (H : Fin 17→ℕ) (A : Fin 17→List Bool)
    (hh : ∀ j,H (eraseSlots j)=0)
    (hb : ∀ i,(A (scratch i)).length≤C)
    (hd : A 15=List.replicate C true) (hl : A 16=List.replicate (C+1) false) :
    ∃ r,runFrom erase (2*C+4) ⟨erase.start,H,A⟩=some r ∧
      r.final.heads=H ∧
      r.final.tapes=install eraseSlots A (PCPTraversal.clearedLocal 10 C (C+1)) ∧
      r.steps=2*C+4 := by
  have raw:=RecoveryScratchErase.erase_ready C (C+1) (fun i=>A (scratch i)) hb
  apply raw.focus_at eraseSlots erase_injective H A
  · intro i
    fin_cases i <;> simp only [eraseSlots]
    all_goals first | exact hd | exact hl | rfl
  · exact hh

theorem reuse_run (C : ℕ) (pre tail out : List Bool) (offset n count : ℕ)
    (hc : CloseoutRowsRawAtomNative.budget offset n+1≤C) :
    let word:=out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)
    ∃ r,runFrom machine (budget C offset n)
      (entry C (pre++natWord n++tail) pre.length offset count out)=some r ∧
      r.final.heads=heads (pre.length+(natWord n).length) (count+n) word ∧
      r.final.tapes=data C (pre++natWord n++tail) (offset+n) (count+n) word ∧
      r.steps≤budget C offset n := by
  dsimp only
  obtain ⟨a,ha,t0,h0,t11,h11,t12,h12,t13,h13,workBound,h14,t14,_⟩:=
    CloseoutRowsRawAtomReset.reset_run C pre tail out offset n count hc
  let a':=TapeEmbedding.receipt (fun _ : Fin 2=>0) (extra C) a
  have firstRun:=TapeEmbedding.run_embed CloseoutRowsRawAtomReset.machine
    (fun _ : Fin 2=>0) (extra C) _ _ a ha
  have oldH (i : Fin 15):a'.final.heads (i.castAdd 2)=a.final.heads i:=by
    simp only [a',TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have oldT (i : Fin 15):a'.final.tapes (i.castAdd 2)=a.final.tapes i:=by
    simp only [a',TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have ph (i : Fin 10):a'.final.heads (scratch i)=0:=by
    have h:=workBound (⟨i.val+1,by omega⟩ : Fin 14) (by
      simp only [CloseoutRowsRawAtomReset.selected,decide_eq_true_eq];omega)
    exact (oldH ⟨i.val+1,by omega⟩).trans h.1
  have pt (i : Fin 10):(a'.final.tapes (scratch i)).length≤C:=by
    have h:=workBound (⟨i.val+1,by omega⟩ : Fin 14) (by
      simp only [CloseoutRowsRawAtomReset.selected,decide_eq_true_eq];omega)
    change (a'.final.tapes ((⟨i.val+1,by omega⟩ : Fin 15).castAdd 2)).length≤C
    rw [oldT]
    exact h.2.le
  obtain ⟨b,hb,bh,bt,_⟩:=erase_run C a'.final.heads a'.final.tapes (by
    intro i
    fin_cases i
    all_goals first
      | exact ph 0 | exact ph 1 | exact ph 2 | exact ph 3 | exact ph 4
      | exact ph 5 | exact ph 6 | exact ph 7 | exact ph 8 | exact ph 9 | rfl) pt rfl rfl
  have joined:=Composition.run_join first erase _ _ _ a' b firstRun hb
  have cleared (i : Fin 10):b.final.tapes (scratch i)=List.replicate C false:=by
    rw [bt]
    have e:eraseSlots ((i.castAdd 1).castAdd 1)=scratch i:=by fin_cases i <;> rfl
    rw [←e,install_slot _ erase_injective]
    simp only [PCPTraversal.clearedLocal,Fin.addCases_left]
  have live (i : Fin 17) (hi : ∀ j,eraseSlots j≠i):b.final.tapes i=a'.final.tapes i:=by
    rw [bt,install_other _ _ _ _ hi]
  have driver:b.final.tapes 15=List.replicate C true:=by
    change b.final.tapes (eraseSlots 10)=_
    rw [bt,install_slot _ erase_injective];rfl
  have log:b.final.tapes 16=List.replicate (C+1) false:=by
    change b.final.tapes (eraseSlots 11)=_
    rw [bt,install_slot _ erase_injective]
    simp [PCPTraversal.clearedLocal,Fin.addCases]
  refine ⟨Composition.joinedReceipt a' b,joined,?_,?_,runFrom_steps_le machine _ _ _ joined⟩
  · change b.final.heads=_
    rw [bh]
    funext i
    fin_cases i
    all_goals first
      | exact (oldH 0).trans h0 | exact (oldH 11).trans h11
      | exact (oldH 12).trans h12 | exact (oldH 13).trans h13 | exact (oldH 14).trans h14
      | exact ph 0 | exact ph 1 | exact ph 2 | exact ph 3 | exact ph 4 | exact ph 5
      | exact ph 6 | exact ph 7 | exact ph 8 | exact ph 9 | rfl
  · change b.final.tapes=_
    funext i
    fin_cases i
    all_goals first
      | exact (live 0 (by intro j;fin_cases j <;> decide)).trans ((oldT 0).trans t0)
      | exact (live 11 (by intro j;fin_cases j <;> decide)).trans ((oldT 11).trans t11)
      | exact (live 12 (by intro j;fin_cases j <;> decide)).trans ((oldT 12).trans t12)
      | exact (live 13 (by intro j;fin_cases j <;> decide)).trans ((oldT 13).trans t13)
      | exact (live 14 (by intro j;fin_cases j <;> decide)).trans ((oldT 14).trans t14)
      | exact cleared 0 | exact cleared 1 | exact cleared 2 | exact cleared 3 | exact cleared 4
      | exact cleared 5 | exact cleared 6 | exact cleared 7 | exact cleared 8 | exact cleared 9
      | exact driver | exact log

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomReuse
