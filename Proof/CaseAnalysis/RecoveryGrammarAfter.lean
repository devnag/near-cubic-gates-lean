import Proof.CaseAnalysis.RecoveryGrammarWorker

/-! An original grammar child returns its output reference on25. Save that
reference, advance the actual count once, and reuse the paid row-bank erase
and prototype loader. No child graph is copied or reconstructed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarAfter
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def referenceSlots : Fin 3→Fin 78:=![25,74,73]
noncomputable def reference:=RecoveryFocus.machine referenceSlots RecoveryBoundedAddress.reference
def advanced (A : Fin 78→List Bool) (ref : ℕ) (stack : List Bool):=
  Function.update (Function.update A 25 (List.replicate (ref+1) true)) 74
    (RecoveryBoundedAddress.pushed ref stack)

theorem reference_run (out stack : List Bool) (A : Fin 78→List Bool) (ref B : ℕ)
    (ha : A 25=List.replicate ref true) (hs : A 74=stack) (hw : A 73=List.replicate B false)
    (hB : 2*ref+2≤B) :
    ∃ r,runFrom reference (6*ref+11) ⟨reference.start,heads out stack,A⟩=some r ∧
      r.steps≤6*ref+11 ∧ r.final.heads=heads out (RecoveryBoundedAddress.pushed ref stack) ∧
      r.final.tapes=advanced A ref stack := by
  obtain ⟨p,pr,ph,pt,ps⟩:=RecoveryBoundedAddress.reference_run ref B stack hB
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock referenceSlots (by decide) RecoveryBoundedAddress.reference
    _ (heads out stack) A ⟨RecoveryBoundedAddress.reference.start,
      RecoveryBoundedSelectorReference.heads stack,RecoveryBoundedSelectorReference.data ref B stack⟩
    (by intro j;fin_cases j <;> rfl)
    (by intro j;fin_cases j;exact ha;exact hs;exact hw) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,referenceSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j <;> rfl
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      have h74 : i≠74:=fun he=>hi ⟨1,he.symm⟩
      simp only [heads,if_neg h74]
  · funext i
    by_cases hi : ∃ j,referenceSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      fin_cases j
      · rfl
      · rfl
      · change List.replicate B false=advanced A ref stack 73
        simpa only [advanced,Function.update_of_ne (by decide : (73 : Fin 78)≠74),
          Function.update_of_ne (by decide : (73 : Fin 78)≠25)] using hw.symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).2]
      have h25 : i≠25:=fun he=>hi ⟨0,he.symm⟩
      have h74 : i≠74:=fun he=>hi ⟨1,he.symm⟩
      simp only [advanced,Function.update_of_ne h25,Function.update_of_ne h74]

noncomputable def first:=Composition.machine reference RecoveryBoundedRowErase.machine
noncomputable def machine:=Composition.machine first RecoveryBoundedRowReload.machine
def budget (ref B : ℕ) (fields : Fin 78→List Bool):=
  (6*ref+11)+1+(2*B+4)+1+RecoveryBoundedRowReload.budget fields B
def output (fields : Fin 78→List Bool) (A : Fin 78→List Bool) (ref B : ℕ) (stack : List Bool):=
  RecoveryBoundedRowReload.loaded fields B (RecoveryBoundedRowErase.data B (advanced A ref stack))

theorem after_run (out stack tail : List Bool) (A fields : Fin 78→List Bool) (ref B : ℕ)
    (ha : A 25=List.replicate ref true) (hs : A 74=stack) (hw : A 73=List.replicate B false)
    (hp : A 75=RecoveryBoundedRowReload.word fields++tail)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hB : 2*ref+2≤B) (hA : ∀ i,(A (RecoveryBoundedRowErase.work i)).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hpB : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ r,runFrom machine (budget ref B fields) ⟨machine.start,heads out stack,A⟩=some r ∧
      r.steps≤budget ref B fields ∧
      r.final.heads=heads out (RecoveryBoundedAddress.pushed ref stack) ∧
      r.final.tapes=output fields A ref B stack := by
  let nextStack:=RecoveryBoundedAddress.pushed ref stack
  let nextA:=advanced A ref stack
  obtain ⟨p,pr,ps,ph,pt⟩:=reference_run out stack A ref B ha hs hw hB
  have keep (i : Fin 78) (h25 : i≠25) (h74 : i≠74) : nextA i=A i := by
    simp only [nextA,advanced,Function.update_of_ne h25,Function.update_of_ne h74]
  have size : ∀ i,(nextA (RecoveryBoundedRowErase.work i)).length≤B := by
    intro i
    rw [keep _ (RecoveryBoundedRowErase.work_spec i).2.2.1
      (RecoveryBoundedRowErase.work_high i 74 (by decide))]
    exact hA i
  obtain ⟨q,qr,qh,qt,qs⟩:=RecoveryBoundedRowErase.erase_run B (heads out nextStack) nextA
    (RecoveryBoundedRowAfter.erase_heads out nextStack) size
    (by rw [keep 76 (by decide) (by decide)];exact hd)
    (by rw [keep 77 (by decide) (by decide)];exact hl)
  have qr' : runFrom RecoveryBoundedRowErase.machine (2*B+4)
      (restart p.final RecoveryBoundedRowErase.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have firstRun:=Composition.run_join reference RecoveryBoundedRowErase.machine _ _ _ p q pr qr'
  have kept (i : Fin 78) (hi : (73 : ℕ) ≤ i.val) (h74 : i≠74) :
      RecoveryBoundedRowErase.data B nextA i=A i := by
    have h25 : i≠25:=by intro he;subst i;omega
    simp only [RecoveryBoundedRowErase.data,show ¬(i.val<73 ∧ i≠20 ∧ i≠25 ∧ i≠70) by omega,↓reduceIte]
    exact keep i h25 h74
  obtain ⟨s,sr,ss,sh,st⟩:=RecoveryBoundedRowReload.reload_run fields B tail (heads out nextStack)
    (RecoveryBoundedRowErase.data B nextA) rfl rfl rfl (RecoveryBoundedRowAfter.heads_port out nextStack)
    (by rw [kept 75 (by decide) (by decide)];exact hp)
    (by rw [kept 73 (by decide) (by decide)];exact hw)
    (by rw [kept 76 (by decide) (by decide)];exact hd)
    (RecoveryBoundedRowAfter.erased_port nextA B) hf hpB
  have sr' : runFrom RecoveryBoundedRowReload.machine (RecoveryBoundedRowReload.budget fields B)
      (restart (joinedReceipt p q).final RecoveryBoundedRowReload.machine.start)=some s := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some s
    rw [qh,qt]
    exact sr
  have whole:=Composition.run_join first RecoveryBoundedRowReload.machine _ _ _ (joinedReceipt p q) s firstRun sr'
  refine ⟨joinedReceipt (joinedReceipt p q) s,whole,?_,sh,st⟩
  change p.steps+1+q.steps+1+s.steps≤budget ref B fields
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarAfter
