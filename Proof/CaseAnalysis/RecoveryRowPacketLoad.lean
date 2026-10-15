import Proof.CaseAnalysis.RecoveryRowPacketBudget

/-! Load the refreshed original row metadata through the existing paid
whole-bank erase and fifteen-field loader, retaining graph and saved refs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketLoad
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def localMachine:=Composition.machine RecoveryBoundedRowErase.machine RecoveryBoundedRowReload.machine
def budget (fields : Fin 78→List Bool) (B : ℕ):=2*B+4+1+RecoveryBoundedRowReload.budget fields B
def output (fields : Fin 78→List Bool) (B : ℕ) (A : Fin 78→List Bool):=
  RecoveryBoundedRowReload.loaded fields B (RecoveryBoundedRowErase.data B A)

theorem local_run (out stack tail : List Bool) (A fields : Fin 78→List Bool) (B : ℕ)
    (hw : A 73=List.replicate B false) (hp : A 75=RecoveryBoundedRowReload.word fields++tail)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hA : ∀ i,(A (RecoveryBoundedRowErase.work i)).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hpB : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ r,runFrom localMachine (budget fields B) ⟨localMachine.start,heads out stack,A⟩=some r ∧
      r.steps≤budget fields B ∧ r.final.heads=heads out stack ∧ r.final.tapes=output fields B A := by
  obtain ⟨p,pr,ph,pt,ps⟩:=RecoveryBoundedRowErase.erase_run B (heads out stack) A
    (RecoveryBoundedRowAfter.erase_heads out stack) hA hd hl
  have kept (i : Fin 78) (hi : 73 ≤ i.val) : RecoveryBoundedRowErase.data B A i=A i:=by
    simp only [RecoveryBoundedRowErase.data,
      show ¬(i.val<73 ∧ i≠20 ∧ i≠25 ∧ i≠70) by omega,↓reduceIte]
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedRowReload.reload_run fields B tail (heads out stack)
    (RecoveryBoundedRowErase.data B A) rfl rfl rfl (RecoveryBoundedRowAfter.heads_port out stack)
    (by rw [kept 75 (by decide)];exact hp) (by rw [kept 73 (by decide)];exact hw)
    (by rw [kept 76 (by decide)];exact hd) (RecoveryBoundedRowAfter.erased_port A B) hf hpB
  have qr' : runFrom RecoveryBoundedRowReload.machine (RecoveryBoundedRowReload.budget fields B)
      (restart p.final RecoveryBoundedRowReload.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have whole:=Composition.run_join RecoveryBoundedRowErase.machine RecoveryBoundedRowReload.machine _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,whole,?_,qh,qt⟩
  change p.steps+1+q.steps≤budget fields B
  unfold budget
  omega

def slots (i : Fin 78) : Fin 88:=i.castAdd 10
noncomputable def machine:=RecoveryFocus.machine slots localMachine
noncomputable def bank (fields : Fin 78→List Bool) (B : ℕ) (A : Fin 88→List Bool):=
  install slots A (output fields B (fun j=>A (slots j)))

theorem load_run (out stack tail : List Bool) (fields : Fin 78→List Bool) (B : ℕ)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (hH : ∀ j,H (slots j)=heads out stack j)
    (hw : A 73=List.replicate B false) (hp : A 75=RecoveryBoundedRowReload.word fields++tail)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hA : ∀ i,(A (slots (RecoveryBoundedRowErase.work i))).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hpB : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ r,runFrom machine (budget fields B) ⟨machine.start,H,A⟩=some r ∧
      r.steps≤budget fields B ∧ r.final.heads=H ∧ r.final.tapes=bank fields B A := by
  obtain ⟨p,pr,ps,ph,pt⟩:=local_run out stack tail (fun j=>A (slots j)) fields B hw hp hd hl hA hf hpB
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots (Fin.castAdd_injective 78 10)
    localMachine _ H A ⟨localMachine.start,heads out stack,fun j=>A (slots j)⟩ hH (fun _=>rfl) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      exact (hH j).symm
    · exact (rkeep i (by intro j he;exact hi ⟨j,he⟩)).1
  · have he:=HierarchyWidth.install_eq slots (Fin.castAdd_injective 78 10) A r.final.tapes
      (output fields B (fun j=>A (slots j)))
      (by intro j;rw [rt j,pt]) (by intro i hi;exact (rkeep i hi).2)
    exact he.symm

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketLoad
