import Proof.CaseAnalysis.CaseTwoSourceBlock
import Proof.PCP.PCPPNativeNodeRead

/-! Read the three actual PCPP dimensions from its original native header.
The existing field skipper pays for the list tag, then the existing native
three-field reader produces the counts. Every cursor is restored. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Shape
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def skipSlots : Fin 3→Fin 33:=![0,31,32]
def nodeSlots (i : Fin 31) : Fin 33:=i.castAdd 2
def skip:=RecoveryFocus.machine skipSlots (PCPPQueryField.machine false)
def nodes:=RecoveryFocus.machine nodeSlots PCPPNativeNodeRead.machine
def raw:=Composition.machine skip nodes
def machine:=Rewind.machine raw
def word (sys aux cb : ℕ) (tail : List Bool):=natWord 3++natWord sys++natWord aux++natWord cb++tail
def rawInput (sys aux cb : ℕ) (tail : List Bool) : Fin 33→List Bool:=
  SourceHandoff.sourceTapes (word sys aux cb tail)
def input (sys aux cb : ℕ) (tail : List Bool) : Fin 34→List Bool:=
  SourceHandoff.sourceTapes (word sys aux cb tail)
def rawBudget (sys aux cb : ℕ):=PCPPQueryField.fieldCost 3+1+PCPPNativeNodeRead.budget sys aux cb
def budget (sys aux cb : ℕ):=2*rawBudget sys aux cb+2
def outputSlot (j : Fin 3) : Fin 34:=(nodeSlots (PCPPNativeNodeRead.outputSlot j)).castAdd 1

theorem raw_run (sys aux cb : ℕ) (tail : List Bool) :
    ∃ r,run raw (rawBudget sys aux cb) (rawInput sys aux cb tail)=some r ∧
      r.steps≤rawBudget sys aux cb ∧ r.final.tapes 0=word sys aux cb tail ∧
      ∀ j : Fin 3,r.final.tapes (nodeSlots (PCPPNativeNodeRead.outputSlot j))=
        UnaryTemplate.tape (![sys,aux,cb] j):=by
  obtain ⟨sk,hsk,skf,sks⟩:=PCPPQueryField.nat_run false []
    (natWord sys++natWord aux++natWord cb++tail) [] [] 3
  have hword : []++natWord 3++(natWord sys++natWord aux++natWord cb++tail)=word sys aux cb tail:=by
    simp only [word,List.nil_append,List.append_assoc]
  rw [hword] at hsk skf
  obtain ⟨first,hfirst,_,fs,fh,ft,keep⟩:=RecoveryFocus.dock skipSlots (by decide)
    (PCPPQueryField.machine false) _ (fun _=>0) (rawInput sys aux cb tail) _
    (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>rfl) sk hsk
  obtain ⟨nr,hn,ns,nt,_,nout,_⟩:=PCPPNativeNodeRead.cold_run (natWord 3) tail sys aux cb
  have source_eq : PCPPNativeNodeRead.source (natWord 3) tail sys aux cb=word sys aux cb tail:=rfl
  rw [source_eq] at hn nt
  have entry_heads (j : Fin 31) : first.final.heads (nodeSlots j)=
      (PCPPNativeNodeRead.entry (word sys aux cb tail) (natWord 3).length).heads j:=by
    by_cases hj : j=0
    · subst j
      have h:=fh 0
      rw [skf] at h
      simpa [nodeSlots,skipSlots,PCPPNativeNodeRead.entry,PCPPQueryField.payload,PCPPQueryField.cfg,
        DecompositionSource.natWord_length] using h
    · have hn0 : j.val≠0:=fun he=>hj (Fin.ext he)
      have ha : ∀ i,skipSlots i≠nodeSlots j:=by
        intro i he
        have hv:=congrArg Fin.val he
        fin_cases i <;>simp [skipSlots,nodeSlots] at hv <;>omega
      simpa [PCPPNativeNodeRead.entry,hj] using (keep _ ha).1
  have entry_tapes (j : Fin 31) : first.final.tapes (nodeSlots j)=
      (PCPPNativeNodeRead.entry (word sys aux cb tail) (natWord 3).length).tapes j:=by
    by_cases hj : j=0
    · subst j
      have h:=ft 0
      rw [skf] at h
      exact h
    · have hn0 : j.val≠0:=fun he=>hj (Fin.ext he)
      have ha : ∀ i,skipSlots i≠nodeSlots j:=by
        intro i he
        have hv:=congrArg Fin.val he
        fin_cases i <;>simp [skipSlots,nodeSlots] at hv <;>omega
      rw [(keep _ ha).2]
      simp [rawInput,SourceHandoff.sourceTapes,nodeSlots,PCPPNativeNodeRead.entry,hj,hn0]
  obtain ⟨last,hl,_,ls,_,lt,_⟩:=RecoveryFocus.dock nodeSlots
    (by intro i j he;apply Fin.ext;exact congrArg (fun x : Fin 33=>x.val) he) PCPPNativeNodeRead.machine _
    first.final.heads first.final.tapes _ entry_heads entry_tapes nr hn
  have whole:=Composition.run_join skip nodes _ _ _ first last hfirst hl
  refine ⟨_,whole,?_,?_,?_⟩
  · change first.steps+1+last.steps≤_
    rw [fs,sks,ls]
    unfold rawBudget PCPPQueryField.fieldCost
    omega
  · change last.final.tapes (nodeSlots 0)=_
    exact (lt 0).trans nt
  · intro j
    change last.final.tapes (nodeSlots (PCPPNativeNodeRead.outputSlot j))=_
    exact (lt _).trans (nout j)

theorem shape_run (sys aux cb : ℕ) (tail : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget sys aux cb) (input sys aux cb tail) out ∧
      out 0=word sys aux cb tail ∧
      ∀ j : Fin 3,out (outputSlot j)=UnaryTemplate.tape (![sys,aux,cb] j):=by
  obtain ⟨base,hb,bs,b0,bt⟩:=raw_run sys aux cb tail
  obtain ⟨r,hr,rt,rh,rs,_⟩:=Rewind.reset_run raw _ _ base hb
  have hi : Fin.addCases (m:=33) (n:=1) (motive:=fun _=>List Bool)
      (rawInput sys aux cb tail) (fun _=>[])=input sys aux cb tail:=by
    exact PCPPRequestSource.single_input_from (t:=33) (by decide) _ _ rfl
  rw [hi] at hr
  have ready : ClockJoin.ReadyRun machine (2*base.steps+2) (input sys aux cb tail) r.final.tapes:=
    ⟨r,hr,rfl,rh,rs.le⟩
  exact ⟨_,ClockJoin.enlarge _ _ _ _ _ ready (by unfold budget;omega),
    (rt 0).trans b0,fun j=>(rt _).trans (bt j)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Shape
