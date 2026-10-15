import Proof.CaseAnalysis.WitnessSelectedSource
import Proof.MachineModel.OrdinaryRewindWorkspace

/-! The same actual PCPP output supplies systematic, auxiliary and clause
counts. One paid tag skip precedes the existing three-natural-field reader;
the source and all three templates return at head zero for later consumers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourceFields
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def skipSlots : Fin 3→Fin 33:=![0,31,32]
def nodeSlots (i : Fin 31) : Fin 33:=i.castAdd 2
theorem node_injective : Function.Injective nodeSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 33=>k.val) h)
noncomputable def skip:=RecoveryFocus.machine skipSlots (PCPPQueryField.machine false)
noncomputable def read:=RecoveryFocus.machine nodeSlots PCPPNativeNodeRead.machine
noncomputable def raw:=Composition.machine skip read
def word (a b c : ℕ) (tail : List Bool):=PCPPNativeNodeRead.source (natWord 3) tail a b c
def rawInput (source : List Bool) (i : Fin 33):=if i=0 then source else []
def rawBudget (a b c : ℕ):=PCPPQueryField.fieldCost 3+1+PCPPNativeNodeRead.budget a b c
def outputSlot (i : Fin 3):=nodeSlots (PCPPNativeNodeRead.outputSlot i)
noncomputable def machine:=Rewind.machine raw
def input (source : List Bool) : Fin 34→List Bool:=
  Fin.addCases (m:=33) (n:=1) (motive:=fun _=>List Bool) (rawInput source) (fun _=>[])
def budget (a b c : ℕ):=2*rawBudget a b c+2

theorem skip_pick (i : Fin 31) : RecoveryFocus.pick skipSlots (nodeSlots i)=
    if i=0 then some 0 else none:=by
  by_cases hi:i=0
  · subst i
    exact RecoveryFocus.pick_slot skipSlots (by decide) 0
  · have hn:¬∃ j,skipSlots j=nodeSlots i:=by
      rintro ⟨j,hj⟩
      fin_cases j
      · exact hi (Fin.ext (congrArg Fin.val hj).symm)
      · have hv:=congrArg Fin.val hj
        change 31=i.val at hv
        omega
      · have hv:=congrArg Fin.val hj
        change 32=i.val at hv
        omega
    simp only [RecoveryFocus.pick,dif_neg hn,if_neg hi]

theorem raw_run (a b c : ℕ) (tail : List Bool) : ∃ r,
    run raw (rawBudget a b c) (rawInput (word a b c tail))=some r ∧
      r.steps ≤ rawBudget a b c ∧ r.final.tapes 0=word a b c tail ∧
      (∀ i : Fin 3,r.final.tapes (outputSlot i)=UnaryTemplate.tape (![a,b,c] i)):=by
  let source:=word a b c tail
  obtain ⟨s,hs,sf,ss⟩:=PCPPQueryField.nat_run false [] (natWord a++natWord b++natWord c++tail) [] [] 3
  have he:[]++natWord 3++(natWord a++natWord b++natWord c++tail)=source:=by
    simp only [source,word,PCPPNativeNodeRead.source,List.nil_append,List.append_assoc]
  rw [he] at hs sf
  simp only [List.length_nil] at hs sf
  obtain ⟨first,hfirst,ff,fs⟩:=RecoveryFocus.run_config skipSlots (by decide) (PCPPQueryField.machine false)
    (fun _=>0) (rawInput source) _ _ s hs
  have hi:RecoveryFocus.config skipSlots (fun _=>0) (rawInput source)
      (PCPPQueryField.cfg 0 source 0 [] 0 [])=initialConfiguration skip (rawInput source):=by
    apply WilliamsSourceCrop.focus_same skipSlots (initialConfiguration skip (rawInput source))
    · intro j;fin_cases j <;> rfl
    · intro j;fin_cases j <;> rfl
  rw [hi] at hfirst
  obtain ⟨n,hn,ns,n0,_,nt,_⟩:=PCPPNativeNodeRead.cold_run (natWord 3) tail a b c
  have nh:∀ j,first.final.heads (nodeSlots j)=
      (PCPPNativeNodeRead.entry source (natWord 3).length).heads j:=by
    intro j
    rw [ff,sf]
    simp only [RecoveryFocus.config,skip_pick]
    by_cases hj:j=0
    · subst j
      simp only [ite_true,PCPPQueryField.payload,PCPPQueryField.cfg,PCPPNativeNodeRead.entry,
        Nat.zero_add,DecompositionSource.natWord_length]
      rfl
    · simp only [hj,ite_false,PCPPNativeNodeRead.entry]
  have ntapes:∀ j,first.final.tapes (nodeSlots j)=
      (PCPPNativeNodeRead.entry source (natWord 3).length).tapes j:=by
    intro j
    rw [ff,sf]
    simp only [RecoveryFocus.config,skip_pick]
    by_cases hj:j=0
    · subst j;rfl
    · have hne:nodeSlots j≠0:=by
        intro h
        exact hj (Fin.ext (congrArg (fun i : Fin 33=>i.val) h))
      simp only [hj,ite_false,rawInput,hne,PCPPNativeNodeRead.entry]
  obtain ⟨last,hl,_,ls,_,lt,_⟩:=RecoveryFocus.dock nodeSlots node_injective
    PCPPNativeNodeRead.machine _ first.final.heads first.final.tapes
    (PCPPNativeNodeRead.entry source (natWord 3).length) nh ntapes n hn
  have joined:=Composition.run_join skip read _ _ _ first last hfirst hl
  refine ⟨Composition.joinedReceipt first last,joined,?_,?_,?_⟩
  · change first.steps+1+last.steps ≤ rawBudget a b c
    rw [fs,ss,ls]
    unfold rawBudget PCPPQueryField.fieldCost
    omega
  · exact (lt 0).trans n0
  · intro i
    exact (lt (PCPPNativeNodeRead.outputSlot i)).trans (nt i)

theorem fields_run (a b c : ℕ) (tail : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget a b c) (input (word a b c tail)) output ∧
      output 0=word a b c tail ∧
      (∀ i : Fin 3,output ((outputSlot i).castAdd 1)=UnaryTemplate.tape (![a,b,c] i)):=by
  obtain ⟨base,hb,bs,b0,bt⟩:=raw_run a b c tail
  obtain ⟨r,hr,rt,_,rh,rs,_⟩:=Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have ht:2*base.steps+2 ≤ budget a b c:=by unfold budget;omega
  have h:ClockJoin.ReadyRun machine (2*base.steps+2) (input (word a b c tail)) r.final.tapes:=
    ⟨r,hr,rfl,rh,rs.le⟩
  refine ⟨r.final.tapes,ClockJoin.enlarge machine _ _ _ _ h ht,(rt 0).trans b0,?_⟩
  intro i
  exact (rt (outputSlot i)).trans (bt i)

end NearCubicWires.RepairOrdinary.CloseoutWitness.SourceFields
