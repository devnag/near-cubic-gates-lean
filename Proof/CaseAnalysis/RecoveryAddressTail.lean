import Proof.CaseAnalysis.RecoveryAddressScalarPorts

/-! The paid common tail of both address branches preserves its actual
child reference and restores the next unary input and address cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape RepairRepresentation RecoveryRootRound RecoveryExecution Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def referenceSlots : Fin 3→Fin 40:=![25,38,32]
def restoreSlots : Fin 7→Fin 40:=![1,39,29,34,32,22,23]
noncomputable def saveReference:=RecoveryFocus.machine referenceSlots reference
noncomputable def restore:=RecoveryFocus.machine restoreSlots RecoveryBoundedAddressRestore.machine
def advance : Machine 40 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun i=>if i=37 then .right else .stay⟩ else none
noncomputable def tailMachine:=Composition.machine (Composition.machine saveReference restore) advance
def tailBudget (acc index value C : ℕ):=(6*acc+11)+1+(2*C+2*index+2*value+14)+2

theorem save_run (index acc C D value limit pos retained : ℕ) (flag : Bool)
    (out source stack : List Bool) (hC : 2*acc+2 ≤ C) :
    ∃ r,runFrom saveReference (6*acc+11)
      ⟨saveReference.start,heads out stack pos,data index acc C D value limit flag out source stack retained⟩=some r ∧
      r.steps ≤ 6*acc+11 ∧ r.final.heads=heads out (pushed acc stack) pos ∧
      r.final.tapes=data index (acc+1) C D value limit flag out source (pushed acc stack) retained := by
  obtain ⟨p,hp,ph,pt,ps⟩:=reference_run acc C stack hC
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock referenceSlots (by decide) reference _
    (heads out stack pos) (data index acc C D value limit flag out source stack retained)
    ⟨reference.start,RecoveryBoundedSelectorReference.heads stack,RecoveryBoundedSelectorReference.data acc C stack⟩
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl) p hp
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,referenceSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j <;> rfl
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h38 : i≠38 := fun h=>hi ⟨1,h.symm⟩
      fin_cases i
      all_goals first | exact False.elim (h38 rfl) | rfl
  · have he:=HierarchyWidth.install_eq referenceSlots (by decide)
      (data index acc C D value limit flag out source stack retained) r.final.tapes
      (RecoveryBoundedSelectorReference.data (acc+1) C (pushed acc stack))
      (by intro j;rw [rt j,pt]) (by intro i hi;exact (rkeep i hi).2)
    rw [←he]
    apply HierarchyWidth.install_eq referenceSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      have h25 : i≠25:=fun h=>hi 0 h.symm
      have h38 : i≠38:=fun h=>hi 1 h.symm
      simp only [data_override,if_neg h25,if_neg h38]

theorem restore_run (index spent base C D value limit pos : ℕ) (flag : Bool)
    (out source stack : List Bool) (hi : index+1 ≤ C) (hs : spent ≤ C) (hv : value+1 ≤ C) :
    ∃ r,runFrom restore (2*C+2*index+2*value+14)
      ⟨restore.start,heads out stack pos,data spent base C D value limit flag out source stack index⟩=some r ∧
      r.steps=2*C+2*index+2*value+14 ∧ r.final.heads=heads out stack pos ∧
      r.final.tapes=data index base C D (value+1) limit false out source stack index := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedAddressRestore.restore_ready index spent value C flag hi hs hv).focus_at
    restoreSlots (by decide) (heads out stack pos) (data spent base C D value limit flag out source stack index)
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl)
  have he : install restoreSlots (data spent base C D value limit flag out source stack index)
      (RecoveryBoundedAddressRestore.data index spent value C flag 3)=
      data index base C D (value+1) limit false out source stack index := by
    apply HierarchyWidth.install_eq restoreSlots (by decide)
    · intro j
      fin_cases j <;> first
      | rfl
      | exact RecoveryBoundedSelectorLoop.pad_false C (by omega)
    · intro i hi
      have h1 : i≠1:=fun h=>hi 0 h.symm
      have h29 : i≠29:=fun h=>hi 2 h.symm
      have h34 : i≠34:=fun h=>hi 3 h.symm
      simp only [data_override,if_neg h1,if_neg h29,if_neg h34]
  rw [he] at rt
  exact ⟨r,hr,rs,rh,rt⟩

theorem advance_run (index base C D value limit pos retained : ℕ) (flag : Bool) (out source stack : List Bool) :
    ∃ r,runFrom advance 1
      ⟨advance.start,heads out stack pos,data index base C D value limit flag out source stack retained⟩=some r ∧
      r.steps=1 ∧ r.final.heads=heads out stack (pos+1) ∧
      r.final.tapes=data index base C D value limit flag out source stack retained := by
  have hstep : step advance
      ⟨advance.start,heads out stack pos,data index base C D value limit flag out source stack retained⟩=
      some ⟨1,heads out stack (pos+1),data index base C D value limit flag out source stack retained⟩ := by
    simp only [step,advance,Fin.val_zero,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=37
      · subst i;rfl
      · change HeadMove.apply (if i=37 then .right else .stay) (heads out stack pos i)=_
        rw [if_neg hi]
        fin_cases i
        all_goals first | exact False.elim (hi rfl) | rfl
    · rfl
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hstep).run (by rfl)
  exact ⟨r,hr,rs,by rw [rf],by rw [rf]⟩

theorem tail_run (index spent acc C D value limit pos : ℕ) (flag : Bool)
    (out source stack : List Bool) (hi : index+1 ≤ C) (hs : spent ≤ C) (hv : value+1 ≤ C) (ha : 2*acc+2 ≤ C) :
    ∃ r,runFrom tailMachine (tailBudget acc index value C)
      ⟨tailMachine.start,heads out stack pos,data spent acc C D value limit flag out source stack index⟩=some r ∧
      r.steps ≤ tailBudget acc index value C ∧ r.final.heads=heads out (pushed acc stack) (pos+1) ∧
      r.final.tapes=data index (acc+1) C D (value+1) limit false out source (pushed acc stack) index := by
  obtain ⟨a,haRun,as,ah,atapes⟩:=save_run spent acc C D value limit pos index flag out source stack ha
  obtain ⟨b,hbRun,bs,bh,bt⟩:=restore_run index spent (acc+1) C D value limit pos flag out source (pushed acc stack) hi hs hv
  have hb' : runFrom restore (2*C+2*index+2*value+14) (restart a.final restore.start)=some b := by
    change runFrom restore _ ⟨restore.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact hbRun
  have hab:=Composition.run_join saveReference restore _ _ _ a b haRun hb'
  obtain ⟨c,hcRun,cs,ch,ct⟩:=advance_run index (acc+1) C D (value+1) limit pos index false out source (pushed acc stack)
  have hc' : runFrom advance 1 (restart (joinedReceipt a b).final advance.start)=some c := by
    change runFrom advance 1 ⟨advance.start,b.final.heads,b.final.tapes⟩=some c
    rw [bh,bt]
    exact hcRun
  have full:=Composition.run_join (Composition.machine saveReference restore) advance _ _ _ (joinedReceipt a b) c hab hc'
  refine ⟨joinedReceipt (joinedReceipt a b) c,full,?_,ch,ct⟩
  change a.steps+1+b.steps+1+c.steps ≤ tailBudget acc index value C
  unfold tailBudget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
