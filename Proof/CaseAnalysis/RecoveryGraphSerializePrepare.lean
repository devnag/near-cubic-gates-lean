import Proof.CaseAnalysis.RecoveryQueryRewind
import Proof.CaseAnalysis.RecoveryGrammarScalarAdd
import Proof.Amplification.RecoveryTseitinRawIncrement

/-! Paid preparation of the four original cold-serializer inputs. The
original native graph is returned using the retained coarse driver; the
actual output reference is copied and incremented, and arity is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerializePrepare
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedGrammarScalarAdd (unary)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_ready (n sourceCap outCap B : ℕ) (hB : n+1≤B) :
    ClockJoin.ReadyRun PCPUnaryCopy.machine (2*n+4)
      ![unary sourceCap n,List.replicate outCap false,List.replicate B false]
      ![unary sourceCap n,unary outCap n,List.replicate B false] := by
  obtain ⟨r,hr,ht,hh,hs⟩ := PCPUnaryCopy.copy_ready n sourceCap outCap B
  rw [max_eq_left hB] at ht
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem increment_ready (n B : ℕ) (hB : n+1≤B) :
    ClockJoin.ReadyRun RepairSource.RecoveryTseitinRawIncrement.machine (2*n+4)
      ![unary B n,List.replicate B false] ![unary B (n+1),List.replicate B false] := by
  obtain ⟨p,hp,pt,ph,ps⟩ := RepairSource.RecoveryTseitinRawIncrement.increment_ready n B hB
  let caps : Fin 2→ℕ := ![B,0]
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config
    RepairSource.RecoveryTseitinRawIncrement.machine caps _ _ p hp
  have hi : ZeroPadding.config caps
      (initialConfiguration RepairSource.RecoveryTseitinRawIncrement.machine
        ![List.replicate n true,List.replicate B false])=
      initialConfiguration RepairSource.RecoveryTseitinRawIncrement.machine
        ![unary B n,List.replicate B false] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i
      · rfl
      · exact ZeroPadding.pad_zero _
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.le.trans ps.le⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps i) (p.final.tapes i))=_
    rw [pt]
    funext i;fin_cases i
    · rfl
    · exact ZeroPadding.pad_zero _
  · intro i
    rw [rf]
    exact ph i

def rewindSlots : Fin 3→Fin 7 := ![0,4,5]
def copyRefSlots : Fin 3→Fin 7 := ![1,3,5]
def incrementSlots : Fin 2→Fin 7 := ![3,5]
def copyAritySlots : Fin 3→Fin 7 := ![2,6,5]
theorem copyArity_injective : Function.Injective copyAritySlots := by
  intro i j he
  have hv := congrArg Fin.val he
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (norm_num [copyAritySlots] at hv)
noncomputable def rewind := RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine
noncomputable def copyRef := RecoveryFocus.machine copyRefSlots PCPUnaryCopy.machine
noncomputable def increment := RecoveryFocus.machine incrementSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def copyArity := RecoveryFocus.machine copyAritySlots PCPUnaryCopy.machine
noncomputable def copies := Composition.machine (Composition.machine copyRef increment) copyArity
noncomputable def machine := Composition.machine rewind copies

def input (arity output B : ℕ) (graph : List Bool) : Fin 7→List Bool :=
  ![graph,List.replicate output true,unary B arity,List.replicate B false,
    List.replicate B true,List.replicate B false,[]]
def copied (arity output B : ℕ) (graph : List Bool) : Fin 7→List Bool :=
  ![graph,List.replicate output true,unary B arity,unary B output,
    List.replicate B true,List.replicate B false,[]]
def incremented (arity output B : ℕ) (graph : List Bool) : Fin 7→List Bool :=
  ![graph,List.replicate output true,unary B arity,unary B (output+1),
    List.replicate B true,List.replicate B false,[]]
noncomputable def result (arity output B : ℕ) (graph : List Bool) : Fin 7→List Bool :=
  install copyAritySlots (incremented arity output B graph)
    ![unary B arity,List.replicate arity true,List.replicate B false]
def heads (graph : List Bool) : Fin 7→ℕ := ![graph.length,0,0,0,0,0,0]
def budget (arity output B : ℕ) := 2*B+4*output+2*arity+17

theorem copy_ref_ready (arity output B : ℕ) (graph : List Bool) (ho : output+1≤B) :
    ClockJoin.ReadyRun copyRef (2*output+4) (input arity output B graph) (copied arity output B graph) := by
  have base := copy_ready output 0 B B ho
  rw [show unary 0 output=List.replicate output true from ZeroPadding.pad_zero _] at base
  have run := base.focus copyRefSlots (by decide) (input arity output B graph)
    (by intro i;fin_cases i <;> rfl)
  have hi : install copyRefSlots (input arity output B graph)
      ![List.replicate output true,unary B output,List.replicate B false]=copied arity output B graph := by
    funext i;fin_cases i <;> first
      | exact install_slot copyRefSlots (by decide) _ _ 0
      | exact install_slot copyRefSlots (by decide) _ _ 1
      | exact install_slot copyRefSlots (by decide) _ _ 2
      | exact install_other copyRefSlots _ _ _ (by decide)
  rw [hi] at run
  exact run

theorem increment_ref_ready (arity output B : ℕ) (graph : List Bool) (ho : output+1≤B) :
    ClockJoin.ReadyRun increment (2*output+4) (copied arity output B graph) (incremented arity output B graph) := by
  have run := (increment_ready output B ho).focus incrementSlots (by decide) (copied arity output B graph)
    (by intro i;fin_cases i <;> rfl)
  have hi : install incrementSlots (copied arity output B graph)
      ![unary B (output+1),List.replicate B false]=incremented arity output B graph := by
    funext i;fin_cases i <;> first
      | exact install_slot incrementSlots (by decide) _ _ 0
      | exact install_slot incrementSlots (by decide) _ _ 1
      | exact install_other incrementSlots _ _ _ (by decide)
  rw [hi] at run
  exact run

theorem copy_arity_ready (arity output B : ℕ) (graph : List Bool) (ha : arity+1≤B) :
    ClockJoin.ReadyRun copyArity (2*arity+4) (incremented arity output B graph) (result arity output B graph) := by
  have base := copy_ready arity B 0 B ha
  rw [show unary 0 arity=List.replicate arity true from ZeroPadding.pad_zero _] at base
  have run := base.focus copyAritySlots copyArity_injective (incremented arity output B graph)
    (by intro i;fin_cases i <;> rfl)
  exact run

theorem result_copied (arity output B : ℕ) (graph : List Bool) (j : Fin 3) :
    result arity output B graph (copyAritySlots j)=
      (![unary B arity,List.replicate arity true,List.replicate B false] : Fin 3→List Bool) j :=
  install_slot copyAritySlots copyArity_injective _ _ j

theorem result_retained (arity output B : ℕ) (graph : List Bool) (i : Fin 7)
    (hi : ∀ j,copyAritySlots j≠i) :
    result arity output B graph i=incremented arity output B graph i :=
  install_other copyAritySlots _ _ i hi

theorem copies_ready (arity output B : ℕ) (graph : List Bool) (ho : output+1≤B) (ha : arity+1≤B) :
    ClockJoin.ReadyRun copies (4*output+2*arity+14) (input arity output B graph) (result arity output B graph) := by
  have whole := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (copy_ref_ready arity output B graph ho)
      (increment_ref_ready arity output B graph ho)) (copy_arity_ready arity output B graph ha)
  have hc : ((2*output+4)+1+(2*output+4))+1+(2*arity+4)=4*output+2*arity+14 := by omega
  rw [hc] at whole
  exact whole

theorem rewind_run (arity output B : ℕ) (graph : List Bool) (hg : graph.length≤B) :
    ∃ r,runFrom rewind (2*B+2) ⟨rewind.start,heads graph,input arity output B graph⟩=some r ∧
      r.final.heads=(fun _=>0) ∧ r.final.tapes=input arity output B graph ∧ r.steps=2*B+2 := by
  obtain ⟨p,hp,ps,pf⟩ := RecoveryBoundedQueryRewind.padded_run graph B graph.length hg
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩ := RecoveryFocus.dock rewindSlots (by decide)
    CompetitorRecordRewind.machine _ (heads graph) (input arity output B graph)
    (RecoveryBoundedQueryRewind.padded 0 graph graph.length B)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl) p hp
  refine ⟨r,hr,?_,?_,rs.trans ps⟩
  · funext i;fin_cases i <;> first
      | exact (rh 0).trans (by rw [pf];rfl)
      | exact (rh 1).trans (by rw [pf];rfl)
      | exact (rh 2).trans (by rw [pf];rfl)
      | exact (rkeep _ (by decide)).1
  · funext i;fin_cases i <;> first
      | exact (rt 0).trans (by rw [pf];rfl)
      | exact (rt 1).trans (by rw [pf];rfl)
      | exact (rt 2).trans (by rw [pf];rfl)
      | exact (rkeep _ (by decide)).2

theorem prepare_run (arity output B : ℕ) (graph : List Bool)
    (hg : graph.length≤B) (ho : output+1≤B) (ha : arity+1≤B) :
    ∃ r,runFrom machine (budget arity output B) ⟨machine.start,heads graph,input arity output B graph⟩=some r ∧
      r.final.heads=(fun _=>0) ∧ r.final.tapes=result arity output B graph ∧ r.steps≤budget arity output B := by
  obtain ⟨p,hp,ph,pt,ps⟩ := rewind_run arity output B graph hg
  obtain ⟨q,hq,qt,qh,qs⟩ := copies_ready arity output B graph ho ha
  have entry : Composition.restart p.final copies.start=initialConfiguration copies (input arity output B graph) := by
    apply configuration_ext
    · rfl
    · exact ph
    · exact pt
  change runFrom copies (4*output+2*arity+14) (initialConfiguration copies (input arity output B graph))=some q at hq
  rw [←entry] at hq
  have whole := Composition.run_join rewind copies _ _ _ p q hp hq
  have hc : (2*B+2)+1+(4*output+2*arity+14)=budget arity output B := by unfold budget;omega
  rw [hc] at whole
  refine ⟨Composition.joinedReceipt p q,whole,funext qh,qt,?_⟩
  change p.steps+1+q.steps≤budget arity output B
  unfold budget
  omega

theorem budget_le (arity output B : ℕ) (ho : output+1≤B) (ha : arity+1≤B) :
    budget arity output B≤16*(B+2) := by unfold budget;omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerializePrepare
