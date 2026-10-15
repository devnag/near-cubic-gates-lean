import Proof.PCP.PCPTripleLoop

/-! Cold allocation for the repeated serializer: print its fixed triple
count, advance that sentinel once, and physically erase/allocate its bank.
Only the source, append stream and actual outside capacity arrive as data. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleStart
open LocalBitMultitape RecoveryExecution RecoveryRootRound PCPSerializerReuse
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputTapes (capacity : ℕ) (source out : List Bool) (i : Fin 132) : List Bool :=
  if i=0 then source else if i=129 then out else if i=130 then List.replicate capacity true else []
def inputHeads (pos appendPos : ℕ) (i : Fin 132) : ℕ :=
  if i=2 then 0 else bodyHeads pos appendPos i
def slots : Fin 2 → Fin 132 := ![2,1]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def printer := RecoveryFocus.machine slots (HierarchyFixedWord.machine (CompareMachine.word 3))
noncomputable def printed (capacity : ℕ) (source out : List Bool) :=
  install slots (inputTapes capacity source out)
    (![CompareMachine.word 3,List.replicate 4 false] : Fin 2 → List Bool)
def advance : Machine 132 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some
    ⟨1,fun _ => none,fun i => if i=2 then .right else .stay⟩ else none
noncomputable def tail := Composition.machine advance eraseMachine
noncomputable def machine := Composition.machine printer tail
noncomputable def entry (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  (⟨machine.start,inputHeads pos out.length,inputTapes capacity source out⟩ : Configuration 132 _)

theorem printed_count (capacity : ℕ) (source out : List Bool) :
    printed capacity source out 2=CompareMachine.word 3 :=
  install_slot slots slots_injective _ _ 0
theorem printed_log (capacity : ℕ) (source out : List Bool) :
    printed capacity source out 1=List.replicate 4 false :=
  install_slot slots slots_injective _ _ 1
theorem printed_other (capacity : ℕ) (source out : List Bool) (i : Fin 132)
    (h1 : i≠1) (h2 : i≠2) : printed capacity source out i=inputTapes capacity source out i := by
  apply install_other
  intro j
  fin_cases j
  · exact Ne.symm h2
  · exact Ne.symm h1

theorem print_run (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :
    ∃ r,runFrom printer 10 ⟨printer.start,inputHeads pos out.length,inputTapes capacity source out⟩=some r ∧
      r.final.heads=inputHeads pos out.length ∧ r.final.tapes=printed capacity source out ∧ r.steps=10 := by
  have h := (HierarchyFixedWord.word_ready (CompareMachine.word 3)).focus_at slots slots_injective
    (inputHeads pos out.length) (inputTapes capacity source out)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  exact h

theorem advance_run (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :
    ∃ r,runFrom advance 1 ⟨0,inputHeads pos out.length,printed capacity source out⟩=some r ∧
      r.final=⟨1,bodyHeads pos out.length,printed capacity source out⟩ ∧ r.steps=1 := by
  have h : step advance ⟨0,inputHeads pos out.length,printed capacity source out⟩=
      some ⟨1,bodyHeads pos out.length,printed capacity source out⟩ := by
    simp only [step,advance,Fin.val_zero,ite_true,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=2
      · subst i; rfl
      · simp only [applyAction,inputHeads,hi,ite_false,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem printed_scratch (capacity : ℕ) (source out : List Bool) (hcap : 4 ≤ capacity)
    (j : Fin 127) : (printed capacity source out (scratchSlots j)).length ≤ capacity := by
  by_cases hj : scratchSlots j=1
  · rw [hj,printed_log,List.length_replicate]
    exact hcap
  rw [printed_other capacity source out _ hj (scratch_not_live j).2]
  have hblank : inputTapes capacity source out (scratchSlots j)=[] := by
    fin_cases j <;> rfl
  rw [hblank]
  exact Nat.zero_le _

theorem erase_prepared_run (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool)
    (hcap : 4 ≤ capacity) :
    ∃ r,runFrom eraseMachine (2*capacity+4)
      ⟨eraseMachine.start,bodyHeads pos out.length,printed capacity source out⟩=some r ∧
      r.final.heads=(bodyEntry capacity (capacity+1) source pos 3 out).heads ∧
      r.final.tapes=(bodyEntry capacity (capacity+1) source pos 3 out).tapes ∧ r.steps=2*capacity+4 := by
  have h0 : printed capacity source out 0=source := by
    rw [printed_other capacity source out 0 (by decide) (by decide)]
    rfl
  have ho : printed capacity source out 129=out := by
    rw [printed_other capacity source out 129 (by decide) (by decide)]
    rfl
  have hd : printed capacity source out 130=List.replicate capacity true := by
    rw [printed_other capacity source out 130 (by decide) (by decide)]
    rfl
  have hl : printed capacity source out 131=List.replicate 0 false := by
    rw [printed_other capacity source out 131 (by decide) (by decide)]
    rfl
  obtain ⟨r,hr,rh,rt,rs⟩ := erase_run capacity 0 (bodyHeads pos out.length)
    (printed capacity source out) (printed_scratch capacity source out hcap) hd hl
    (by intro j; fin_cases j <;> rfl) (by rfl) (by rfl)
  have result : Result capacity 0 pos 3 source out r.final := by
    refine ⟨rh,?_,?_,?_,?_,?_,?_⟩
    · rw [rt,erased_live capacity 0 _ 0 (Or.inl rfl)]
      exact h0
    · rw [rt,erased_live capacity 0 _ 2 (Or.inr (Or.inl rfl))]
      exact printed_count capacity source out
    · rw [rt,erased_live capacity 0 _ 129 (Or.inr (Or.inr rfl))]
      exact ho
    · rw [rt]; exact erased_driver capacity 0 _
    · rw [rt]; exact erased_log capacity 0 _
    · intro j; rw [rt]; exact erased_slot capacity 0 _ j
  refine ⟨r,hr,?_,?_,rs⟩
  · rw [bodyEntry_heads]
    exact rh
  · rw [bodyEntry_tapes]
    simpa only [Nat.zero_max] using result.tapes_eq

theorem start_run (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool)
    (hcap : 4 ≤ capacity) :
    ∃ r,runFrom machine (2*capacity+17) (entry capacity source pos out)=some r ∧
      r.final.heads=(bodyEntry capacity (capacity+1) source pos 3 out).heads ∧
      r.final.tapes=(bodyEntry capacity (capacity+1) source pos 3 out).tapes ∧ r.steps=2*capacity+17 := by
  obtain ⟨p,hp,ph,pt,ps⟩ := print_run capacity source pos out
  obtain ⟨a,ha,af,as⟩ := advance_run capacity source pos out
  obtain ⟨e,he,eh,et,es⟩ := erase_prepared_run capacity source pos out hcap
  have hae : runFrom eraseMachine (2*capacity+4) (Composition.restart a.final eraseMachine.start)=some e := by
    rw [af]
    exact he
  have hat := Composition.run_join advance eraseMachine _ _ _ a e ha hae
  have hid : Composition.leftConfig _
      (⟨0,inputHeads pos out.length,printed capacity source out⟩ : Configuration 132 2)=
      Composition.restart p.final tail.start := by
    apply configuration_ext
    · rfl
    · exact ph.symm
    · exact pt.symm
  rw [hid] at hat
  have hall := Composition.run_join printer tail _ _ _ p (Composition.joinedReceipt a e) hp hat
  have htime : 10+1+(1+1+(2*capacity+4))=2*capacity+17 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt p (Composition.joinedReceipt a e),hall,eh,et,?_⟩
  change p.steps+1+(a.steps+1+e.steps)=_
  rw [ps,as,es]
  exact htime

end NearCubicWires.RepairOrdinary.PCPTripleStart
