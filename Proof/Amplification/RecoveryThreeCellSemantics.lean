import Proof.Amplification.RecoveryThreeCellReader

/-! All-code shape correspondence and the three physically retained literal
codes of the ordinary reader. Natural Boolean tags are checked afterwards. -/
namespace NearCubicWires.RepairOrdinary.RecoveryThreeCellReader
open LocalBitMultitape RecoveryClauseState RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem after_value (s : State) (which : Fin 3) (hz : value s.bits≠0) :
    value (s.after which).bits=(cell (value s.bits)).2 := by
  simp only [State.after,hz,ite_false]
  exact RecoveryRawListStep.list_component false s.bits hz

theorem result_flags (s : State) :
    (endState s).result=true ↔
      (s1 s).flag=true ∧ (s2 s).flag=true ∧ (s3 s).flag=true ∧ (s4 s).flag=false := by
  cases h1 : (s1 s).flag <;> cases h2 : (s2 s).flag <;>
    cases h3 : (s3 s).flag <;> cases h4 : (s4 s).flag <;>
    simp only [endState,h1,h2,h3,h4,Bool.false_eq_true,↓reduceIte] <;>
    simp [s1,s2,s3,s4,s0]

theorem result_inputs (s : State) :
    (endState s).result=true ↔
      value s.bits≠0 ∧ value (s1 s).bits≠0 ∧ value (s2 s).bits≠0 ∧ value (s3 s).bits=0 := by
  rw [result_flags]
  simp only [s1,s2,s3,s4,after_flag,decide_eq_true_eq,decide_eq_false_iff_not,not_not,s0]

theorem result_shape (s : State) : (endState s).result=shapeThree (value s.bits) := by
  apply Bool.eq_iff_iff.mpr
  rw [result_inputs]
  simp only [shapeThree,Bool.and_eq_true,bne_iff_ne,beq_iff_eq,and_assoc]
  constructor
  · rintro ⟨h0,h1,h2,h3⟩
    have hv1 := after_value (s0 s) 0 h0
    have hv2 := after_value (s1 s) 1 h1
    have hv3 := after_value (s2 s) 2 h2
    change value (s1 s).bits=(cell (value s.bits)).2 at hv1
    change value (s2 s).bits=(cell (value (s1 s).bits)).2 at hv2
    change value (s3 s).bits=(cell (value (s2 s).bits)).2 at hv3
    rw [hv1] at h1 hv2
    rw [hv2] at h2 hv3
    rw [hv3] at h3
    exact ⟨h0,h1,h2,h3⟩
  · rintro ⟨h0,h1,h2,h3⟩
    have hv1 := after_value (s0 s) 0 h0
    change value (s1 s).bits=(cell (value s.bits)).2 at hv1
    have hn1 : value (s1 s).bits≠0 := by rwa [hv1]
    have hv2 := after_value (s1 s) 1 hn1
    change value (s2 s).bits=(cell (value (s1 s).bits)).2 at hv2
    rw [hv1] at hv2
    have hn2 : value (s2 s).bits≠0 := by rwa [hv2]
    have hv3 := after_value (s2 s) 2 hn2
    change value (s3 s).bits=(cell (value (s2 s).bits)).2 at hv3
    rw [hv2] at hv3
    exact ⟨h0,hn1,hn2,by rwa [hv3]⟩

def literalWords (s : State) : Fin 3 → List Bool :=
  ![RecoveryCellStore.headWord s.bits,RecoveryCellStore.headWord (s1 s).bits,
    RecoveryCellStore.headWord (s2 s).bits]
def literalCodes (code : Nat) : Fin 3 → Nat :=
  ![(cell code).1,(cell (cell code).2).1,(cell (cell (cell code).2).2).1]

theorem success_fields (s : State) (hs : (endState s).result=true) (i : Fin 3) :
    (endState s).fields i=frame (literalWords s i) := by
  obtain ⟨h0,h1,h2,h3⟩ := (result_inputs s).mp hs
  obtain ⟨hf1,hf2,hf3,hf4⟩ := (result_flags s).mp hs
  have he : (endState s).fields=(s4 s).fields := by simp [endState,hf1,hf2,hf3,hf4]
  have he4 : (s4 s).fields=(s3 s).fields := by simp [s4,State.after,h3]
  have he3 : (s3 s).fields=Function.update (s2 s).fields 2 (frame (RecoveryCellStore.headWord (s2 s).bits)) := by
    simp [s3,State.after,h2]
  have he2 : (s2 s).fields=Function.update (s1 s).fields 1 (frame (RecoveryCellStore.headWord (s1 s).bits)) := by
    simp [s2,State.after,h1]
  have he1 : (s1 s).fields=Function.update s.fields 0 (frame (RecoveryCellStore.headWord s.bits)) := by
    simp [s1,s0,State.after,h0]
  rw [he,he4,he3,he2,he1]
  fin_cases i <;> simp [literalWords]

theorem success_values (s : State) (hs : (endState s).result=true) (i : Fin 3) :
    (literalWords s i).length=s.bits.length ∧
      value (literalWords s i)=literalCodes (value s.bits) i := by
  obtain ⟨h0,h1,h2,_⟩ := (result_inputs s).mp hs
  have hv1 := after_value (s0 s) 0 h0
  change value (s1 s).bits=(cell (value s.bits)).2 at hv1
  have hv2 := after_value (s1 s) 1 h1
  change value (s2 s).bits=(cell (value (s1 s).bits)).2 at hv2
  rw [hv1] at hv2
  have hl1 : (s1 s).bits.length=s.bits.length := after_length (s0 s) 0
  have hl2 : (s2 s).bits.length=s.bits.length := (after_length (s1 s) 1).trans hl1
  fin_cases i
  · exact ⟨RecoveryCellStore.headWord_length s.bits,RecoveryCellStore.head_value s.bits h0⟩
  · refine ⟨(RecoveryCellStore.headWord_length (s1 s).bits).trans hl1,?_⟩
    change value (RecoveryCellStore.headWord (s1 s).bits)=(cell (cell (value s.bits)).2).1
    exact (RecoveryCellStore.head_value (s1 s).bits h1).trans (congrArg (fun n => (cell n).1) hv1)
  · refine ⟨(RecoveryCellStore.headWord_length (s2 s).bits).trans hl2,?_⟩
    change value (RecoveryCellStore.headWord (s2 s).bits)=(cell (cell (cell (value s.bits)).2).2).1
    exact (RecoveryCellStore.head_value (s2 s).bits h2).trans (congrArg (fun n => (cell n).1) hv2)

theorem read_three (s : State) (hv : s.Valid) :
    ∃ receipt : ExecutionReceipt 28 (Fintype.card (RecoveryCalls.Control sizes)),
      run machine (budget s) s.tapes=some receipt ∧
      receipt.final.tapes 27=[shapeThree (value s.bits)] ∧
      (∀ i,receipt.final.heads i=0) ∧
      (shapeThree (value s.bits)=true → ∀ i : Fin 3,
        ∃ word,word.length=s.bits.length ∧ value word=literalCodes (value s.bits) i ∧
          receipt.final.tapes (savedSlot i)=frame word) := by
  obtain ⟨r,hr,ht,hh,_⟩ := reader_ready s hv
  have hm := run_moreFuel machine (time s) (budget s-time s) s.tapes r hr
  rw [Nat.add_sub_of_le (time_bound s)] at hm
  refine ⟨r,hm,?_,hh,?_⟩
  · rw [ht,tapes_result,result_shape]
  · intro hs i
    have he : (endState s).result=true := (result_shape s).trans hs
    have hw := success_values s he i
    refine ⟨literalWords s i,hw.1,hw.2,?_⟩
    rw [ht,tapes_saved]
    exact success_fields s he i

end NearCubicWires.RepairOrdinary.RecoveryThreeCellReader
