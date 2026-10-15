import Proof.PCP.VerifierDecodingSequentialRecord

/-! Exact record positions in the executed counted table scan, including
canonical rows with an arbitrary subsequent suffix. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Sequential
open LocalBitMultitape VerifierEncoding RepairOrdinary SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem records_tests_iff (bound : List Bool) (t n : ℕ) (bits : List Bool) :
    RecordsMachine.tests bound t n bits=true ↔
      ∀ i : Fin n,RecordMachine.recordValid (bits.drop (i.val*RecordsMachine.width bound t)) bound t=true := by
  induction n generalizing bits with
  | zero => simp [RecordsMachine.tests]
  | succ n ih =>
    rw [RecordsMachine.tests,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨hfirst,htail⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hfirst
      · have hj := htail j
        rw [List.drop_drop] at hj
        have he : RecordsMachine.width bound t+j.val*RecordsMachine.width bound t=
            j.succ.val*RecordsMachine.width bound t := by simp only [Fin.val_succ]; ring
        rw [he] at hj
        exact hj
    · intro hall
      refine ⟨by simpa using hall 0,?_⟩
      intro i
      rw [List.drop_drop]
      have he : RecordsMachine.width bound t+i.val*RecordsMachine.width bound t=
          i.succ.val*RecordsMachine.width bound t := by simp only [Fin.val_succ]; ring
      rw [he]
      exact hall i.succ

theorem records_tests_add (bound : List Bool) (t a b : ℕ) (bits : List Bool) :
    RecordsMachine.tests bound t (a+b) bits=
      (RecordsMachine.tests bound t a bits &&
        RecordsMachine.tests bound t b (bits.drop (RecordsMachine.width bound t*a))) := by
  induction a generalizing bits with
  | zero => simp [RecordsMachine.tests]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega,RecordsMachine.tests,ih,RecordsMachine.tests]
    simp only [List.drop_drop,Bool.and_assoc]
    have he : RecordsMachine.width bound t+RecordsMachine.width bound t*a=RecordsMachine.width bound t*(a+1) := by ring
    rw [he]

theorem encoded_records_test {t s n : ℕ} (j : ℕ) (actions : Fin n → Option (Action t s))
    (tail : List Bool) (hs : s<2^j) :
    RecordsMachine.tests (binary j s) t n ((List.ofFn fun i => actionCode j (actions i)).flatten++tail)=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.flatten_cons,List.append_assoc,RecordsMachine.tests]
    rw [encoded_record_valid j (actions 0) _ hs,Bool.true_and]
    have hwidth : RecordsMachine.width (binary j s) t=(actionCode j (actions 0)).length := by
      simp [RecordsMachine.width]
    rw [hwidth,List.drop_left]
    exact ih (fun i => actions i.succ)

theorem encoded_grid_test {t s rows cols : ℕ} (j : ℕ)
    (actions : Fin rows → Fin cols → Option (Action t s)) (tail : List Bool) (hs : s<2^j) :
    RecordsMachine.tests (binary j s) t (rows*cols)
      ((List.ofFn fun row => (List.ofFn fun col => actionCode j (actions row col)).flatten).flatten++tail)=true := by
  induction rows with
  | zero => simp [RecordsMachine.tests]
  | succ rows ih =>
    rw [List.ofFn_succ,List.flatten_cons,List.append_assoc,show (rows+1)*cols=cols+rows*cols by ring]
    rw [records_tests_add,encoded_records_test j (actions 0) _ hs,Bool.true_and]
    have hlen : RecordsMachine.width (binary j s) t*cols=
        (List.ofFn fun col => actionCode j (actions 0 col)).flatten.length := by
      rw [flat_ofFn_length _ (fun i => actionCode_length j (actions 0 i))]
      simp only [RecordsMachine.width,binary_length]
      ring
    rw [hlen,List.drop_left]
    exact ih (fun row => actions row.succ)

theorem table_tests_encoded (v : OrdinaryVerifier) :
    TableValidation.valid (binary (natBitLength v.stateCount) v.stateCount)
      v.tapeCount (v.stateCount*2^v.tapeCount) (table v)=true := by
  have ht := encoded_grid_test (natBitLength v.stateCount)
    (fun (q : Fin v.stateCount) (mask : Fin (2^v.tapeCount)) =>
      v.machine.rule q (fun i => mask.val.testBit i.val)) []
    (Nat.lt_pow_succ_log_self (by decide) v.stateCount)
  simp only [List.append_nil] at ht
  have hl : RecordsMachine.width (binary (natBitLength v.stateCount) v.stateCount) v.tapeCount*
      (v.stateCount*2^v.tapeCount)=(table v).length := by
    rw [table_length]
    simp only [RecordsMachine.width,binary_length,entryWidth]
    ring
  simp only [TableValidation.valid,Bool.and_eq_true]
  exact ⟨ht,decide_eq_true hl⟩

end NearCubicWires.RepairSource.VerifierDecoding.Sequential
