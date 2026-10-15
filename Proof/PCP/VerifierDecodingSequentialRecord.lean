import Proof.PCP.VerifierDecodingSequentialTags

/-! Every successful sequential record test reconstructs exactly the
canonical action code, and every encoded action passes the same test. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Sequential
open LocalBitMultitape VerifierEncoding RepairOrdinary SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem record_reencode {t s : ℕ} (j : ℕ) (bits : List Bool) (hs : s<2^j)
    (hv : RecordMachine.recordValid bits (binary j s) t=true) :
    actionCode j (decodeAction (t:=t) (s:=s) j bits)=bits.take (1+j+4*t) := by
  cases bits with
  | nil => simp [RecordMachine.recordValid] at hv
  | cons present rest =>
    cases present with
    | false =>
      simp only [RecordMachine.recordValid,Bool.false_eq_true,↓reduceIte,RecordMachine.absentValid,
        binary_length,Bool.and_eq_true,decide_eq_true_eq] at hv
      have htags := absent_tags_reencode t (rest.drop j) hv.2
      simp only [decodeAction,List.headD_cons,Bool.false_eq_true,↓reduceIte,actionCode]
      rw [show 1+j+4*t=(j+4*t)+1 by omega,List.take_succ_cons,List.take_add,hv.1.2,htags]
      simp only [List.replicate_add]
    | true =>
      simp only [RecordMachine.recordValid,↓reduceIte,RecordMachine.presentValid,Bool.and_eq_true,
        decide_eq_true_eq,RecordMachine.rangeValid,binary_length,binary_value _ _ hs] at hv
      have htags := present_tags_reencode t (rest.drop j) hv.2
      have hfield : fixedBits j (value (rest.take j))=rest.take j := by
        rw [fixedBits_binary]
        have he := binary_value_word (rest.take j)
        simpa only [List.length_take,Nat.min_eq_left hv.1.1] using he
      let a : Action t s :=
        ⟨⟨value (rest.take j),hv.1.2⟩,
          fun i => decodeWrite ((slice (rest.drop j) (i.val*4) 4).take 2),
          fun i => decodeMove ((slice (rest.drop j) (i.val*4) 4).drop 2)⟩
      have hd : decodeAction j (true::rest)=some a := by
        simp [decodeAction,slice,a,hv.1.2,Nat.add_comm 1 j]
      rw [hd]
      change true::(fixedBits j (value (rest.take j))++
        (List.ofFn fun i : Fin t => tagCode (slice (rest.drop j) (i.val*4) 4)).flatten)=_
      rw [hfield,htags,show 1+j+4*t=(j+4*t)+1 by omega,List.take_succ_cons,List.take_add]

theorem record_prefix_reencode {t s : ℕ} (j : ℕ) (bits : List Bool) (hs : s<2^j)
    (hv : RecordMachine.recordValid bits (binary j s) t=true) :
    actionCode j (decodeAction (t:=t) (s:=s) j (bits.take (1+j+4*t)))=bits.take (1+j+4*t) := by
  have he := record_reencode j bits hs hv
  rw [←he,decodeAction_code j hs.le]

theorem encoded_record_valid {t s : ℕ} (j : ℕ) (a : Option (Action t s)) (tail : List Bool) (hs : s<2^j) :
    RecordMachine.recordValid (actionCode j a++tail) (binary j s) t=true := by
  cases a with
  | none =>
    have htags := zero_tags_test t tail
    have hj : j≤(List.replicate (j+4*t) false++tail).length := by simp; omega
    have htake : (List.replicate (j+4*t) false++tail).take j=List.replicate j false := by
      rw [List.replicate_add, List.append_assoc]
      simp
    have hdrop : (List.replicate (j+4*t) false++tail).drop j=List.replicate (4*t) false++tail := by
      rw [List.replicate_add,List.append_assoc]
      simp
    simp only [actionCode,List.cons_append,RecordMachine.recordValid,Bool.false_eq_true,↓reduceIte,
      RecordMachine.absentValid,binary_length,hj,htake,and_self,decide_true,Bool.true_and,hdrop,htags]
  | some a =>
    let payload := (List.ofFn fun i : Fin t => writeCode (a.write i)++moveCode (a.move i)).flatten
    have htags := encoded_tags_test a.write a.move tail
    have hj : j≤(fixedBits j a.nextControl.val++payload++tail).length := by simp
    have htake : (fixedBits j a.nextControl.val++payload++tail).take j=fixedBits j a.nextControl.val := by
      rw [List.append_assoc]
      simpa only [fixedBits_length] using List.take_left (l₁:=fixedBits j a.nextControl.val) (l₂:=payload++tail)
    have hdrop : (fixedBits j a.nextControl.val++payload++tail).drop j=payload++tail := by
      rw [List.append_assoc]
      simpa only [fixedBits_length] using List.drop_left (l₁:=fixedBits j a.nextControl.val) (l₂:=payload++tail)
    change RecordMachine.presentValid (fixedBits j a.nextControl.val++payload++tail) (binary j s) t=true
    simp only [RecordMachine.presentValid,RecordMachine.rangeValid,binary_length,binary_value _ _ hs,
      hj,htake,fixedBits_value j _ (a.nextControl.isLt.trans hs),a.nextControl.isLt,and_self,
      decide_true,Bool.true_and,hdrop]
    exact htags

end NearCubicWires.RepairSource.VerifierDecoding.Sequential
