import Proof.PCP.VerifierDecodingSequentialChunks

/-! Canonical reconstruction of the tested write/move payload. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Sequential
open LocalBitMultitape VerifierEncoding RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tagCode (bits : List Bool) : List Bool :=
  writeCode (decodeWrite (bits.take 2))++moveCode (decodeMove (bits.drop 2))

theorem extend_tagWord (word : TagMachine.Word) : TagMachine.extend (TagMachine.tagWord word)=word := by
  funext i; fin_cases i <;> rfl

theorem tagWord_extend (bits : List Bool) (h : bits.length=4) : TagMachine.tagWord (TagMachine.extend bits)=bits := by
  have he := TagMachine.prefixWord_extend bits 4 (by omega) (by omega)
  have hp : TagMachine.prefixWord (TagMachine.extend bits) 4=TagMachine.tagWord (TagMachine.extend bits) := by
    simp [TagMachine.prefixWord,TagMachine.tagWord,List.ofFn_succ]
  rw [hp] at he
  simpa only [←h,List.take_length] using he

theorem tag_present_iff (bits : List Bool) (h : bits.length=4) :
    TagMachine.valid true (TagMachine.extend bits)=true ↔ tagCode bits=bits := by
  rw [←tagWord_extend bits h]
  rw [extend_tagWord]
  exact TagMachine.valid_present _

theorem tag_absent_iff (bits : List Bool) (h : bits.length=4) :
    TagMachine.valid false (TagMachine.extend bits)=true ↔ bits=List.replicate 4 false := by
  rw [TagMachine.valid_absent,tagWord_extend bits h]

theorem present_tags_reencode (n : ℕ) (bits : List Bool)
    (h : TagScan.tests 4 (TagMachine.valid true) n bits=true) :
    (List.ofFn fun i : Fin n => tagCode (slice bits (i.val*4) 4)).flatten=bits.take (4*n) := by
  obtain ⟨hlen,hall⟩ := (tag_tests_iff 4 (TagMachine.valid true) n bits).mp h
  simp only [show (4 : Fin 5).val=4 from rfl,TagMachine.received_four] at hall
  have he : (fun i : Fin n => tagCode (slice bits (i.val*4) 4))=
      (fun i : Fin n => slice bits (i.val*4) 4) := by
    funext i
    have ht := hall i
    exact (tag_present_iff _ (slice_length bits _ _ (by dsimp at hlen; omega))).mp ht
  rw [he,flat_slices]
  congr 1
  omega

theorem absent_tags_reencode (n : ℕ) (bits : List Bool)
    (h : TagScan.tests 4 (TagMachine.valid false) n bits=true) :
    bits.take (4*n)=List.replicate (4*n) false := by
  obtain ⟨hlen,hall⟩ := (tag_tests_iff 4 (TagMachine.valid false) n bits).mp h
  simp only [show (4 : Fin 5).val=4 from rfl,TagMachine.received_four] at hall
  have he : (fun i : Fin n => slice bits (i.val*4) 4)=fun _ : Fin n => List.replicate 4 false := by
    funext i
    have ht := hall i
    exact (tag_absent_iff _ (slice_length bits _ _ (by dsimp at hlen; omega))).mp ht
  rw [show 4*n=n*4 by omega,←flat_slices,he]
  simp only [List.ofFn_const,List.flatten_replicate_replicate]

theorem slice_append_left (pre tail : List Bool) (a w : ℕ) (h : a+w≤pre.length) :
    slice (pre++tail) a w=slice pre a w := by
  simp only [slice,List.drop_append]
  rw [Nat.sub_eq_zero_of_le (by omega : a≤pre.length),List.drop_zero]
  exact List.take_append_of_le_length (by simp only [List.length_drop]; omega)

theorem canonical_tags_valid (write : Option Bool) (move : HeadMove) :
    TagMachine.valid true (TagMachine.extend (writeCode write++moveCode move))=true := by
  cases write with
  | none => cases move <;> rfl
  | some b => cases b <;> cases move <;> rfl

theorem encoded_tags_test {n : ℕ} (writes : Fin n → Option Bool) (moves : Fin n → HeadMove) (tail : List Bool) :
    TagScan.tests 4 (TagMachine.valid true) n
      ((List.ofFn fun i => writeCode (writes i)++moveCode (moves i)).flatten++tail)=true := by
  let payload := (List.ofFn fun i => writeCode (writes i)++moveCode (moves i)).flatten
  have hlen : payload.length=n*4 := flat_ofFn_length _ (by intro i; simp)
  apply (tag_tests_iff _ _ _ _).mpr
  simp only [show (4 : Fin 5).val=4 from rfl]
  refine ⟨by change 4*n≤(payload++tail).length; rw [List.length_append,hlen]; omega,?_⟩
  intro i
  rw [TagMachine.received_four]
  change TagMachine.valid true (TagMachine.extend (slice (payload++tail) (i.val*4) 4))=true
  rw [slice_append_left payload tail _ _ (by rw [hlen]; omega)]
  have he := slice_flat (width:=4) (fun i => writeCode (writes i)++moveCode (moves i)) (by intro i; simp) i
  rw [he]
  exact canonical_tags_valid _ _

theorem zero_tags_test (n : ℕ) (tail : List Bool) :
    TagScan.tests 4 (TagMachine.valid false) n (List.replicate (4*n) false++tail)=true := by
  apply (tag_tests_iff _ _ _ _).mpr
  refine ⟨by simp,?_⟩
  intro i
  simp only [show (4 : Fin 5).val=4 from rfl,TagMachine.received_four]
  rw [slice_append_left _ tail _ _ (by simp; omega)]
  have he : slice (List.replicate (4*n) false) (i.val*4) 4=List.replicate 4 false := by
    simp only [slice,List.drop_replicate,List.take_replicate]
    congr 1
    omega
  rw [he]
  rfl

end NearCubicWires.RepairSource.VerifierDecoding.Sequential
