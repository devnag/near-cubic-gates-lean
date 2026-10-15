import Proof.Packets.PacketsXWalkSampleWord

/-! Paid walk iterations use consecutive literal 160-bit chunks. These list
identities expose every iteration's actual prefix and suffix of the frozen word. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptList
open NearCubicWires NearCubicWires.SupplierWalk

def prefixBits {n : Nat} (labels : Fin n→PoweredMargulisLabel) (i : Nat):=
  ((List.ofFn labels).take i).flatMap WalkPoweredWord.word
def suffix {n : Nat} (labels : Fin n→PoweredMargulisLabel) (i : Nat):=
  ((List.ofFn labels).drop i).flatMap WalkPoweredWord.word

theorem words_eq {n : Nat} (labels : Fin n→PoweredMargulisLabel) :
    WalkSampleWord.labelsWord labels=(List.ofFn labels).flatMap WalkPoweredWord.word := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [WalkSampleWord.labelsWord,List.ofFn_succ,List.flatMap_cons,ih]
    rfl

theorem flat_length (labels : List PoweredMargulisLabel) :
    (labels.flatMap WalkPoweredWord.word).length=160*labels.length := by
  induction labels with
  | nil=>rfl
  | cons label labels ih=>
    rw [List.flatMap_cons,List.length_append,WalkPoweredWord.length,ih,List.length_cons]
    omega

theorem prefix_length {n : Nat} (labels : Fin n→PoweredMargulisLabel) (i : Nat) :
    (prefixBits labels i).length=160*min i n := by
  rw [prefixBits,flat_length,List.length_take,List.length_ofFn]

theorem complete {n : Nat} (labels : Fin n→PoweredMargulisLabel) :
    prefixBits labels n=WalkSampleWord.labelsWord labels := by
  rw [words_eq,prefixBits,List.take_of_length_le (by simp)]

theorem split {n : Nat} (labels : Fin n→PoweredMargulisLabel) (i : Nat) (hi : i<n) :
    WalkSampleWord.labelsWord labels=prefixBits labels i++WalkPoweredWord.word (labels ⟨i,hi⟩)++suffix labels (i+1) := by
  have hh : i<(List.ofFn labels).length := by simpa using hi
  have h : (List.ofFn labels).take i++[(List.ofFn labels)[i]]++(List.ofFn labels).drop (i+1)=List.ofFn labels := by
    rw [←List.take_succ_eq_append_getElem hh,List.take_append_drop]
  have hmap:=congrArg (fun xs : List PoweredMargulisLabel=>xs.flatMap WalkPoweredWord.word) h
  simpa only [words_eq,prefixBits,suffix,List.flatMap_append,List.flatMap_singleton,List.getElem_ofFn] using hmap.symm

end Theorem25Completion.WalkTranscriptList
