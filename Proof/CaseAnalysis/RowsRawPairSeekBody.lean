import Proof.CaseAnalysis.RowsRawAtomSeek

/-! The A.2 source cache is ordered X,C at each occurrence. One original
occurrence index advances over these two existing cache entries together;
no doubled index word or second cache is manufactured. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawAtomSeek (heads data advance advance_run skip skip_run)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Pair:=List (List ℕ)×List (List ℕ)
def word (p : Pair):=ExtIncidence.stream p.1++ExtIncidence.stream p.2
def cacheWord (ps : List Pair):=ps.flatMap word
noncomputable def skipPair:=Composition.machine skip skip
noncomputable def body:=Composition.machine skipPair advance

theorem skip_pair_run (ip : ℕ) (index pre tail : List Bool) (p : Pair) :
    Step skipPair ((word p).length+1) (heads ip pre.length)
      (data index (pre++word p++tail))
      (heads ip (pre.length+(word p).length)) (data index (pre++word p++tail)) := by
  have first:=skip_run ip index pre (ExtIncidence.stream p.2++tail) p.1
  have last:=skip_run ip index (pre++ExtIncidence.stream p.1) tail p.2
  simp only [List.length_append,List.append_assoc] at first last
  have all:=first.seq last
  have time:(ExtIncidence.stream p.1).length+1+(ExtIncidence.stream p.2).length=
      (word p).length+1:=by simp only [word,List.length_append];omega
  rw [time] at all
  simpa only [skipPair,word,List.length_append,List.append_assoc,Nat.add_assoc] using all

theorem body_run (ip : ℕ) (index pre tail : List Bool) (p : Pair) :
    Step body ((word p).length+3) (heads ip pre.length)
      (data index (pre++word p++tail))
      (heads (ip+1) (pre.length+(word p).length)) (data index (pre++word p++tail)) := by
  have first:=skip_pair_run ip index pre tail p
  have last:=advance_run ip (pre.length+(word p).length) index (pre++word p++tail)
  simpa only [body,Nat.add_assoc] using first.seq last

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek
