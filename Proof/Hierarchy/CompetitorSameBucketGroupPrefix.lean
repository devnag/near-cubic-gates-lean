import Proof.Hierarchy.CompetitorSameBucketGroupTail

/-! Actual read/comparison/conditional-flush prefix of one signed record.
The branch is the physically computed equality of both cell identifiers. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tested (s : Store) (p m : ℕ) (e : Entry) : Store :=
  if s.present then compared (marked (loaded s p m e) true) else loaded s p m e
def changed (s : Store) (m : ℕ) (e : Entry) : Bool :=
  s.present && !decide (s.current=e.ids m)
def prepared (s : Store) (p m : ℕ) (e : Entry) : Store :=
  if changed s m e then emitted (tested s p m e) else tested s p m e
def prefixOutput (s : Store) (w m : ℕ) (e : Entry) (out : List Bool) : List Bool :=
  if changed s m e then out++pair w s else out

theorem record_marker (pre suffix : List Bool) (p m : ℕ) (e : Entry) :
    readTapeBit (pre++StablePartition.recordBits (e.record p m)++suffix) pre.length=true := by
  rw [← CompetitorSameBucketGroupRead.entry_word]
  simp only [CompetitorSameBucketGroupRead.word,List.append_assoc,List.cons_append,List.nil_append]
  exact Streaming.read_append _ _ _

theorem prefix_run (s : Store) (cap w p m : ℕ) (pre suffix out : List Bool) (e : Entry)
    (hm : s.magnitude.length≤p) (hi : s.ids.length≤2*m)
    (hcur : s.present=true → s.current.length=2*m) (hc : 8*m+3≤cap) (ha : 4*w+3≤cap) :
    ∃ time≤4*p+16*m+24*w+47,
      Timed machine time
        (boundary 0 cap w p m pre.length (pre++StablePartition.recordBits (e.record p m)++suffix) out s)
        (boundary 5 cap w p m (pre.length+2*p+4*m+5)
          (pre++StablePartition.recordBits (e.record p m)++suffix)
          (prefixOutput s w m e out) (prepared s p m e)) := by
  let source := pre++StablePartition.recordBits (e.record p m)++suffix
  let pos := pre.length+2*p+4*m+5
  have hprobe := probe_call 1 cap w p m pre.length source out s (by
    change (if readTapeBit source pre.length then some (1 : Fin 10) else
      if s.present then some 9 else none)=some 1
    rw [show readTapeBit source pre.length=true from record_marker pre suffix p m e]
    rfl)
  cases hp : s.present
  · have hr := call_run 1 5 (4*p+8*m+12) cap w p m pre.length pos source out out s (loaded s p m e)
      (read_run s cap w p m pre suffix out e hm hi) (by
        intro q
        simp only [next,readBits_present,loaded,hp]
        rfl)
    refine ⟨1+(4*p+8*m+12+1),by omega,?_⟩
    simpa [prefixOutput,prepared,tested,changed,hp,source,pos] using hprobe.trans hr
  · have hr := call_run 1 2 (4*p+8*m+12) cap w p m pre.length pos source out out s (loaded s p m e)
      (read_run s cap w p m pre suffix out e hm hi) (by
        intro q
        simp only [next,readBits_present,loaded,hp]
        rfl)
    have hm' := call_run 2 3 1 cap w p m pos pos source out out
      (loaded s p m e) (marked (loaded s p m e) true)
      (mark_run true (loaded s p m e) cap w p m pos source out) (by intro q; rfl)
    have hbefore := (hprobe.trans hr).trans hm'
    have hcompare := compare_run (marked (loaded s p m e) true) cap w p m pos source out
      (hcur hp) (ids_length m e) (by omega)
    by_cases he : s.current=e.ids m
    · have hcmp := call_run 3 5 (8*m+4) cap w p m pos pos source out out
        (marked (loaded s p m e) true) (compared (marked (loaded s p m e) true)) hcompare (by
          intro q
          simp [next,readBits_same,compared,marked,loaded,he])
      refine ⟨((1+(4*p+8*m+12+1))+(1+1))+(8*m+4+1),by omega,?_⟩
      simpa [prefixOutput,prepared,tested,changed,hp,he,source,pos] using hbefore.trans hcmp
    · have hcmp := call_run 3 4 (8*m+4) cap w p m pos pos source out out
        (marked (loaded s p m e) true) (compared (marked (loaded s p m e) true)) hcompare (by
          intro q
          simp [next,readBits_same,compared,marked,loaded,he])
      have hem := call_run 4 5 (24*w+25) cap w p m pos pos source out
        (out++pair w (compared (marked (loaded s p m e) true)))
        (compared (marked (loaded s p m e) true)) (emitted (compared (marked (loaded s p m e) true)))
        (emit_run _ cap w p m pos source out ha) (by intro q; rfl)
      refine ⟨(((1+(4*p+8*m+12+1))+(1+1))+(8*m+4+1))+(24*w+25+1),by omega,?_⟩
      simpa [prefixOutput,prepared,tested,changed,hp,he,pair,compared,marked,loaded,source,pos] using
        (hbefore.trans hcmp).trans hem

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
