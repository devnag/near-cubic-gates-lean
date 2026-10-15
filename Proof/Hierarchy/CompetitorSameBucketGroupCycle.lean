import Proof.Hierarchy.CompetitorSameBucketGroupPrefix

/-! One complete record cycle and the final flush of the SAME grouping
machine, with all controller calls charged and all actual cursors retained. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Valid (p m : ℕ) (s : Store) : Prop :=
  s.magnitude.length≤p ∧ s.ids.length≤2*m ∧ s.current.length≤2*m ∧
    (s.present=true → s.current.length=2*m)
def stepStore (s : Store) (p m : ℕ) (e : Entry) := added (prepared s p m e)
def Fits (w p m : ℕ) (s : Store) (e : Entry) : Prop :=
  value (binary p e.coefficient.natAbs)+selected (prepared s p m e) (decide (e.coefficient<0))<2^w
def cycleBound (cap w p m : ℕ) := 2*cap+40*w+4*p+32*m+82

theorem prepared_fields (s : Store) (p m : ℕ) (e : Entry) :
    (prepared s p m e).magnitude=binary p e.coefficient.natAbs ∧
    (prepared s p m e).ids=e.ids m ∧ (prepared s p m e).current=s.current ∧
    (prepared s p m e).sign=decide (e.coefficient<0) := by
  unfold prepared
  split <;> unfold tested <;> split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem stepStore_fields (s : Store) (p m : ℕ) (e : Entry) :
    (stepStore s p m e).magnitude=binary p e.coefficient.natAbs ∧
    (stepStore s p m e).ids=e.ids m ∧ (stepStore s p m e).current=e.ids m ∧
    (stepStore s p m e).present=true := by
  obtain ⟨hm,hi,_,_⟩ := prepared_fields s p m e
  unfold stepStore added accumulated
  split <;> simp only [marked,copied,Bool.false_eq_true,↓reduceIte] <;>
    exact ⟨hm,hi,hi,True.intro⟩

theorem stepStore_valid (s : Store) (p m : ℕ) (e : Entry) : Valid p m (stepStore s p m e) := by
  obtain ⟨hm,hi,hcur,_⟩ := stepStore_fields s p m e
  simp only [Valid,hm,hi,hcur,binary_length,ids_length,le_refl,implies_true,and_self]

theorem cycle_run (s : Store) (cap w p m : ℕ) (pre suffix out : List Bool) (e : Entry)
    (hv : Valid p m s) (hpw : p≤w) (hc : 8*m+3≤cap) (ha : 4*w+3≤cap)
    (hfit : Fits w p m s e) :
    ∃ time≤cycleBound cap w p m,
      Timed machine time
        (boundary 0 cap w p m pre.length (pre++StablePartition.recordBits (e.record p m)++suffix) out s)
        (boundary 0 cap w p m (pre.length+2*p+4*m+5)
          (pre++StablePartition.recordBits (e.record p m)++suffix)
          (prefixOutput s w m e out) (stepStore s p m e)) := by
  obtain ⟨n,hn,hpre⟩ := prefix_run s cap w p m pre suffix out e hv.1 hv.2.1 hv.2.2.2 hc ha
  obtain ⟨hm,hi,hcur,hsign⟩ := prepared_fields s p m e
  have htail := tail_run (prepared s p m e) cap w p m (pre.length+2*p+4*m+5)
    (pre++StablePartition.recordBits (e.record p m)++suffix) (prefixOutput s w m e out)
    (by rw [hi,ids_length]) (by rw [hcur];exact hv.2.2.1) hc
    (by rw [hm,binary_length];exact hpw) ha (by simpa only [Fits,hm,hsign] using hfit)
  refine ⟨n+(2*cap+16*w+16*m+35),?_,hpre.trans htail⟩
  unfold cycleBound
  omega

def finalOutput (w : ℕ) (out : List Bool) (s : Store) := if s.present then out++pair w s else out
def finalStore (s : Store) := if s.present then emitted s else s

theorem finish_run (s : Store) (cap w p m : ℕ) (pre out : List Bool) (ha : 4*w+3≤cap) :
    ∃ time≤24*w+27,Timed machine time
      (boundary 0 cap w p m pre.length (pre++[false]) out s)
      (RecoveryCalls.stopped sizes (heads pre.length (finalOutput w out s).length)
        ((finalStore s).tapes cap w p m (pre++[false]) (finalOutput w out s))) := by
  have hfalse : readTapeBit (pre++[false]) pre.length=false := Streaming.read_append pre [] false
  cases hp : s.present
  · have h := probe_stop cap w p m pre.length (pre++[false]) out s (by
      change (if readTapeBit (pre++[false]) pre.length then some (1 : Fin 10) else
        if s.present then some 9 else none)=none
      rw [hfalse,hp]
      rfl)
    exact ⟨1,by omega,by simpa only [finalOutput,finalStore,hp,Bool.false_eq_true,↓reduceIte] using h⟩
  · have h := probe_call 9 cap w p m pre.length (pre++[false]) out s (by
      change (if readTapeBit (pre++[false]) pre.length then some (1 : Fin 10) else
        if s.present then some 9 else none)=some 9
      rw [hfalse,hp]
      rfl)
    have hem := stop_run 9 (24*w+25) cap w p m pre.length pre.length (pre++[false]) out
      (out++pair w s) s (emitted s) (emit_run s cap w p m pre.length (pre++[false]) out ha)
      (by intro q; rfl)
    exact ⟨1+(24*w+25+1),by omega,by simpa only [finalOutput,finalStore,hp,↓reduceIte] using h.trans hem⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
