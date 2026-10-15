import Proof.Hierarchy.CompetitorSameBucketGroupCycle

/-! Whole execution of the existing grouping controller over the original
record stream. This theorem retains prepared scalar workspaces explicitly;
the cold producer must construct them and discharge the per-cell fits. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (p m : ℕ) (es : List Entry) := es.flatMap (fun e => StablePartition.recordBits (e.record p m))
def emittedPrefix (w m : ℕ) (s : Store) (e : Entry) := if changed s m e then pair w s else []
def scanStore (p m : ℕ) (s : Store) : List Entry → Store
  | [] => finalStore s
  | e::es => scanStore p m (stepStore s p m e) es
def scanWord (w p m : ℕ) (s : Store) : List Entry → List Bool
  | [] => if s.present then pair w s else []
  | e::es => emittedPrefix w m s e++scanWord w p m (stepStore s p m e) es
def FitsAll (w p m : ℕ) (s : Store) : List Entry → Prop
  | [] => True
  | e::es => Fits w p m s e ∧ FitsAll w p m (stepStore s p m e) es

theorem fields_stream (p m : ℕ) (es : List Entry) : stream p m es=fields p m es++[false] := by
  simp [stream,records,StablePartition.stream,StablePartition.recordsBits,fields,List.flatMap_map]
theorem stream_cons (p m : ℕ) (e : Entry) (es : List Entry) :
    stream p m (e::es)=StablePartition.recordBits (e.record p m)++stream p m es := by
  simp only [fields_stream,fields,List.flatMap_cons,List.append_assoc]
theorem record_length (p m : ℕ) (e : Entry) :
    (StablePartition.recordBits (e.record p m)).length=2*p+4*m+5 := by
  rw [← CompetitorSameBucketGroupRead.entry_word,CompetitorSameBucketGroupRead.word_length,
    binary_length,ids_length]
  omega
theorem prefixOutput_append (s : Store) (w m : ℕ) (e : Entry) (out : List Bool) :
    prefixOutput s w m e out=out++emittedPrefix w m s e := by
  unfold prefixOutput emittedPrefix
  split <;> simp

theorem loop_run (cap w p m : ℕ) (pre out : List Bool) (es : List Entry) (s : Store)
    (hv : Valid p m s) (hpw : p≤w) (hc : 8*m+3≤cap) (ha : 4*w+3≤cap)
    (hfit : FitsAll w p m s es) :
    ∃ time≤es.length*cycleBound cap w p m+(24*w+27),
      Timed machine time
        (boundary 0 cap w p m pre.length (pre++stream p m es) out s)
        (RecoveryCalls.stopped sizes
          (heads (pre++fields p m es).length (out++scanWord w p m s es).length)
          ((scanStore p m s es).tapes cap w p m (pre++stream p m es) (out++scanWord w p m s es))) := by
  induction es generalizing pre out s with
  | nil =>
    obtain ⟨n,hn,h⟩ := finish_run s cap w p m pre out ha
    refine ⟨n,by simpa using hn,?_⟩
    cases hp : s.present <;>
      simpa [fields_stream,fields,scanStore,scanWord,finalOutput,hp] using h
  | cons e es ih =>
    obtain ⟨n,hn,hcycle⟩ := cycle_run s cap w p m pre (stream p m es) out e hv hpw hc ha hfit.1
    obtain ⟨k,hk,hloop⟩ := ih (pre++StablePartition.recordBits (e.record p m))
      (prefixOutput s w m e out) (stepStore s p m e) (stepStore_valid s p m e) hfit.2
    have hpos : (pre++StablePartition.recordBits (e.record p m)).length=
        pre.length+2*p+4*m+5 := by rw [List.length_append,record_length];omega
    rw [hpos] at hloop
    have h := hcycle.trans hloop
    refine ⟨n+k,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [stream_cons,fields,List.flatMap_cons,scanStore,scanWord,prefixOutput_append,
        List.append_assoc] using h

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
