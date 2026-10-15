import Proof.MachineModel.OrdinaryTransitionWalkMachine
import Proof.MachineModel.OrdinaryMemoryInitialEmission
import Proof.MachineModel.OrdinaryClaimedTrace

/-! The array's physical stream is the chronological memory batch of the
symbolic trace, with the initialization serial continued without reset. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape SignedSortKey MemoryLog
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def itemEvents : ℕ→List TransitionArray.Item→List Event
  | _,[]=>[]
  | tape,e::es=>⟨(tape,e.head),e.read,TransitionTag.after e.tag e.read⟩::itemEvents (tape+1) es

theorem itemEvents_length (tape : ℕ) (es : List TransitionArray.Item) : (itemEvents tape es).length=es.length := by
  induction es generalizing tape with
  | nil=>rfl
  | cons e es ih=>simp only [itemEvents,List.length_cons,ih]

theorem walk_cursors (w cap : ℕ) (d : TransitionTape.Store) (es : List TransitionArray.Item) :
    (TransitionArray.walk w cap d es).source=d.source ∧
    (TransitionArray.walk w cap d es).pos=d.pos+8*es.length ∧
    (TransitionArray.walk w cap d es).scans=d.scans ∧
    (TransitionArray.walk w cap d es).cursor=d.cursor+2*es.length ∧
    (TransitionArray.walk w cap d es).serial=d.serial+es.length ∧
    (TransitionArray.walk w cap d es).tape=d.tape+es.length := by
  induction es generalizing d with
  | nil=>simp only [TransitionArray.walk,List.length_nil,Nat.mul_zero,Nat.add_zero,and_self]
  | cons e es ih=>
    have h := ih (TransitionArray.finished d w cap e.head e.tag e.read)
    change _=d.source ∧ _=d.pos+8+8*es.length ∧ _=d.scans ∧ _=d.cursor+2+2*es.length ∧
      _=d.serial+1+es.length ∧ _=d.tape+1+es.length at h
    simp only [TransitionArray.walk,List.length_cons]
    obtain ⟨hs,hp,hsc,hc,hser,ht⟩ := h
    refine ⟨hs,?_,hsc,?_,?_,?_⟩
    all_goals omega

theorem walk_difference (w cap : ℕ) (d : TransitionTape.Store) (es : List TransitionArray.Item)
    (h : d.head.difference.length≤2*w+1) :
    (TransitionArray.walk w cap d es).head.difference.length≤2*w+1 := by
  induction es generalizing d with
  | nil=>exact h
  | cons e es ih=>
    exact ih _ (TransitionArray.finished_difference d w cap e h)

theorem walk_stream (w cap : ℕ) (d : TransitionTape.Store) (es : List TransitionArray.Item)
    (hh : ∀ e∈es,e.head<2^w) (ht : d.tape+es.length<2^w) :
    (TransitionArray.walk w cap d es).out=d.out++
      MemoryInitialEmission.fields (2*w) (2*w+2) w d.serial (itemEvents d.tape es) := by
  induction es generalizing d with
  | nil=>simp [TransitionArray.walk,itemEvents,MemoryInitialEmission.fields,StablePartition.recordsBits]
  | cons e es ih=>
    let next := TransitionArray.finished d w cap e.head e.tag e.read
    have htail := ih next (by intro x hx; exact hh x (by simp [hx]))
      (by change d.tape+1+es.length<2^w; simp only [List.length_cons] at ht; omega)
    change (TransitionArray.walk w cap next es).out=_
    rw [htail]
    have hfirst : next.out=d.out++frame (e.read::TransitionTag.after e.tag e.read::
        binary (2*w) d.serial++binary (2*w+2) (d.tape*2^w+e.head)) :=
      TransitionTape.finished_stream (TransitionArray.loaded d e.head) w cap e.tag e.read
        (hh e (by simp)) (by change d.tape<2^w; omega)
    rw [hfirst]
    change (d.out++frame (e.read::TransitionTag.after e.tag e.read::binary (2*w) d.serial++
      binary (2*w+2) (d.tape*2^w+e.head)))++
      MemoryInitialEmission.fields (2*w) (2*w+2) w (d.serial+1) (itemEvents (d.tape+1) es)=_
    simp only [itemEvents,MemoryInitialEmission.fields,List.zipIdx_cons,List.map_cons,
      StablePartition.recordsBits,List.flatMap_cons,StablePartition.recordBits,MemorySort.encoded,
      MemorySort.cellCode,List.append_assoc,List.cons_append,RepairOrdinary.frame]

theorem itemEvents_ofFn {t : ℕ} (tape : ℕ) (f : Fin t→TransitionArray.Item) :
    itemEvents tape (List.ofFn f)=List.ofFn (fun i=>
      (⟨(tape+i.val,(f i).head),(f i).read,TransitionTag.after (f i).tag (f i).read⟩ : Event)) := by
  induction t generalizing tape with
  | zero=>simp only [List.ofFn_zero,itemEvents]
  | succ t ih=>
    rw [List.ofFn_succ,itemEvents,ih,List.ofFn_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    congr 2
    omega

theorem actionItems_events {t s : ℕ} (a : Action t s) (heads : Fin t→ℕ) (reads : Fin t→Bool) :
    itemEvents 0 (actionItems a heads reads)=
      MemoryTransition.batch heads reads (fun i=>(a.write i).getD (reads i)) := by
  rw [actionItems,itemEvents_ofFn]
  simp only [Nat.zero_add,actionTag_after,List.ofFn_eq_map,MemoryTransition.batch]
  rfl

end NearCubicWires.RepairOrdinary.TransitionWalk
