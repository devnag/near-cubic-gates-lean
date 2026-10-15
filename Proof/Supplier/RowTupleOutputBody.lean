import Proof.Supplier.RowTupleOutputParts

/-! One physical binary candidate: reset/filter, conditionally append its
position word, then increment and test the retained bounded binary cursor. -/
namespace NearCubicWires.RepairOrdinary.RowTupleOutputBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowTupleFilterParts
open RowTupleOutputParts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states {t s : ℕ} (_ : Machine t s) := s
noncomputable def sizes : Fin 3→ℕ := ![states candidate,5,14]
noncomputable def programs : (i : Fin 3)→Machine 18 (sizes i)
  | ⟨0,_⟩=>candidate
  | ⟨1,_⟩=>append
  | ⟨2,_⟩=>advance
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def next (i : Fin 3) (_ : Fin (sizes i)) (bits : Fin 18→Bool) : Option (Fin 3) :=
  ![some (if bits 9 then 1 else 2),some 2,none] i
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def boundary (i : Fin 3) (w k : ℕ) (x : Data) (flag : Bool) (out : List Bool) :=
  controlConfig (RecoveryCalls.code sizes i) (cfg (programs i).start w k x flag out)
noncomputable def finished (w k : ℕ) (x : Data) (flag : Bool) (out : List Bool) :=
  RecoveryCalls.stopped sizes (cfg candidate.start w k x flag out).heads
    (cfg candidate.start w k x flag out).tapes
def emitted (x : Data) : List Bool := if x.good then x.source else []
def updated (w k n : ℕ) (x : Data) := RowTupleAdvance.next w k n (filtered w k n x)
def budget (w k : ℕ) := k*(52*w+68)+38

theorem entry_eq (w k : ℕ) (x : Data) (flag : Bool) (out : List Bool) :
    boundary 0 w k x flag out=cfg machine.start w k x flag out := by
  apply configuration_ext <;> rfl

theorem candidate_call (w k n M : ℕ) (x : Data) (flag : Bool) (out : List Bool)
    (hn : n<2^(w*k)) (hM : 0<M) (hMw : M≤2^w)
    (hx : x.source=frame (binary (w*k+1) n)) (hb : x.bound=M-1) (hp : x.previous<2^w) :
    ∃ t≤k*(40*w+68)+11,Timed machine t (boundary 0 w k x flag out)
      (boundary (if (filtered w k n x).good then 1 else 2) w k (filtered w k n x) flag out) := by
  obtain ⟨r,hr,rh,rt,_⟩ := RowTupleOutputParts.candidate_run w k n M x flag out hn hM hMw hx hb hp
  have hnext : next 0 r.final.control r.final.scanned=
      some (if (filtered w k n x).good then 1 else 2) := by
    simp only [next,Matrix.cons_val_zero,Configuration.scanned,rh,rt]
    rfl
  obtain ⟨t,ht,h⟩ := call_receipt sizes programs 0 next 0
    (if (filtered w k n x).good then 1 else 2) _ _ r hr hnext
  rw [rh,rt] at h
  exact ⟨t,by omega,h⟩

theorem append_call (w k n : ℕ) (x : Data) (flag : Bool) (out : List Bool)
    (hx : x.source=frame (binary (w*k+1) n)) :
    ∃ t≤4*(w*k)+9,Timed machine t (boundary 1 w k x flag out)
      (boundary 2 w k x flag (out++x.source)) := by
  obtain ⟨r,hr,rh,rt,_⟩ := RowTupleOutputParts.append_run w k n x flag out hx
  obtain ⟨t,ht,h⟩ := call_receipt sizes programs 0 next 1 2 _ _ r hr (by rfl)
  rw [rh,rt] at h
  exact ⟨t,by omega,h⟩

theorem advance_stop (w k n : ℕ) (x : Data) (flag : Bool) (out : List Bool)
    (hn : n<2^(w*k)) (hx : x.source=frame (binary (w*k+1) n)) :
    ∃ t≤8*(w*k)+18,Timed machine t (boundary 2 w k x flag out)
      (finished w k (RowTupleAdvance.next w k n x) (decide (n+1<2^(w*k))) out) := by
  obtain ⟨r,hr,rh,rt,_⟩ := RowTupleOutputParts.advance_run w k n x flag out hn hx
  obtain ⟨t,ht,h⟩ := stop_receipt sizes programs 0 next 2 _ _ r hr (by rfl)
  rw [rh,rt] at h
  exact ⟨t,by omega,h⟩

theorem body_timed (w k n M : ℕ) (x : Data) (flag : Bool) (out : List Bool)
    (hn : n<2^(w*k)) (hM : 0<M) (hMw : M≤2^w)
    (hx : x.source=frame (binary (w*k+1) n)) (hb : x.bound=M-1) (hp : x.previous<2^w) :
    ∃ t≤budget w k,Timed machine t (cfg machine.start w k x flag out)
      (finished w k (updated w k n x) (decide (n+1<2^(w*k)))
        (out++emitted (filtered w k n x))) := by
  obtain ⟨a,ha,arun⟩ := candidate_call w k n M x flag out hn hM hMw hx hb hp
  rw [entry_eq] at arun
  have hsource : (filtered w k n x).source=frame (binary (w*k+1) n) :=
    (RowTupleFilterMeaning.fold_source _ _).trans hx
  cases hg : (filtered w k n x).good with
  | false =>
    obtain ⟨b,hb,brun⟩ := advance_stop w k n (filtered w k n x) flag out hn hsource
    rw [hg] at arun
    refine ⟨a+b,?_,?_⟩
    · unfold budget; nlinarith
    · simpa only [Bool.false_eq_true,↓reduceIte,emitted,hg,List.append_nil,updated] using arun.trans brun
  | true =>
    obtain ⟨b,hb,brun⟩ := append_call w k n (filtered w k n x) flag out hsource
    obtain ⟨c,hc,crun⟩ := advance_stop w k n (filtered w k n x) flag
      (out++(filtered w k n x).source) hn hsource
    rw [hg] at arun
    refine ⟨a+b+c,?_,?_⟩
    · unfold budget; nlinarith
    · simpa only [↓reduceIte,emitted,hg,updated] using (arun.trans brun).trans crun

theorem body_run (w k n M : ℕ) (x : Data) (flag : Bool) (out : List Bool)
    (hn : n<2^(w*k)) (hM : 0<M) (hMw : M≤2^w)
    (hx : x.source=frame (binary (w*k+1) n)) (hb : x.bound=M-1) (hp : x.previous<2^w) :
    ∃ r,runFrom machine (budget w k) (cfg machine.start w k x flag out)=some r ∧
      r.final.heads=(cfg machine.start w k (updated w k n x) (decide (n+1<2^(w*k)))
        (out++emitted (filtered w k n x))).heads ∧
      r.final.tapes=(cfg machine.start w k (updated w k n x) (decide (n+1<2^(w*k)))
        (out++emitted (filtered w k n x))).tapes ∧ r.steps≤budget w k := by
  obtain ⟨t,ht,h⟩ := body_timed w k n M x flag out hn hM hMw hx hb hp
  obtain ⟨r,hr,rf,rs⟩ := h.run (by simp [machine,finished,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more := runFrom_moreFuel machine t (budget w k-t) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact ⟨r,more,by rw [rf]; rfl,by rw [rf]; rfl,rs.le.trans ht⟩

end NearCubicWires.RepairOrdinary.RowTupleOutputBody
