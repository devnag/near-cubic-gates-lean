import Proof.Hierarchy.CompetitorSameBucketGroupControl

/-! Exact node-to-node execution in the existing ten-node grouping machine.
The source and dense-output cursors remain live across every call. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def boundary (j : Fin 10) (cap w p m pos : ℕ)
    (source out : List Bool) (s : Store) :=
  controlConfig (RecoveryCalls.code sizes j)
    (RecoveryCalls.restarted (programs j) (heads pos out.length)
      (s.tapes cap w p m source out))

def readBits (cap w p m pos : ℕ) (source out : List Bool) (s : Store) : Fin 24 → Bool :=
  fun i => readTapeBit (s.tapes cap w p m source out i) (heads pos out.length i)

@[simp] theorem readBits_source (cap w p m pos : ℕ) (source out : List Bool) (s : Store) :
    readBits cap w p m pos source out s 0=readTapeBit source pos := rfl
@[simp] theorem readBits_sign (cap w p m pos : ℕ) (source out : List Bool) (s : Store) :
    readBits cap w p m pos source out s 10=s.sign := rfl
@[simp] theorem readBits_present (cap w p m pos : ℕ) (source out : List Bool) (s : Store) :
    readBits cap w p m pos source out s 11=s.present := rfl
@[simp] theorem readBits_same (cap w p m pos : ℕ) (source out : List Bool) (s : Store) :
    readBits cap w p m pos source out s 12=s.same := rfl

theorem call_run (j l : Fin 10) (time cap w p m pos npos : ℕ)
    (source out nout : List Bool) (s ns : Store)
    (h : Run (programs j) time cap w p m pos npos source out nout s ns)
    (hn : ∀ q,next j q (readBits cap w p m npos source nout ns)=some l) :
    Timed machine (time+1) (boundary j cap w p m pos source out s)
      (boundary l cap w p m npos source nout ns) := by
  obtain ⟨r,hr,hh,ht,hs⟩ := h
  obtain ⟨hp,hhalt⟩ := prefix_of_run (programs j) time _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  rw [hs] at hb
  have hnext : next j r.final.control r.final.scanned=some l := by
    change next j r.final.control (fun i => readTapeBit (r.final.tapes i) (r.final.heads i))=_
    rw [hh,ht]
    exact hn r.final.control
  have he := RecoveryCalls.return_step sizes programs 0 next j l r.final hhalt hnext
  have hout : RecoveryCalls.restarted (programs l) r.final.heads r.final.tapes=
      RecoveryCalls.restarted (programs l) (heads npos nout.length)
        (ns.tapes cap w p m source nout) := by rw [hh,ht]
  rw [hout] at he
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem stop_run (j : Fin 10) (time cap w p m pos npos : ℕ)
    (source out nout : List Bool) (s ns : Store)
    (h : Run (programs j) time cap w p m pos npos source out nout s ns)
    (hn : ∀ q,next j q (readBits cap w p m npos source nout ns)=none) :
    Timed machine (time+1) (boundary j cap w p m pos source out s)
      (RecoveryCalls.stopped sizes (heads npos nout.length) (ns.tapes cap w p m source nout)) := by
  obtain ⟨r,hr,hh,ht,hs⟩ := h
  obtain ⟨hp,hhalt⟩ := prefix_of_run (programs j) time _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  rw [hs] at hb
  have hnext : next j r.final.control r.final.scanned=none := by
    change next j r.final.control (fun i => readTapeBit (r.final.tapes i) (r.final.heads i))=_
    rw [hh,ht]
    exact hn r.final.control
  have he := RecoveryCalls.stop_step sizes programs 0 next j r.final hhalt hnext
  rw [hh,ht] at he
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem probe_call (l : Fin 10) (cap w p m pos : ℕ) (source out : List Bool) (s : Store)
    (hn : next 0 (programs 0).start (readBits cap w p m pos source out s)=some l) :
    Timed machine 1 (boundary 0 cap w p m pos source out s)
      (boundary l cap w p m pos source out s) := by
  have he := RecoveryCalls.return_step sizes programs 0 next 0 l
    (RecoveryCalls.restarted (programs 0) (heads pos out.length) (s.tapes cap w p m source out))
    (by rfl) hn
  exact Timed.single (by simp [machine,boundary,RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he

theorem probe_stop (cap w p m pos : ℕ) (source out : List Bool) (s : Store)
    (hn : next 0 (programs 0).start (readBits cap w p m pos source out s)=none) :
    Timed machine 1 (boundary 0 cap w p m pos source out s)
      (RecoveryCalls.stopped sizes (heads pos out.length) (s.tapes cap w p m source out)) := by
  have he := RecoveryCalls.stop_step sizes programs 0 next 0
    (RecoveryCalls.restarted (programs 0) (heads pos out.length) (s.tapes cap w p m source out))
    (by rfl) hn
  exact Timed.single (by simp [machine,boundary,RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
