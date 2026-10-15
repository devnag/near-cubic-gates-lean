import Proof.Amplification.RecoveryRowLookupRead

/-! Whole streamed prior-row lookup body, including malformed reads, paid
returns, and the retained first matching count. This body is ready for the
bounded rejecting repeat over the already checked table prefix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sizes : Fin 2→Nat :=
  ![Fintype.card (RecoveryCalls.Control RecoveryRowFields.sizes),
    Fintype.card (RecoveryCalls.Control RecoveryRowLookupCell.sizes)]
noncomputable def programs : (j : Fin 2)→Machine 14 (sizes j)
  | ⟨0,_⟩=>readMachine
  | ⟨1,_⟩=>cellMachine
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (scanned : Fin 14→Bool) : Option (Fin 2) :=
  if j.val=0 then if scanned 6 then some 1 else none else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (width : Nat) := 32*width+50

theorem row_run (d : Data) (pre bits : List Bool) (hd : d.Valid)
    (hs : d.row.source=pre++frame bits) (hp : d.row.pos=pre.length) :
    ∃ r,runFrom machine (budget d.row.width) (d.cfg machine.start)=some r ∧
      r.steps≤budget d.row.width ∧ r.final.heads 6=0 ∧
      r.final.tapes 6=[(readRow d.row.width bits).isSome] ∧
      ((readRow d.row.width bits).isSome=true →
        r.final=(d.done bits).cfg (RecoveryCalls.controlCode sizes none) ∧ (d.done bits).Valid) := by
  obtain ⟨r0,hr0,_,hh0,ht0,hf0⟩ := read_run d pre bits hd hs hp
  by_cases ha : (readRow d.row.width bits).isSome=true
  · have hw : 4*d.row.width≤bits.length := by
      rw [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at ha
      exact ha
    obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 1 _ _ r0 hr0 (by
      simp [next,Configuration.scanned,hh0,ht0,ha,readTapeBit])
    rw [hf0 ha] at h0
    change Timed machine n0 (d.cfg (RecoveryCalls.code sizes 0 readMachine.start))
      ((d.afterRead bits).cfg (RecoveryCalls.code sizes 1 cellMachine.start)) at h0
    obtain ⟨r1,hr1,hf1,_⟩ := read_cell_run d bits hd hw
    obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 1 _ _ r1 hr1 (by rfl)
    rw [hf1] at h1
    change Timed machine n1 ((d.afterRead bits).cfg (RecoveryCalls.code sizes 1 cellMachine.start))
      ((d.done bits).cfg (RecoveryCalls.controlCode sizes none)) at h1
    have h := h0.trans h1
    have hn : n0+n1≤budget d.row.width := by
      change n0≤16*d.row.width+14+1 at hn0
      unfold budget
      omega
    obtain ⟨r,hr,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,Data.cfg])
    have hm := runFrom_moreFuel machine (n0+n1) (budget d.row.width-(n0+n1)) _ r hr
    rw [Nat.add_sub_of_le hn] at hm
    refine ⟨r,hm,hsteps.le.trans hn,?_,?_,fun _=>⟨hf,done_valid d bits hd hw⟩⟩
    · rw [hf]; rfl
    · rw [hf]
      change [true]=[(readRow d.row.width bits).isSome]
      rw [ha]
  · have hfalse : (readRow d.row.width bits).isSome=false := Bool.eq_false_iff.mpr ha
    obtain ⟨n0,hn0,h0⟩ := stop_receipt sizes programs 0 next 0 _ _ r0 hr0 (by
      simp [next,Configuration.scanned,hh0,ht0,hfalse,readTapeBit])
    obtain ⟨r,hr,hf,hsteps⟩ := h0.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hn : n0≤budget d.row.width := by
      change n0≤16*d.row.width+14+1 at hn0
      unfold budget
      omega
    have hm := runFrom_moreFuel machine n0 (budget d.row.width-n0) _ r hr
    rw [Nat.add_sub_of_le hn] at hm
    refine ⟨r,hm,hsteps.le.trans hn,?_,?_,fun h=>False.elim (ha h)⟩
    · simpa [hf,RecoveryCalls.stopped] using hh0
    · simpa [hf,RecoveryCalls.stopped] using ht0

end NearCubicWires.RepairOrdinary.RecoveryRowLookupStream
