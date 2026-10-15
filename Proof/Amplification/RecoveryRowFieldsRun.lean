import Proof.Amplification.RecoveryRowFields

/-! The complete four-field row controller, including each paid return and
short-row rejection. Bounds depend only on the input-derived scalar width;
no unread witness suffix is traversed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem programs_start (j : Fin 6) : (programs j).start=0 := by
  fin_cases j <;> rfl

theorem restarted_cfg (d : Data) (j : Fin 6) (q : Fin 6) :
    controlConfig (RecoveryCalls.code sizes j)
      (RecoveryCalls.restarted (programs j) (d.cfg q).heads (d.cfg q).tapes)=
      d.cfg (RecoveryCalls.code sizes j (0 : Fin 6)) := by
  apply configuration_ext
  · exact congrArg (RecoveryCalls.code sizes j) (programs_start j)
  · rfl
  · rfl

noncomputable def terminal (d : Data) := d.cfg (RecoveryCalls.controlCode sizes none)

theorem tail_trace (count start : Nat) (hcount : start+count=4)
    (d : Data) (pre bits : List Bool) (hs : d.source=pre++frame bits)
    (hp : d.pos=pre.length) (hd : d.Valid) :
    ∃ n, ∃ final : Configuration 7 (Fintype.card (RecoveryCalls.Control sizes)),
      n ≤ count*(4*d.width+3)+2 ∧
      Timed machine n
        (d.cfg (RecoveryCalls.code sizes ⟨start,by omega⟩ (0 : Fin 6))) final ∧
      final.control=RecoveryCalls.controlCode sizes none ∧
      final.heads 6=0 ∧ final.tapes 6=[decide (count*d.width ≤ bits.length)] ∧
      (count*d.width ≤ bits.length →
        final=terminal ({afterReads d start count bits with valid:=true} : Data)) := by
  induction count generalizing start d pre bits with
  | zero =>
    have hstart : start=4 := by omega
    subst start
    obtain ⟨r,hr,hf,_⟩ := flag_run d true
    have hrun : runFrom (programs 4) 1 (d.cfg 0)=some r := hr
    obtain ⟨n,hn,h⟩ := stop_receipt sizes programs 0 next 4 _ _ r hrun (by rfl)
    rw [hf] at h
    refine ⟨n,terminal ({d with valid:=true} : Data),?_,h,?_,?_,?_,?_⟩
    · simpa using hn
    · rfl
    · rfl
    · simp [terminal,Data.cfg]
    · intro _; rfl
  | succ count ih =>
    have hstart : start<4 := by omega
    let j : Fin 6 := ⟨start,by omega⟩
    let k : Fin 6 := ⟨start+1,by omega⟩
    have hj : programs j=fieldMachine (index start) := by
      simp [programs,j,index,Nat.mod_eq_of_lt hstart,hstart]
    obtain ⟨r,hr,ha,hh,ht,hf⟩ := field_read d (index start) pre bits hs hp hd
    have hrun : runFrom (programs j) (4*d.width+2) (d.cfg 0)=some r := by rw [hj]; exact hr
    by_cases hw : d.width ≤ bits.length
    · obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next j k _ _ r hrun (by
        simp [next,j,k,hstart,ha.mpr hw])
      rw [hf hw,restarted_cfg] at h0
      change Timed machine n0 (d.cfg (RecoveryCalls.code sizes j (0 : Fin 6)))
        ((d.after (index start) (bits.take d.width)).cfg (RecoveryCalls.code sizes k (0 : Fin 6))) at h0
      have hl : (bits.take d.width).length=d.width := by simp [List.length_take,hw]
      have hsource : (d.after (index start) (bits.take d.width)).source=
          (pre++Streaming.marks (bits.take d.width))++frame (bits.drop d.width) := by
        rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
        exact hs
      have hpos : (d.after (index start) (bits.take d.width)).pos=
          (pre++Streaming.marks (bits.take d.width)).length := by
        simp [Data.after,List.length_append,Streaming.marks_length,hp]
      obtain ⟨n1,final,hn1,h1,hcontrol,hhead,htape,haccept⟩ := ih (start+1) (by omega)
        (d.after (index start) (bits.take d.width)) (pre++Streaming.marks (bits.take d.width))
        (bits.drop d.width) hsource hpos (after_valid d _ _ hd (by omega))
      have hbound : n0+n1 ≤ (count+1)*(4*d.width+3)+2 := by
        change n1 ≤ count*(4*d.width+3)+2 at hn1
        rw [Nat.succ_mul]
        omega
      have hguard : count*d.width ≤ (bits.drop d.width).length ↔
          (count+1)*d.width ≤ bits.length := by
        rw [List.length_drop,Nat.succ_mul]
        omega
      refine ⟨n0+n1,final,hbound,h0.trans h1,hcontrol,hhead,?_,?_⟩
      · simpa only [Data.after,hguard] using htape
      · intro hg
        exact haccept (hguard.mpr hg)
    · obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next j 5 _ _ r hrun (by
        have hq : r.final.control.val≠4 := by
          intro he
          exact hw (ha.mp (Fin.ext he))
        simp [next,j,hstart,hq])
      obtain ⟨z,hz,hzf,_⟩ := flag_raw r.final d.valid false hh ht
      have hzr : runFrom (programs 5) 1
          (RecoveryCalls.restarted (programs 5) r.final.heads r.final.tapes)=some z := hz
      obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 5 _ _ z hzr (by rfl)
      have h := h0.trans h1
      have hg : ¬(count+1)*d.width ≤ bits.length := by rw [Nat.succ_mul]; omega
      refine ⟨n0+n1,RecoveryCalls.stopped sizes z.final.heads z.final.tapes,?_,h,rfl,?_,?_,?_⟩
      · rw [Nat.succ_mul]
        omega
      · simpa [hzf,RecoveryCalls.stopped] using hh
      · simp [hzf,RecoveryCalls.stopped,hg]
      · intro hc; exact False.elim (hg hc)

def budget (width : Nat) := 16*width+14

theorem row_run (d : Data) (pre bits : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length) (hd : d.Valid) :
    ∃ r,runFrom machine (budget d.width) (d.cfg machine.start)=some r ∧
      r.steps ≤ budget d.width ∧ r.final.heads 6=0 ∧
      r.final.tapes 6=[(readRow d.width bits).isSome] ∧
      ((readRow d.width bits).isSome=true →
        r.final=terminal ({afterReads d 0 4 bits with valid:=true} : Data)) := by
  obtain ⟨n,final,hn,h,hc,hh,ht,ha⟩ := tail_trace 4 0 rfl d pre bits hs hp hd
  have hbound : n ≤ budget d.width := by unfold budget; omega
  obtain ⟨r,hr,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,hc])
  have hm := runFrom_moreFuel machine n (budget d.width-n) _ r hr
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨r,hm,hsteps.le.trans hbound,by rw [hf]; exact hh,?_,?_⟩
  · rw [hf,ht,RecoveryCertificateRow.row_isSome]
  · intro hg
    rw [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at hg
    exact hf.trans (ha hg)

end NearCubicWires.RepairOrdinary.RecoveryRowFields
