import Proof.Amplification.RecoveryCommittedBitCore

/-! Actual reusable committed-word lookup with paid result clearing and
rewind. Running time depends on the two word lengths, never the index value. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCommittedBit
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawCost (query bits : List Bool) := bits.length*(4*query.length+9)+4

theorem raw_run (bits : List Bool) (d : Data) (pre : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length)
    (hc : 2*d.query.length+1≤d.capacity) :
    ∃ r,runFrom raw (rawCost d.query bits) (d.cfg raw.start)=some r ∧
      r.steps≤rawCost d.query bits ∧
      r.final=(finishData bits (d.picked false)).cfg (RecoveryCalls.controlCode graphSizes none) := by
  obtain ⟨r0,hr0,hf0,_⟩ := write_run d false false
  obtain ⟨n0,hn0,h0⟩ := call_receipt graphSizes programs 4 next 4 0 _ _ r0 hr0 (by rfl)
  rw [hf0] at h0
  change Timed raw n0 (d.cfg raw.start) ((d.picked false).cfg (RecoveryCalls.code graphSizes 0 (0 : Fin 3))) at h0
  obtain ⟨n1,hn1,h1⟩ := core_run bits (d.picked false) pre hs hp hc
  have h := h0.trans h1
  have hn : n0+n1≤rawCost d.query bits := by
    change n1≤bits.length*(4*d.query.length+9)+2 at hn1
    unfold rawCost
    omega
  obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [RecoveryCalls.machine,Data.cfg])
  have hm := runFrom_moreFuel raw (n0+n1) (rawCost d.query bits-(n0+n1)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,ht.le.trans hn,hf⟩

def initialData (query bits : List Bool) (flag result : Bool) (capacity : Nat) : Data :=
  ⟨query,frame bits,0,flag,result,capacity⟩

theorem lookup_run (query bits : List Bool) (oldFlag oldResult : Bool) (capacity : Nat)
    (hsmall : 2*query.length+1≤capacity) (hcap : rawCost query bits≤capacity) :
    ∃ r,run machine (2*rawCost query bits+2)
        ![frame query,[oldFlag],List.replicate capacity false,frame bits,[oldResult],List.replicate capacity false]=some r ∧
      r.steps≤2*rawCost query bits+2 ∧ (∀ i,r.final.heads i=0) ∧
      ∃ remainder flag,remainder.length=query.length ∧
        r.final.tapes=![frame remainder,[flag],List.replicate capacity false,frame bits,
          [(value bits).testBit (value query)],List.replicate capacity false] := by
  let d := initialData query bits oldFlag oldResult capacity
  obtain ⟨base,hr,hbound,hf⟩ := raw_run bits d [] rfl rfl hsmall
  have hi : d.cfg raw.start=initialConfiguration raw
      ![frame query,[oldFlag],List.replicate capacity false,frame bits,[oldResult]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hr
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hr capacity
  have hb : base.steps≤rawCost query bits := hbound
  have hn : 2*base.steps+2≤2*rawCost query bits+2 := by omega
  have hm := runFrom_moreFuel machine (2*base.steps+2) (2*rawCost query bits+2-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,?_,hsteps.le.trans hn,hh,(finishData bits (d.picked false)).query,
    (finishData bits (d.picked false)).flag,finish_query_length bits (d.picked false),?_⟩
  · have he : (fun i => Fin.addCases
        ![frame query,[oldFlag],List.replicate capacity false,frame bits,[oldResult]]
        (fun _ : Fin 1 => List.replicate capacity false) i)=
        ![frame query,[oldFlag],List.replicate capacity false,frame bits,[oldResult],List.replicate capacity false] := by
      funext i; fin_cases i <;> rfl
    rw [he] at hm
    exact hm
  · funext i; fin_cases i
    · simpa [hf,Data.cfg] using ht 0
    · simpa [hf,Data.cfg] using ht 1
    · simpa [hf,Data.cfg,finish_capacity,d,Data.picked,initialData] using ht 2
    · simpa [hf,Data.cfg,finish_source,d,Data.picked,initialData] using ht 3
    · have hv := finish_result bits (d.picked false) rfl
      rw [answer_bitAt,bitAt_testBit] at hv
      have h4 := ht 4
      rw [hf] at h4
      change r.final.tapes 4=[(finishData bits (d.picked false)).result] at h4
      rw [hv] at h4
      exact h4
    · change r.final.tapes (Fin.natAdd 5 0)=List.replicate capacity false
      simpa only [Nat.max_eq_left (hb.trans hcap)] using hc

end NearCubicWires.RepairOrdinary.RecoveryCommittedBit
