import Proof.PCP.VerifierDecodingTableDelimiter

/-! Whole counted table validation: paid driver rewind, all record calls,
exact end delimiter, and physical final Boolean. No numerical expected-length
producer is used; successful source consumption supplies that equality. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TableValidation
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def valid (bound : List Bool) (t e : ℕ) (bits : List Bool) : Bool :=
  tests bound t e bits && decide (width bound t*e=bits.length)

noncomputable def initial (bound : List Bool) (t cap c e : ℕ) (x : State) :=
  controlConfig (RecoveryCalls.code sizes 0)
    (Composition.leftConfig loopStates (RecordsDriver.cfg (0 : Fin 3) (input bound t cap x) c e (e+1)))

noncomputable def endpoint (bound : List Bool) (t cap c e : ℕ) (out : State) :=
  let base := RecordsDriver.cfg (0 : Fin 3) (input bound t cap out) c e 1
  finished true base.heads base.tapes

theorem close_run {n budget : ℕ}
    {entry : Configuration 9 (Fintype.card (RecoveryCalls.Control sizes))}
    (value : Bool) (heads : Fin 9 → ℕ) (tapes : Fin 9 → List Bool)
    (h : Timed machine n entry (finished value heads tapes)) (hb : n≤budget) :
    ∃ r, runFrom machine budget entry=some r ∧ r.steps≤budget ∧
      r.final=finished value heads tapes ∧ r.final.scanned 7=value := by
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,finished,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine n (budget-n) entry r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,hs.trans_le hb,hf,by rw [hf]; exact finished_scanned value heads tapes⟩

theorem table_run (bound : List Bool) (t cap c e : ℕ)
    (hc : 2*bound.length+1≤cap) (he : e≤c) (x : State) (hx : Inv bound x) :
    ∃ r, runFrom machine (e*(8*bound.length+12*t+34)+11) (initial bound t cap c e x)=some r ∧
      r.steps≤e*(8*bound.length+12*t+34)+11 ∧ r.final.scanned 7=valid bound t e x.bits ∧
      (valid bound t e x.bits=true → ∃ out : State,
        r.final=endpoint bound t cap c e out ∧
        out.pre++frame out.bits=x.pre++frame x.bits ∧
        out.pre.length=x.pre.length+2*width bound t*e ∧ out.bits=[] ∧ Inv bound out) := by
  obtain ⟨base,original,hr,hs,hchecked,hfinal⟩ := RecordsDriver.driver_run bound t cap c e hc he x hx
  cases ht : tests bound t e x.bits with
  | false =>
    simp only [Checked,ht,Bool.false_eq_true,↓reduceIte] at hchecked
    have hn : next 0 base.final.control base.final.scanned=some 3 := by
      simp [next,hfinal,Composition.rightConfig,ZeroPadding.config,hchecked]
      exact reject_ne_success
    have hp := call_prefix 0 3 (e*(8*bound.length+12*t+34)+6) _ base hr hn
    have hall := hp.trans (flag_tail false base.final.heads base.final.tapes)
    obtain ⟨r,hrun,hsteps,_,hbit⟩ := close_run false _ _ hall
      (show base.steps+1+2≤e*(8*bound.length+12*t+34)+11 by omega)
    refine ⟨r,hrun,hsteps,?_,by simp [valid,ht]⟩
    simpa [valid,ht] using hbit
  | true =>
    simp only [Checked,ht,↓reduceIte] at hchecked
    obtain ⟨out,ho,hsource,hpos,hbits,hlen,hinv⟩ := hchecked
    have hb : base.final=Composition.rightConfig 3
        (RecordsDriver.cfg (RepeatMachine.phaseCode recordStates 3) (input bound t cap out) c e 1) := by
      rw [hfinal,ho,RecordsDriver.padded_cfg]
    have hn : next 0 base.final.control base.final.scanned=some 1 := by
      simp [next,hb,Composition.rightConfig,RecordsDriver.cfg]
    have hp := call_prefix 0 1 (e*(8*bound.length+12*t+34)+6) _ base hr hn
    have hd := delimiter_tail out.pre out.bits base.final.heads base.final.tapes
      (by simp [hb,Composition.rightConfig,RecordsDriver.cfg,input,RecordMachine.cfg,Fin.addCases])
      (by simp [hb,Composition.rightConfig,RecordsDriver.cfg,input,RecordMachine.cfg,Fin.addCases])
    have hall := hp.trans hd
    obtain ⟨r,hrun,hsteps,hresult,hbit⟩ := close_run (decide (out.bits=[])) _ _ hall
      (show base.steps+1+4≤e*(8*bound.length+12*t+34)+11 by omega)
    have hend : (out.bits=[]) ↔ width bound t*e=x.bits.length := by
      rw [hbits,List.drop_eq_nil_iff]
      omega
    refine ⟨r,hrun,hsteps,?_,?_⟩
    · simpa [valid,ht,hend] using hbit
    · intro hv
      have hlen' : width bound t*e=x.bits.length := by simpa [valid,ht] using hv
      have hempty := hend.mpr hlen'
      refine ⟨out,?_,hsource,hpos,hempty,hinv⟩
      rw [hresult]
      simp only [hempty,decide_true]
      rw [hb]
      rfl

end NearCubicWires.RepairSource.VerifierDecoding.TableValidation
