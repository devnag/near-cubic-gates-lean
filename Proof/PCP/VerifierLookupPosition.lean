import Proof.PCP.VerifierLookupSkipRecord

/-! Actual table and flag selection instantiate the linear search with the
fixed physical skippers. Only existing j/t dimensions are inputs. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupPosition
open LocalBitMultitape RepairOrdinary RecoveryExecution SignedSortKey RadixSemantics
open LookupSelect
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tableMachine := LookupSelect.machine LookupSkip.record
noncomputable def flagsMachine := LookupSelect.machine LookupSkip.flagPair

theorem table_run (d : Store) (j t c : ℕ)
    (hj : d.driverA=CompareMachine.word j) (ht : d.driverB=CapMachine.counter c t)
    (hz : d.counter=binary d.query.length 0) (hf : d.flag=false)
    (hc : 2*d.query.length+1≤d.cap) :
    ∃ r,runFrom tableMachine ((value d.query+1)*(8*d.query.length+3*j+12*t+27))
      (cfg tableMachine.start d)=some r ∧
      r.final=cfg r.final.control (completed d (value d.query) (2*(1+j+4*t))) ∧
      r.steps≤(value d.query+1)*(8*d.query.length+3*j+12*t+27) := by
  have hs : ∀ e : Store,e.driverA=CompareMachine.word j → e.driverB=CapMachine.counter c t →
      ∃ r,runFrom LookupSkip.record (3*j+12*t+18) (cfg LookupSkip.record.start e)=some r ∧
        r.final=cfg r.final.control {e with pos:=e.pos+2*(1+j+4*t)} := by
    intro e heA heB
    obtain ⟨r,hr,hrf,_⟩ := LookupSkip.record_run e j t c heA heB
    exact ⟨r,hr,hrf⟩
  obtain ⟨r,hr,hrf,hrs⟩ := search_run LookupSkip.record (2*(1+j+4*t)) (3*j+12*t+18)
    (CompareMachine.word j) (CapMachine.counter c t) hs d hz hf hc hj ht
  have hb : 8*d.query.length+(3*j+12*t+18)+9=8*d.query.length+3*j+12*t+27 := by omega
  rw [hb] at hr hrs
  exact ⟨r,hr,by rw [hrf]; rfl,hrs⟩

theorem flags_run (d : Store)
    (hz : d.counter=binary d.query.length 0) (hf : d.flag=false)
    (hc : 2*d.query.length+1≤d.cap) :
    ∃ r,runFrom flagsMachine ((value d.query+1)*(8*d.query.length+14))
      (cfg flagsMachine.start d)=some r ∧
      r.final=cfg r.final.control (completed d (value d.query) 4) ∧
      r.steps≤(value d.query+1)*(8*d.query.length+14) := by
  have hs : ∀ e : Store,e.driverA=d.driverA → e.driverB=d.driverB →
      ∃ r,runFrom LookupSkip.flagPair 5 (cfg LookupSkip.flagPair.start e)=some r ∧
        r.final=cfg r.final.control {e with pos:=e.pos+4} := by
    intro e _ _
    exact LookupSkip.flagPair_run e
  obtain ⟨r,hr,hrf,hrs⟩ := search_run LookupSkip.flagPair 4 5 d.driverA d.driverB hs d hz hf hc rfl rfl
  have hb : 8*d.query.length+5+9=8*d.query.length+14 := by omega
  rw [hb] at hr hrs
  exact ⟨r,hr,by rw [hrf]; rfl,hrs⟩

theorem query_value (scans : List Bool) (j state : ℕ) (hs : state<2^j) :
    value (scans++binary j state)=state*2^scans.length+value scans := by
  rw [value_append,binary_value j state hs]
  ring

theorem query_ordinal_lt (scans : List Bool) (s j state : ℕ) (hs : state< s) (hj : s<2^j) :
    value (scans++binary j state)< s*2^scans.length := by
  rw [query_value scans j state (hs.trans hj)]
  have hm := value_lt scans
  have hp := Nat.mul_le_mul_right (2^scans.length) (Nat.succ_le_of_lt hs)
  rw [Nat.succ_mul] at hp
  omega

end NearCubicWires.RepairSource.VerifierDecoding.LookupPosition
