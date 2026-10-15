import Proof.PCP.VerifierLookupSelectArithmetic

/-! A fixed finite comparison/increment/skip controller performs the actual
linear table search. Its ordinal starts on a physical tape; no address or
row is an instruction. The concrete record skipper is supplied separately. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupSelect
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes (s : ℕ) : Fin 3 → ℕ := ![7,5,s]
noncomputable def programs {s : ℕ} (skip : Machine 7 s) : (j : Fin 3) → Machine 7 (sizes s j)
  | 0 => compareProgram
  | 1 => incrementProgram
  | 2 => skip

def next {s : ℕ} (j : Fin 3) (_ : Fin (sizes s j)) (bits : Fin 7 → Bool) : Option (Fin 3) :=
  if j.val=0 then if bits 3 then none else some 1
  else if j.val=1 then some 2 else some 0
noncomputable def machine {s : ℕ} (skip : Machine 7 s) := RecoveryCalls.machine (sizes s) (programs skip) 0 next

theorem call_prefix {s : ℕ} (skip : Machine 7 s) (j k : Fin 3) (d e : Store) (fuel : ℕ)
    (r : ExecutionReceipt 7 (sizes s j))
    (hr : runFrom (programs skip j) fuel (cfg (programs skip j).start d)=some r)
    (hf : r.final=cfg r.final.control e)
    (hn : next j r.final.control r.final.scanned=some k) :
    ∃ n≤fuel+1,Timed (machine skip) n
      (cfg (RecoveryCalls.code (sizes s) j (programs skip j).start) d)
      (cfg (RecoveryCalls.code (sizes s) k (programs skip k).start) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs skip j) fuel _ r hr
  have hb := RecoveryCalls.body_timed (sizes s) (programs skip) 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step (sizes s) (programs skip) 0 next j k r.final hh hn
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs skip j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

theorem stop_prefix {s : ℕ} (skip : Machine 7 s) (j : Fin 3) (d e : Store) (fuel : ℕ)
    (r : ExecutionReceipt 7 (sizes s j))
    (hr : runFrom (programs skip j) fuel (cfg (programs skip j).start d)=some r)
    (hf : r.final=cfg r.final.control e)
    (hn : next j r.final.control r.final.scanned=none) :
    ∃ n≤fuel+1,Timed (machine skip) n
      (cfg (RecoveryCalls.code (sizes s) j (programs skip j).start) d)
      (cfg (RecoveryCalls.controlCode (sizes s) none) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs skip j) fuel _ r hr
  have hb := RecoveryCalls.body_timed (sizes s) (programs skip) 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step (sizes s) (programs skip) 0 next j r.final hh hn
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs skip j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

def completed (d : Store) (n stride : ℕ) : Store :=
  {d with pos:=d.pos+n*stride,counter:=binary d.query.length (value d.query),flag:=true}

theorem search_prefix {s : ℕ} (skip : Machine 7 s) (stride skipBudget : ℕ)
    (driverA driverB : List Bool)
    (hskip : ∀ d : Store,d.driverA=driverA → d.driverB=driverB →
      ∃ r,runFrom skip skipBudget (cfg skip.start d)=some r ∧
        r.final=cfg r.final.control {d with pos:=d.pos+stride})
    (n k : ℕ) (d : Store) (hk : k+n=value d.query)
    (hcounter : d.counter=binary d.query.length k) (hflag : d.flag=false)
    (hcap : 2*d.query.length+1≤d.cap) (ha : d.driverA=driverA) (hb : d.driverB=driverB) :
    ∃ time≤(n+1)*(8*d.query.length+skipBudget+9),Timed (machine skip) time
      (cfg (machine skip).start d)
      (cfg (RecoveryCalls.controlCode (sizes s) none) (completed d n stride)) := by
  induction n generalizing k d with
  | zero =>
    have hw : d.query.length=d.counter.length := by rw [hcounter,binary_length]
    obtain ⟨r,hr,hrf,_⟩ := compare_run d hw hflag hcap
    have hv : value d.counter=k := by
      rw [hcounter,binary_value]
      have hx := value_lt d.query
      omega
    have hflag' : decide (value d.query≤value d.counter)=true := by rw [hv]; simp only [Nat.add_zero] at hk; simp [hk]
    rw [hflag'] at hrf
    obtain ⟨time,ht,hp⟩ := stop_prefix skip 0 d {d with flag:=true} _ r hr hrf (by
      rw [hrf]
      simp [next,cfg,Configuration.scanned,readTapeBit,List.getD])
    have hout : {d with flag:=true}=completed d 0 stride := by
      simp only [completed,Nat.zero_mul,Nat.add_zero]
      congr 1
      rw [hcounter]
      congr 1
    rw [hout] at hp
    exact ⟨time,by omega,hp⟩
  | succ n ih =>
    have hw : d.query.length=d.counter.length := by rw [hcounter,binary_length]
    obtain ⟨cmp,hcmp,hcmpf,_⟩ := compare_run d hw hflag hcap
    have hv : value d.counter=k := by
      rw [hcounter,binary_value]
      have hx := value_lt d.query
      omega
    have hflag' : decide (value d.query≤value d.counter)=false := by rw [hv]; simp only [decide_eq_false_iff_not]; omega
    rw [hflag'] at hcmpf
    have hsame : {d with flag:=false}=d := by rw [←hflag]
    rw [hsame] at hcmpf
    obtain ⟨ct,hct,hcp⟩ := call_prefix skip 0 1 d d _ cmp hcmp hcmpf (by
      rw [hcmpf]
      simp [next,cfg,Configuration.scanned,hflag,readTapeBit,List.getD])
    have hnext : k+1<2^d.query.length := by have hx := value_lt d.query; omega
    obtain ⟨inc,hinc,hincf,_⟩ := increment_run d k hcounter hnext (by omega)
    let di : Store := {d with counter:=binary d.query.length (k+1)}
    obtain ⟨it,hit,hip⟩ := call_prefix skip 1 2 d di _ inc hinc hincf (by rfl)
    obtain ⟨sk,hsk,hskf⟩ := hskip di ha hb
    let ds : Store := {di with pos:=di.pos+stride}
    obtain ⟨st,hst,hsp⟩ := call_prefix skip 2 0 di ds skipBudget sk hsk hskf (by rfl)
    obtain ⟨tt,htt,htp⟩ := ih (k+1) ds (by change k+1+n=value d.query; omega) rfl hflag hcap ha hb
    have hp := ((hcp.trans hip).trans hsp).trans htp
    have hout : completed ds n stride=completed d (n+1) stride := by
      unfold completed ds di
      congr 1
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    rw [hout] at hp
    refine ⟨((ct+it)+st)+tt,?_,hp⟩
    change tt≤(n+1)*(8*d.query.length+skipBudget+9) at htt
    have he : (n+1+1)*(8*d.query.length+skipBudget+9)=
        (n+1)*(8*d.query.length+skipBudget+9)+(8*d.query.length+skipBudget+9) := by ring
    rw [he]
    omega

theorem search_run {s : ℕ} (skip : Machine 7 s) (stride skipBudget : ℕ)
    (driverA driverB : List Bool)
    (hskip : ∀ d : Store,d.driverA=driverA → d.driverB=driverB →
      ∃ r,runFrom skip skipBudget (cfg skip.start d)=some r ∧
        r.final=cfg r.final.control {d with pos:=d.pos+stride})
    (d : Store) (hcounter : d.counter=binary d.query.length 0) (hflag : d.flag=false)
    (hcap : 2*d.query.length+1≤d.cap) (ha : d.driverA=driverA) (hb : d.driverB=driverB) :
    ∃ r,runFrom (machine skip) ((value d.query+1)*(8*d.query.length+skipBudget+9))
      (cfg (machine skip).start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode (sizes s) none) (completed d (value d.query) stride) ∧
      r.steps≤(value d.query+1)*(8*d.query.length+skipBudget+9) := by
  obtain ⟨time,ht,hp⟩ := search_prefix skip stride skipBudget driverA driverB hskip
    (value d.query) 0 d (by omega) hcounter hflag hcap ha hb
  obtain ⟨r,hr,hrf,hrs⟩ := hp.run (by simp [machine,RecoveryCalls.machine,cfg])
  have hm := runFrom_moreFuel (machine skip) time
    (((value d.query+1)*(8*d.query.length+skipBudget+9))-time) _ r hr
  rw [Nat.add_sub_of_le ht] at hm
  exact ⟨r,hm,hrf,hrs.trans_le ht⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupSelect
