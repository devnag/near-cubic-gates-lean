import Proof.PCP.VerifierLookupCappedWalk

/-! The arithmetic in the runtime table walk acts on physical framed query
and ordinal tapes. The source cursor and both unary dimensions are retained. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupSelect
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  source : List Bool
  pos : ℕ
  query : List Bool
  counter : List Bool
  flag : Bool
  cap : ℕ
  driverA : List Bool
  driverB : List Bool

def cfg {s : ℕ} (q : Fin s) (d : Store) : Configuration 7 s :=
  ⟨q,fun i=>match i.val with | 0=>d.pos | 5=>1 | 6=>1 | _=>0,
    fun i=>match i.val with
      | 0=>d.source | 1=>frame d.query | 2=>frame d.counter | 3=>[d.flag]
      | 4=>List.replicate d.cap false | 5=>d.driverA | _=>d.driverB⟩

def compareSlots : Fin 4 → Fin 7 := ![1,2,3,4]
def incrementSlots : Fin 2 → Fin 7 := ![2,4]
noncomputable def compareProgram := RecoveryFocus.machine compareSlots compareMachine
noncomputable def incrementProgram := RecoveryFocus.machine incrementSlots FramedIncrement.machine

theorem compare_place {s : ℕ} (q : Fin s) (d : Store) (c : Configuration 4 s)
    (hq : c.control=q) (hh : ∀ i,c.heads i=0)
    (ht : c.tapes=![frame d.query,frame d.counter,[d.flag],List.replicate d.cap false])
    (ambient : Store) (hs : ambient.source=d.source) (hp : ambient.pos=d.pos)
    (ha : ambient.driverA=d.driverA) (hb : ambient.driverB=d.driverB) :
    RecoveryFocus.config compareSlots (cfg q ambient).heads (cfg q ambient).tapes c=cfg q d := by
  apply TransitionEvent.focused_eq compareSlots (by decide) (cfg q ambient)
  · exact hq
  · intro i; rw [hh]; fin_cases i <;> rfl
  · intro i; rw [ht]; fin_cases i <;> rfl
  · intro i h; fin_cases i
    · exact hp
    · exact False.elim (h 0 rfl)
    · exact False.elim (h 1 rfl)
    · exact False.elim (h 2 rfl)
    · exact False.elim (h 3 rfl)
    · rfl
    · rfl
  · intro i h; fin_cases i
    · exact hs
    · exact False.elim (h 0 rfl)
    · exact False.elim (h 1 rfl)
    · exact False.elim (h 2 rfl)
    · exact False.elim (h 3 rfl)
    · exact ha
    · exact hb

theorem compare_run (d : Store) (hw : d.query.length=d.counter.length) (hf : d.flag=false)
    (hc : 2*d.query.length+1≤d.cap) :
    ∃ r,runFrom compareProgram (4*d.query.length+4) (cfg compareProgram.start d)=some r ∧
      r.final=cfg r.final.control {d with flag:=decide (value d.query≤value d.counter)} ∧
      r.steps=4*d.query.length+4 := by
  obtain ⟨base,hb,hbt,hbh,hbs⟩ := compare_ready d.query d.counter d.cap hw
  have hi : RecoveryFocus.config compareSlots (cfg compareMachine.start d).heads
      (cfg compareMachine.start d).tapes
      (initialConfiguration compareMachine ![frame d.query,frame d.counter,[false],List.replicate d.cap false])=
      cfg compareMachine.start d :=
    compare_place _ d _ rfl (by intro i; rfl) (by rw [hf]; rfl) d rfl rfl rfl rfl
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config compareSlots (by decide) compareMachine
    (cfg compareMachine.start d).heads (cfg compareMachine.start d).tapes _ _ base hb
  rw [hi] at hr
  have ho : RecoveryFocus.config compareSlots (cfg compareMachine.start d).heads
      (cfg compareMachine.start d).tapes base.final=
      cfg base.final.control {d with flag:=decide (value d.query≤value d.counter)} := by
    apply compare_place _ _ _ rfl hbh
    · simpa only [max_eq_left hc] using hbt
    all_goals rfl
  exact ⟨r,hr,by rw [hrf,ho]; rfl,hrs.trans hbs⟩

theorem increment_place {s : ℕ} (q : Fin s) (d : Store) (c : Configuration 2 s)
    (hq : c.control=q) (hh : ∀ i,c.heads i=0)
    (ht : c.tapes=![frame d.counter,List.replicate d.cap false]) (ambient : Store)
    (hs : ambient.source=d.source) (hp : ambient.pos=d.pos) (hqv : ambient.query=d.query)
    (hf : ambient.flag=d.flag) (ha : ambient.driverA=d.driverA) (hb : ambient.driverB=d.driverB) :
    RecoveryFocus.config incrementSlots (cfg q ambient).heads (cfg q ambient).tapes c=cfg q d := by
  apply TransitionEvent.focused_eq incrementSlots (by decide) (cfg q ambient)
  · exact hq
  · intro i; rw [hh]; fin_cases i <;> rfl
  · intro i; rw [ht]; fin_cases i <;> rfl
  · intro i h; fin_cases i
    · exact hp
    · rfl
    · exact False.elim (h 0 rfl)
    · rfl
    · exact False.elim (h 1 rfl)
    · rfl
    · rfl
  · intro i h; fin_cases i
    · exact hs
    · exact congrArg frame hqv
    · exact False.elim (h 0 rfl)
    · exact congrArg (fun x=>[x]) hf
    · exact False.elim (h 1 rfl)
    · exact ha
    · exact hb

theorem increment_run (d : Store) (n : ℕ) (hc : d.counter=binary d.query.length n)
    (hn : n+1<2^d.query.length) (hcap : 2*d.query.length≤d.cap) :
    ∃ r,runFrom incrementProgram (4*d.query.length+2) (cfg incrementProgram.start d)=some r ∧
      r.final=cfg r.final.control {d with counter:=binary d.query.length (n+1)} ∧
      r.steps≤4*d.query.length+2 := by
  obtain ⟨base,hb,hb0,hb1,hbh,hbs,_⟩ := FramedIncrement.increment_run d.query.length n d.cap hn hcap
  have hbt : base.final.tapes=![frame (binary d.query.length (n+1)),List.replicate d.cap false] := by
    funext i; fin_cases i
    · exact hb0
    · exact hb1
  have hin : Fin.addCases (motive:=fun _ : Fin (1+1)=>List Bool)
      (fun _ : Fin 1=>frame (binary d.query.length n)) (fun _ : Fin 1=>List.replicate d.cap false)=
      (![frame d.counter,List.replicate d.cap false] : Fin 2→List Bool) := by
    rw [hc]; funext i; fin_cases i <;> rfl
  rw [hin] at hb
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config incrementSlots (by decide) FramedIncrement.machine
    (cfg FramedIncrement.machine.start d).heads (cfg FramedIncrement.machine.start d).tapes _ _ base hb
  have hi : RecoveryFocus.config incrementSlots (cfg FramedIncrement.machine.start d).heads
      (cfg FramedIncrement.machine.start d).tapes
      (initialConfiguration FramedIncrement.machine ![frame d.counter,List.replicate d.cap false])=
      cfg FramedIncrement.machine.start d :=
    increment_place _ d _ rfl (by intro i; rfl) rfl d rfl rfl rfl rfl rfl rfl
  rw [hi] at hr
  have ho : RecoveryFocus.config incrementSlots (cfg FramedIncrement.machine.start d).heads
      (cfg FramedIncrement.machine.start d).tapes base.final=
      cfg base.final.control {d with counter:=binary d.query.length (n+1)} := by
    apply increment_place _ _ _ rfl hbh hbt
    all_goals rfl
  exact ⟨r,hr,by rw [hrf,ho]; rfl,hrs.trans_le hbs⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupSelect
