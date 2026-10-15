import Proof.PCP.VerifierLookupCodeReset

/-! Navigation acts on the retained literal code and actual t/s/c/j tapes.
It never receives a computed flag or table offset. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupNavigation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  code : List Bool
  pos : ℕ
  c : ℕ
  t : ℕ
  s : ℕ
  j : ℕ

def driver (d : Store) : Fin 4 → List Bool :=
  ![CapMachine.counter d.c d.t,CapMachine.counter d.c d.s,CapMachine.counter d.c d.c,CompareMachine.word d.j]
def cfg {n : ℕ} (q : Fin n) (d : Store) : Configuration 5 n :=
  ⟨q,Fin.cases d.pos (fun _=>1),Fin.cases d.code (driver d)⟩
def positioned (d : Store) (pos : ℕ) : Store := {d with pos:=pos}
def slots (i : Fin 4) : Fin 2 → Fin 5 := ![0,i.succ]

theorem slots_injective (i : Fin 4) : Function.Injective (slots i) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (have he:=congrArg Fin.val h; simp [slots] at he)

def inner {n : ℕ} (q : Fin n) (code tape : List Bool) (pos : ℕ) : Configuration 2 n :=
  ⟨q,![pos,1],![code,tape]⟩

theorem place {n : ℕ} (i : Fin 4) (q : Fin n) (d : Store) (tape : List Bool) (pos : ℕ)
    (hd : driver d i=tape) :
    RecoveryFocus.config (slots i) (cfg q d).heads (cfg q d).tapes
      (inner q d.code tape pos)=cfg q (positioned d pos) := by
  apply TransitionEvent.focused_eq (slots i) (slots_injective i) (cfg q d)
  · rfl
  · intro z; fin_cases z
    · rfl
    · simp [inner,slots,cfg]
  · intro z; fin_cases z
    · rfl
    · simpa [inner,slots,cfg,positioned,driver] using hd.symm
  · intro z h; fin_cases z <;> first | exact False.elim (h 0 rfl) | rfl
  · intro z h; fin_cases z <;> rfl

noncomputable def walk (i : Fin 4) := RecoveryFocus.machine (slots i) (LookupWalk.machine .right)
noncomputable def reset := RecoveryFocus.machine (slots 2) LookupCodeReset.machine

theorem walk_run (i : Fin 4) (d : Store) (count capacity : ℕ)
    (hd : driver d i=ZeroPadding.pad capacity (CompareMachine.word count)) :
    ∃ r,runFrom (walk i) (3*count+2) (cfg (walk i).start d)=some r ∧
      r.final=cfg 3 (positioned d (d.pos+2*count)) ∧ r.steps=3*count+2 := by
  obtain ⟨raw,hr,hrf,hrs⟩ := LookupWalk.walk_run .right d.code d.pos count
  obtain ⟨base,hb,hbf,hbs,_⟩ := ZeroPadding.run_config (LookupWalk.machine .right)
    (![0,capacity] : Fin 2→ℕ) _ _ raw hr
  have he (q : Fin 4) (pos : ℕ) : ZeroPadding.config (![0,capacity] : Fin 2→ℕ)
      (LookupWalk.cfg q d.code pos count 1)=inner q d.code (ZeroPadding.pad capacity (CompareMachine.word count)) pos := by
    apply configuration_ext
    · rfl
    · rfl
    · funext z; fin_cases z
      · exact ZeroPadding.pad_zero _
      · rfl
  rw [he] at hb
  rw [hrf,he] at hbf
  obtain ⟨r,hrr,hrrf,hrrs⟩ := RecoveryFocus.run_config (slots i) (slots_injective i)
    (LookupWalk.machine .right) (cfg (0 : Fin 4) d).heads (cfg (0 : Fin 4) d).tapes _ _ base hb
  have hi := place i (0 : Fin 4) d _ d.pos hd
  rw [show positioned d d.pos=d from rfl] at hi
  rw [hi] at hrr
  refine ⟨r,hrr,?_,hrrs.trans (hbs.trans hrs)⟩
  rw [hrrf,hbf]
  exact place i 3 d _ _ hd

theorem reset_run (d : Store) (hp : d.pos≤2*d.c+1) :
    ∃ r,runFrom reset (3*d.c+4) (cfg reset.start d)=some r ∧
      r.final=cfg 5 (positioned d 0) ∧ r.steps=3*d.c+4 := by
  obtain ⟨base,hb,hbf,hbs⟩ := LookupCodeReset.reset_run d.code d.pos d.c hp
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config (slots 2) (slots_injective 2)
    LookupCodeReset.machine (cfg LookupCodeReset.machine.start d).heads (cfg LookupCodeReset.machine.start d).tapes _ _ base hb
  have hi := place 2 LookupCodeReset.machine.start d _ d.pos rfl
  rw [show positioned d d.pos=d from rfl] at hi
  have hi' : RecoveryFocus.config (slots 2) (cfg LookupCodeReset.machine.start d).heads
      (cfg LookupCodeReset.machine.start d).tapes
      (LookupCodeReset.cfg LookupCodeReset.machine.start d.code d.pos d.c)=cfg LookupCodeReset.machine.start d := hi
  rw [hi'] at hr
  refine ⟨r,hr,?_,hrs.trans hbs⟩
  rw [hrf,hbf]
  exact place 2 5 d _ 0 rfl

def two : Machine 5 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q _=>if h:q.val<2 then some ⟨⟨q.val+1,by omega⟩,
    fun _=>none,fun i=>if i.val=0 then .right else .stay⟩ else none

theorem two_step (q : Fin 2) (d : Store) :
    step two (cfg q.castSucc d)=some (cfg q.succ (positioned d (d.pos+1))) := by
  fin_cases q <;> simp [step,two,cfg]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,positioned,HeadMove.apply] <;> rfl)

theorem two_run (d : Store) :
    ∃ r,runFrom two 2 (cfg 0 d)=some r ∧ r.final=cfg 2 (positioned d (d.pos+2)) ∧ r.steps=2 := by
  have h := (Timed.single (by rfl : two.halted (0 : Fin 3)=false) (two_step 0 d)).trans
    (Timed.single (by rfl : two.halted (1 : Fin 3)=false) (two_step 1 (positioned d (d.pos+1))))
  have he : positioned (positioned d (d.pos+1)) ((positioned d (d.pos+1)).pos+1)=positioned d (d.pos+2) := by simp [positioned,Nat.add_assoc]
  rw [he] at h
  exact h.run (by rfl)

end NearCubicWires.RepairSource.VerifierDecoding.LookupNavigation
