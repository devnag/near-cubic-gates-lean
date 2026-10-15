import Proof.PCP.VerifierLookupSelectLoop

/-! The literal record walk consumes existing physical dimensions. Its
constant two-cell move and dimension walks preserve every other tape. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupSkip
open LocalBitMultitape RepairOrdinary RecoveryExecution LookupSelect
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advance (d : Store) (n : ℕ) : Store := {d with pos:=d.pos+n}

def two : Machine 7 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q _=>if h:q.val<2 then some ⟨⟨q.val+1,by omega⟩,
    fun _=>none,fun i=>if i.val=0 then .right else .stay⟩ else none

theorem two_step (q : Fin 2) (d : Store) :
    step two (cfg q.castSucc d)=some (cfg q.succ (advance d 1)) := by
  fin_cases q <;> simp [step,two,cfg]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,advance,HeadMove.apply])

theorem two_run (d : Store) :
    ∃ r,runFrom two 2 (cfg 0 d)=some r ∧ r.final=cfg 2 (advance d 2) ∧ r.steps=2 := by
  have h := (Timed.single (by rfl : two.halted (0 : Fin 3)=false) (two_step 0 d)).trans
    (Timed.single (by rfl : two.halted (1 : Fin 3)=false) (two_step 1 (advance d 1)))
  have he : advance (advance d 1) 1=advance d 2 := by simp [advance,Nat.add_assoc]
  rw [he] at h
  exact h.run (by rfl)

def walkSlots (second : Bool) : Fin 2 → Fin 7 := if second then ![0,6] else ![0,5]
noncomputable def walkProgram (second : Bool) := RecoveryFocus.machine (walkSlots second) (LookupWalk.machine .right)

def walkCfg (q : Fin 4) (source driver : List Bool) (pos : ℕ) : Configuration 2 4 :=
  ⟨q,![pos,1],![source,driver]⟩

theorem walk_place (second : Bool) (q : Fin 4) (d : Store) (driver : List Bool) (n : ℕ)
    (hd : (if second then d.driverB else d.driverA)=driver) :
    RecoveryFocus.config (walkSlots second) (cfg q d).heads (cfg q d).tapes
      (walkCfg q d.source driver (d.pos+n))=cfg q (advance d n) := by
  apply TransitionEvent.focused_eq (walkSlots second) (by cases second <;> decide) (cfg q d)
  · rfl
  · intro i; cases second <;> fin_cases i <;> rfl
  · intro i; cases second <;> fin_cases i <;> first | rfl | exact hd.symm
  · intro i hi; cases second <;> fin_cases i <;> first | exact False.elim (hi 0 rfl) | rfl
  · intro i hi; rfl

theorem walk_run (second : Bool) (d : Store) (n capacity : ℕ)
    (hd : (if second then d.driverB else d.driverA)=ZeroPadding.pad capacity (CompareMachine.word n)) :
    ∃ r,runFrom (walkProgram second) (3*n+2) (cfg (walkProgram second).start d)=some r ∧
      r.final=cfg 3 (advance d (2*n)) ∧ r.steps=3*n+2 := by
  obtain ⟨raw,hr,hrf,hrs⟩ := LookupWalk.walk_run .right d.source d.pos n
  obtain ⟨base,hb,hbf,hbs,_⟩ := ZeroPadding.run_config (LookupWalk.machine .right)
    (![0,capacity] : Fin 2→ℕ) _ _ raw hr
  have he (q : Fin 4) (pos : ℕ) : ZeroPadding.config (![0,capacity] : Fin 2→ℕ)
      (LookupWalk.cfg q d.source pos n 1)=walkCfg q d.source (ZeroPadding.pad capacity (CompareMachine.word n)) pos := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i
      · exact ZeroPadding.pad_zero _
      · rfl
  rw [he] at hb
  rw [hrf,he] at hbf
  obtain ⟨r,hrr,hrrf,hrrs⟩ := RecoveryFocus.run_config (walkSlots second) (by cases second <;> decide)
    (LookupWalk.machine .right) (cfg (0 : Fin 4) d).heads (cfg (0 : Fin 4) d).tapes _ _ base hb
  have hi := walk_place second 0 d _ 0 hd
  simp only [Nat.add_zero,advance] at hi
  rw [hi] at hrr
  refine ⟨r,hrr,?_,hrrs.trans (hbs.trans hrs)⟩
  rw [hrrf,hbf]
  exact walk_place second 3 d _ (2*n) hd

end NearCubicWires.RepairSource.VerifierDecoding.LookupSkip
