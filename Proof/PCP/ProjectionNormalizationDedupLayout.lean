import Proof.PCP.ProjectionNormalizationBuffers

namespace NearCubicWires.RepairSource.ProjectionNormalization.Dedup
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  source : List Bool
  sourcePos : ℕ
  candidate : List Bool
  candidatePos : ℕ
  out : List Bool
  discard : List Bool
  driverPos : ℕ
  eq : Bool
  found : Bool
  kept : ℕ
  count : ℕ
  cap : ℕ
  scanCap : ℕ
  copyCap : ℕ

def cfg {s : ℕ} (q : Fin s) (d : Store) : Configuration 12 s where
  control := q
  heads := fun i => if i=0 then d.sourcePos else if i=1 then d.candidatePos else
    if i=2 then d.out.length else if i=3 then d.driverPos else if i=10 then d.discard.length else
    if i=11 then d.kept+1 else 0
  tapes := fun i => if i=0 then d.source else if i=1 then d.candidate else if i=2 then d.out else
    if i=3 then CompareMachine.word d.count else if i=4 then [d.eq] else if i=5 then [d.found] else
    if i=6 then List.replicate d.cap false else if i=7 then List.replicate d.scanCap false else
    if i=8 then List.replicate d.scanCap false else if i=9 then List.replicate d.copyCap false else
    if i=10 then d.discard else CompareMachine.word d.kept

def copySlots : Fin 3 → Fin 12 := ![0,1,9]
def scanSlots : Fin 8 → Fin 12 := ![1,0,4,5,6,3,7,8]
def keepSlots : Fin 2 → Fin 12 := ![1,2]
def discardSlots : Fin 2 → Fin 12 := ![1,10]
noncomputable def copyProgram := RecoveryFocus.machine copySlots CandidateCopy.machine
noncomputable def scanProgram := RecoveryFocus.machine scanSlots SharedDriverRestore.machine
noncomputable def keepProgram := RecoveryFocus.machine keepSlots ClauseCopy.machine
noncomputable def discardProgram := RecoveryFocus.machine discardSlots ClauseCopy.machine

def boot : Machine 12 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i=5 then some false else none,fun i => if i=3 then .right else .stay⟩ else none
def bump : Machine 12 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i=11 then some true else none,fun i => if i=11 then .right else .stay⟩ else none

def sizes : Fin 6 → ℕ := ![2,11,SharedDriverRestore.size,9,9,2]
noncomputable def programs (j : Fin 6) : Machine 12 (sizes j) :=
  Fin.cases boot (Fin.cases copyProgram (Fin.cases scanProgram (Fin.cases keepProgram
    (Fin.cases discardProgram (Fin.cases bump (fun i => Fin.elim0 i)))))) j

def next (j : Fin 6) (_ : Fin (sizes j)) (bits : Fin 12 → Bool) : Option (Fin 6) :=
  if j=0 then some 1 else if j=1 then some 2 else if j=2 then
    some (if bits 5 then 4 else 3) else if j=3 then some 5 else none
noncomputable def body := RecoveryCalls.machine sizes programs 0 next
noncomputable def machine := StreamController.machine body 3
noncomputable def atNode (j : Fin 6) (d : Store) := cfg (RecoveryCalls.code sizes j (programs j).start) d
noncomputable def stopped (d : Store) := cfg (RecoveryCalls.controlCode sizes none) d

def bootOut (d : Store) := {d with driverPos:=d.driverPos+1,found:=false}
def bumpOut (d : Store) := {d with kept:=d.kept+1}

theorem boot_run (d : Store) :
    ∃ r,runFrom boot 1 (cfg 0 d)=some r ∧ r.final=cfg 1 (bootOut d) ∧ r.steps=1 := by
  have h : step boot (cfg 0 d)=some (cfg 1 (bootOut d)) := by
    change some (applyAction (cfg 0 d)
      ⟨1,(fun i => if i=5 then some false else none),(fun i => if i=3 then .right else .stay)⟩)=_
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem bump_run (d : Store) :
    ∃ r,runFrom bump 1 (cfg 0 d)=some r ∧ r.final=cfg 1 (bumpOut d) ∧ r.steps=1 := by
  have hw : writeTapeBit (CompareMachine.word d.kept) (d.kept+1) true=CompareMachine.word (d.kept+1) := by
    have h := Streaming.write_append (CompareMachine.word d.kept) true
    simpa [CompareMachine.word,List.replicate_add] using h
  have h : step bump (cfg 0 d)=some (cfg 1 (bumpOut d)) := by
    simp [step,bump,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,bumpOut,HeadMove.apply,Nat.add_assoc]
    · funext i; fin_cases i <;> simp [applyAction,bumpOut,hw]
  exact (Timed.single (by rfl) h).run (by rfl)

theorem copy_place (oldq q : Fin 11) (d : Store) (sp cp : ℕ) (candidate : List Bool) :
    RecoveryFocus.config copySlots (cfg oldq d).heads (cfg oldq d).tapes
      (CandidateCopy.cfg q d.source sp candidate cp d.copyCap)=
      cfg q {d with sourcePos:=sp,candidate:=candidate,candidatePos:=cp} := by
  apply TransitionEvent.focused_eq copySlots (by decide) (cfg oldq d)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h
    have h0 : i≠0 := fun hi => h 0 hi.symm
    have h1 : i≠1 := fun hi => h 1 hi.symm
    simp [cfg,h0,h1]
  · intro i h
    have h1 : i≠1 := fun hi => h 1 hi.symm
    simp [cfg,h1]

theorem scan_place (oldq q : Fin SharedDriverRestore.size) (d : Store) (eq found : Bool) :
    RecoveryFocus.config scanSlots (cfg oldq d).heads (cfg oldq d).tapes
      (SharedDriverRestore.cfg q d.candidate d.source d.candidatePos d.sourcePos eq found
        d.cap d.count d.driverPos d.scanCap d.scanCap)=cfg q {d with eq:=eq,found:=found} := by
  apply TransitionEvent.focused_eq scanSlots (by decide) (cfg oldq d)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; rfl
  · intro i h
    have h4 : i≠4 := fun hi => h 2 hi.symm
    have h5 : i≠5 := fun hi => h 3 hi.symm
    simp [cfg,h4,h5]

theorem keep_place (oldq q : Fin 9) (d : Store) (cp : ℕ) (out : List Bool) :
    RecoveryFocus.config keepSlots (cfg oldq d).heads (cfg oldq d).tapes
      (ClauseCopy.cfg q d.candidate cp out)=cfg q {d with candidatePos:=cp,out:=out} := by
  apply TransitionEvent.focused_eq keepSlots (by decide) (cfg oldq d)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h
    have h1 : i≠1 := fun hi => h 0 hi.symm
    have h2 : i≠2 := fun hi => h 1 hi.symm
    simp [cfg,h1,h2]
  · intro i h
    have h2 : i≠2 := fun hi => h 1 hi.symm
    simp [cfg,h2]

theorem discard_place (oldq q : Fin 9) (d : Store) (cp : ℕ) (out : List Bool) :
    RecoveryFocus.config discardSlots (cfg oldq d).heads (cfg oldq d).tapes
      (ClauseCopy.cfg q d.candidate cp out)=cfg q {d with candidatePos:=cp,discard:=out} := by
  apply TransitionEvent.focused_eq discardSlots (by decide) (cfg oldq d)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h
    have h1 : i≠1 := fun hi => h 0 hi.symm
    have h10 : i≠10 := fun hi => h 1 hi.symm
    simp [cfg,h1,h10]
  · intro i h
    have h10 : i≠10 := fun hi => h 1 hi.symm
    simp [cfg,h10]

end NearCubicWires.RepairSource.ProjectionNormalization.Dedup
