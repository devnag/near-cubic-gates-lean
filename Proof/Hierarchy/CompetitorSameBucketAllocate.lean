import Proof.Hierarchy.CompetitorSameBucketFunding

/-! Allocate the actual scalar and packet scratch from their retained C/D
raw drivers. All original 398 tapes/cursors are preserved. The enclosing
cold caller supplies those drivers by its already executed fields theorem. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdAllocate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarSlots (j : Fin 40) : Fin 442 :=
  if j.val<38 then ⟨398+j.val,by omega⟩ else if j=38 then 358 else 436
def packetSlots : Fin 6 → Fin 442 := ![437,438,439,440,132,441]
theorem scalar_injective : Function.Injective scalarSlots := by decide
theorem packet_injective : Function.Injective packetSlots := by decide

def eraseInput (n cap : ℕ) : Fin (n+1+1) → List Bool :=
  Fin.addCases (Fin.addCases (fun _ : Fin n => []) (fun _ : Fin 1 => List.replicate cap true)) (fun _ : Fin 1 => [])
def eraseOutput (n cap : ℕ) : Fin (n+1+1) → List Bool :=
  Fin.addCases (Fin.addCases (fun _ : Fin n => List.replicate cap false) (fun _ : Fin 1 => List.replicate cap true))
    (fun _ : Fin 1 => List.replicate (cap+1) false)
theorem erase_ready (n cap : ℕ) : ReadyRun (RecoveryScratchErase.resetMachine n) (2*cap+4) (eraseInput n cap) (eraseOutput n cap) := by
  unfold eraseInput eraseOutput
  simpa only [Nat.zero_max,List.replicate_zero] using RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin n => []) (by simp)

noncomputable def first:=RecoveryFocus.machine scalarSlots (RecoveryScratchErase.resetMachine 38)
noncomputable def last:=RecoveryFocus.machine packetSlots (RecoveryScratchErase.resetMachine 4)
noncomputable def machine:=Composition.machine first last
def budget (c d : ℕ) := (2*c+4)+1+(2*d+4)
def oldTapes (tapes : Fin 398 → List Bool) : Fin 442 → List Bool := Fin.addCases (m := 398) (n := 44) (motive := fun _ => List Bool) tapes (fun _ : Fin 44 => [])
def oldHeads (heads : Fin 398 → ℕ) : Fin 442 → ℕ := Fin.addCases (m := 398) (n := 44) (motive := fun _ => ℕ) heads (fun _ : Fin 44 => 0)
noncomputable def output (c d : ℕ) (tapes : Fin 398 → List Bool) :=
  install packetSlots (install scalarSlots (oldTapes tapes) (eraseOutput 38 c)) (eraseOutput 4 d)
def cfg {s : ℕ} (q : Fin s) (heads : Fin 398 → ℕ) (tapes : Fin 398 → List Bool) : Configuration 442 s :=
  ⟨q,oldHeads heads,oldTapes tapes⟩

theorem selected_scalar (c : ℕ) (heads : Fin 398 → ℕ) (tapes : Fin 398 → List Bool)
    (ht : tapes 358=List.replicate c true) (hh : heads 358=0) :
    (∀ j,oldHeads heads (scalarSlots j)=0) ∧ (∀ j,oldTapes tapes (scalarSlots j)=eraseInput 38 c j) := by
  constructor
  · intro j; fin_cases j
    all_goals first | exact hh | rfl
  · intro j; fin_cases j
    all_goals first | exact ht | rfl

theorem packet_avoids (j : Fin 6) (i : Fin 40) : scalarSlots i≠packetSlots j := by
  fin_cases j <;> fin_cases i <;> decide

theorem selected_packet (c d : ℕ) (heads : Fin 398 → ℕ) (tapes : Fin 398 → List Bool)
    (ht : tapes 132=List.replicate d true) (hh : heads 132=0) :
    (∀ j,oldHeads heads (packetSlots j)=0) ∧
    (∀ j,install scalarSlots (oldTapes tapes) (eraseOutput 38 c) (packetSlots j)=eraseInput 4 d j) := by
  constructor
  · intro j; fin_cases j
    all_goals first | exact hh | rfl
  · intro j
    rw [install_other scalarSlots (oldTapes tapes) (eraseOutput 38 c) (packetSlots j) (packet_avoids j)]
    fin_cases j
    all_goals first | exact ht | rfl

theorem allocate_run (c d : ℕ) (heads : Fin 398 → ℕ) (tapes : Fin 398 → List Bool)
    (cT : tapes 358=List.replicate c true) (cH : heads 358=0)
    (dT : tapes 132=List.replicate d true) (dH : heads 132=0) :
    ∃ actual,runFrom machine (budget c d) (cfg machine.start heads tapes)=some actual ∧
      actual.final.heads=oldHeads heads ∧ actual.final.tapes=output c d tapes ∧ actual.steps=budget c d := by
  obtain ⟨scalar,hs,st,sh,ss⟩:=erase_ready 38 c
  have selected:=selected_scalar c heads tapes cT cH
  have hi : RecoveryFocus.config scalarSlots (oldHeads heads) (oldTapes tapes)
      (initialConfiguration (RecoveryScratchErase.resetMachine 38) (eraseInput 38 c))=
      cfg first.start heads tapes := by
    exact WilliamsSourceCrop.focus_same scalarSlots (cfg first.start heads tapes) _ selected.1 selected.2
  obtain ⟨prepared,hp,pf,ps⟩:=RecoveryFocus.run_config scalarSlots scalar_injective (RecoveryScratchErase.resetMachine 38)
    (oldHeads heads) (oldTapes tapes) _ _ scalar hs
  rw [hi] at hp
  have ph : prepared.final.heads=oldHeads heads := by
    rw [pf]
    funext i
    simp only [RecoveryFocus.config]
    cases he : RecoveryFocus.pick scalarSlots i with
    | none => rfl
    | some j =>
      have hj:=RecoveryFocus.slot_of_pick scalarSlots he
      subst i
      exact (sh j).trans (selected.1 j).symm
  have pt : prepared.final.tapes=install scalarSlots (oldTapes tapes) (eraseOutput 38 c) := by
    rw [pf]
    funext i
    simp only [RecoveryFocus.config,st,RecoveryRootRound.install]
    cases RecoveryFocus.pick scalarSlots i <;> rfl
  obtain ⟨packet,hd,dt,dh,ds⟩:=erase_ready 4 d
  have next:=selected_packet c d heads tapes dT dH
  have hj : RecoveryFocus.config packetSlots prepared.final.heads prepared.final.tapes
      (initialConfiguration (RecoveryScratchErase.resetMachine 4) (eraseInput 4 d))=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j; rw [ph]; exact next.1 j
    · intro j; rw [pt]; exact next.2 j
  obtain ⟨final,hf,ff,fs⟩:=RecoveryFocus.run_config packetSlots packet_injective (RecoveryScratchErase.resetMachine 4)
    prepared.final.heads prepared.final.tapes _ _ packet hd
  rw [hj] at hf
  have joined:=Composition.run_join first last _ _ _ prepared final hp hf
  refine ⟨Composition.joinedReceipt prepared final,joined,?_,?_,?_⟩
  · change final.final.heads=_
    rw [ff]
    funext i
    simp only [RecoveryFocus.config,ph]
    cases he : RecoveryFocus.pick packetSlots i with
    | none => rfl
    | some j =>
      have hj:=RecoveryFocus.slot_of_pick packetSlots he
      subst i
      exact (dh j).trans (next.1 j).symm
  · change final.final.tapes=_
    rw [ff]
    funext i
    simp only [RecoveryFocus.config,dt,pt,output,RecoveryRootRound.install]
    cases RecoveryFocus.pick packetSlots i <;> rfl
  · change prepared.steps+1+final.steps=budget c d
    rw [ps,fs,ss,ds]
    rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdAllocate
