import Proof.Supplier.RowTupleCursorEquation

/-! Paid per-tuple cleanup clears only the coordinate counter, occurrence
stream and occurrence count, and restores their consumer heads. All other
tapes and live cursors are retained. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorErase
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 3→Fin 48 := ![15,23,24]
def eraseSlots : Fin 5→Fin 48 := ![15,23,24,33,34]
theorem injective : Function.Injective eraseSlots := by decide
def eraseInput (F : ℕ) (backing : Fin 3→List Bool) : Fin 5→List Bool :=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) backing (fun _=>List.replicate F true))
    (fun _=>List.replicate (F+1) false)
noncomputable def cleared (F : ℕ) (src : Fin 48→List Bool) :=
  install eraseSlots src (eraseInput F (fun _=>List.replicate F false))
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 3)

theorem erase_run (F : ℕ) (heads : Fin 48→ℕ) (src : Fin 48→List Bool)
    (hh : ∀ i,heads (eraseSlots i)=0) (ht : ∀ i,(src (workSlots i)).length≤F)
    (hd : src 33=List.replicate F true) (hl : src 34=List.replicate (F+1) false) :
    ∃ r,runFrom erase (2*F+4) ⟨erase.start,heads,src⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=cleared F src ∧ r.steps=2*F+4 := by
  have h:=RecoveryScratchErase.erase_ready F (F+1) (fun i=>src (workSlots i)) ht
  simp only [max_self] at h
  apply h.focus_at eraseSlots injective heads src _ hh
  intro i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hd
  · exact hl

def shift (forward : Bool) : Machine 48 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if i=15 ∨ i=24 then (if forward then .right else .left) else .stay⟩ else none
def moved (forward : Bool) (heads : Fin 48→ℕ) : Fin 48→ℕ := fun i=>
  if i=15 ∨ i=24 then (if forward then heads i+1 else heads i-1) else heads i

theorem shift_run (forward : Bool) (heads : Fin 48→ℕ) (src : Fin 48→List Bool) :
    ∃ r,runFrom (shift forward) 1 ⟨0,heads,src⟩=some r ∧
      r.final=⟨1,moved forward heads,src⟩ ∧ r.steps=1 := by
  apply Timed.run (Timed.single (by rfl) ?_) (by rfl)
  simp only [step,shift,Fin.val_zero,↓reduceIte,Option.map_some,Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi:i=15 ∨ i=24
    · cases forward <;> simp [applyAction,moved,hi,HeadMove.apply]
    · simp [applyAction,moved,hi,HeadMove.apply]
  · rfl

noncomputable def first := Composition.machine (shift false) erase
noncomputable def machine := Composition.machine first (shift true)

theorem clear_run (F : ℕ) (heads : Fin 48→ℕ) (src : Fin 48→List Bool)
    (h15:heads 15=1) (h24:heads 24=1) (h23:heads 23=0) (h33:heads 33=0) (h34:heads 34=0)
    (ht : ∀ i,(src (workSlots i)).length≤F)
    (hd : src 33=List.replicate F true) (hl : src 34=List.replicate (F+1) false) :
    ∃ r,runFrom machine (2*F+8) ⟨machine.start,heads,src⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=cleared F src ∧ r.steps=2*F+8 := by
  obtain ⟨a,ha,af,as⟩:=shift_run false heads src
  obtain ⟨b,hb,bh,bt,bs⟩:=erase_run F (moved false heads) src (by
    intro i; fin_cases i <;> simp [eraseSlots,moved,h15,h24,h23,h33,h34]) ht hd hl
  have hab : (⟨erase.start,moved false heads,src⟩ : Configuration 48 _)=
      Composition.restart a.final erase.start := by rw [af]; rfl
  rw [hab] at hb
  have one:=Composition.run_join (shift false) erase _ _ _ a b ha hb
  obtain ⟨c,hc,cf,cs⟩:=shift_run true (moved false heads) (cleared F src)
  have hbc : (⟨(shift true).start,moved false heads,cleared F src⟩ : Configuration 48 _)=
      Composition.restart (Composition.joinedReceipt a b).final (shift true).start := by
    apply configuration_ext
    · rfl
    · exact bh.symm
    · exact bt.symm
  change runFrom (shift true) 1 ⟨(shift true).start,moved false heads,cleared F src⟩=some c at hc
  rw [hbc] at hc
  have whole:=Composition.run_join first (shift true) _ _ _ (Composition.joinedReceipt a b) c one hc
  rw [show (1+1+(2*F+4))+1+1=2*F+8 by omega] at whole
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,whole,?_,?_,?_⟩
  · change c.final.heads=_
    rw [cf]
    funext i
    by_cases hi:i=15 ∨ i=24
    · rcases hi with rfl|rfl <;> simp [moved,h15,h24]
    · simp [moved,hi]
  · change c.final.tapes=_
    rw [cf]
  · change (a.steps+1+b.steps)+1+c.steps=_
    rw [as,bs,cs]
    omega

end NearCubicWires.RepairOrdinary.RowTupleCursorErase
