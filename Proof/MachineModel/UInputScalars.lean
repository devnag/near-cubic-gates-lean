import Proof.MachineModel.UInputFields

/-! Actual scalar preparation from the retained outer input and its extracted
x/B frames. Only logarithmic counts are multiplied in unary; the potentially
large B is normalized and compared in short binary fields. -/
namespace NearCubicWires.RepairOrdinary.UInputScalars
open LocalBitMultitape RecoveryRootRound ClockDyadicLedger ClockUniversalBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 40 → List Bool
def numericSlots : Fin 14 → Fin 40 := ![3,4,5,6,7,8,9,10,11,12,13,14,0,15]
theorem numeric_injective : Function.Injective numericSlots := by decide
def boundSlots : Fin 12 → Fin 40 := ![10,2,16,17,18,9,19,20,21,22,23,24]
theorem bound_injective : Function.Injective boundSlots := by decide
def countSlots : Fin 4 → Fin 40 := ![25,26,1,27]
theorem count_injective : Function.Injective countSlots := by decide
def lowerSlots : Fin 12 → Fin 40 := ![10,25,28,29,30,16,31,32,33,34,35,36]
theorem lower_injective : Function.Injective lowerSlots := by decide
def andSlots : Fin 3 → Fin 40 := ![24,36,37]
theorem and_injective : Function.Injective andSlots := by decide
def logSlots : Fin 3 → Fin 40 := ![3,38,39]
theorem log_injective : Function.Injective logSlots := by decide
noncomputable def numericPhase := RecoveryFocus.machine numericSlots ClockPreparation.machine
noncomputable def boundPhase := RecoveryFocus.machine boundSlots ClockBoundGuard.machine
noncomputable def countPhase := RecoveryFocus.machine countSlots HierarchyInputLength.machine
noncomputable def lowerPhase := RecoveryFocus.machine lowerSlots ClockBoundGuard.machine
noncomputable def andPhase := RecoveryFocus.machine andSlots ClockBoundGuard.conjunction
noncomputable def logPhase := RecoveryFocus.machine logSlots ClockFloorLog.machine

def input (raw x bound : List Bool) : Store := fun i =>
  if i.val=0 then frame raw else if i.val=1 then frame x else if i.val=2 then frame bound else []
def normalized (raw bound : List Bool) := ClockBoundGuard.normalized (width raw.length) bound
def upperFlag (raw bound : List Bool) := ClockBoundGuard.accepted (width raw.length) bound (limitWord raw.length)
def lowerFlag (raw x bound : List Bool) := ClockBoundGuard.accepted (width raw.length)
  (ClockBinary.word x.length) (normalized raw bound)
def flag (raw x bound : List Bool) := upperFlag raw bound && lowerFlag raw x bound

def afterNumeric (raw x bound : List Bool) (carry reset degree : ℕ) : Store := fun i =>
  if i.val=3 then (ClockPreparation.output raw carry reset degree) 0 else
  if i.val=4 then (ClockPreparation.output raw carry reset degree) 1 else
  if i.val=5 then (ClockPreparation.output raw carry reset degree) 2 else
  if i.val=6 then (ClockPreparation.output raw carry reset degree) 3 else
  if i.val=7 then (ClockPreparation.output raw carry reset degree) 4 else
  if i.val=8 then (ClockPreparation.output raw carry reset degree) 5 else
  if i.val=9 then (ClockPreparation.output raw carry reset degree) 6 else
  if i.val=10 then (ClockPreparation.output raw carry reset degree) 7 else
  if i.val=11 then (ClockPreparation.output raw carry reset degree) 8 else
  if i.val=12 then (ClockPreparation.output raw carry reset degree) 9 else
  if i.val=13 then (ClockPreparation.output raw carry reset degree) 10 else
  if i.val=14 then (ClockPreparation.output raw carry reset degree) 11 else
  if i.val=15 then (ClockPreparation.output raw carry reset degree) 13 else
  input raw x bound i

def afterBound (raw x bound : List Bool) (carry reset degree : ℕ) : Store := fun i =>
  if i.val=16 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 2 else
  if i.val=17 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 3 else
  if i.val=18 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 4 else
  if i.val=19 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 6 else
  if i.val=20 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 7 else
  if i.val=21 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 8 else
  if i.val=22 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 9 else
  if i.val=23 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 10 else
  if i.val=24 then (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length)) 11 else
  afterNumeric raw x bound carry reset degree i

def afterCount (raw x bound : List Bool) (carry reset degree cap scratch : ℕ) : Store := fun i =>
  if i.val=25 then (![frame (ClockBinary.word x.length),List.replicate cap false,frame x,List.replicate scratch false]) 0 else
  if i.val=26 then (![frame (ClockBinary.word x.length),List.replicate cap false,frame x,List.replicate scratch false]) 1 else
  if i.val=27 then (![frame (ClockBinary.word x.length),List.replicate cap false,frame x,List.replicate scratch false]) 3 else
  afterBound raw x bound carry reset degree i

def afterLower (raw x bound : List Bool) (carry reset degree cap scratch : ℕ) : Store := fun i =>
  if i.val=28 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 2 else
  if i.val=29 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 3 else
  if i.val=30 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 4 else
  if i.val=31 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 6 else
  if i.val=32 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 7 else
  if i.val=33 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 8 else
  if i.val=34 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 9 else
  if i.val=35 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 10 else
  if i.val=36 then (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound)) 11 else
  afterCount raw x bound carry reset degree cap scratch i

def output (raw x bound : List Bool) (carry reset degree cap scratch : ℕ) : Store := fun i =>
  if i.val=37 then (![[upperFlag raw bound],[lowerFlag raw x bound],[flag raw x bound]]) 2 else
  afterLower raw x bound carry reset degree cap scratch i

theorem numeric_phase (raw x bound : List Bool) (hn : 0 < raw.length) :
    ∃ carry reset degree, ClockJoin.ReadyRun numericPhase (ClockPreparation.budget raw)
      (input raw x bound) (afterNumeric raw x bound carry reset degree) := by
  obtain ⟨carry,reset,degree,_,_,_,h⟩ := ClockPreparation.prepare_run raw hn
  have hfocus := h.focus numericSlots numeric_injective (input raw x bound)
    (by intro j; fin_cases j <;> rfl)
  have ho : install numericSlots (input raw x bound) (ClockPreparation.output raw carry reset degree)=
      afterNumeric raw x bound carry reset degree := by
    apply HierarchyWidth.install_eq _ numeric_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [numericSlots,afterNumeric]
  rw [ho] at hfocus
  exact ⟨carry,reset,degree,hfocus⟩

theorem bound_phase (raw x bound : List Bool) (carry reset degree : ℕ) :
    ClockJoin.ReadyRun boundPhase (16*(width raw.length+1))
      (afterNumeric raw x bound carry reset degree) (afterBound raw x bound carry reset degree) := by
  have h := (ClockBoundGuard.guard_ready (width raw.length) bound (limitWord raw.length)).focus
    boundSlots bound_injective (afterNumeric raw x bound carry reset degree)
    (by intro j; fin_cases j <;> rfl)
  have ho : install boundSlots (afterNumeric raw x bound carry reset degree)
      (ClockBoundGuard.output (width raw.length) bound (limitWord raw.length))=
      afterBound raw x bound carry reset degree := by
    apply HierarchyWidth.install_eq _ bound_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [boundSlots,afterBound]
  rw [ho] at h
  exact h

theorem count_phase (raw x bound : List Bool) (carry reset degree : ℕ) :
    ∃ cap scratch, ClockJoin.ReadyRun countPhase (HierarchyInputLength.budget x)
      (afterBound raw x bound carry reset degree) (afterCount raw x bound carry reset degree cap scratch) := by
  obtain ⟨cap,scratch,_,_,r,hr,h0,h1,h2,h3,hh,hs⟩ := HierarchyInputLength.count_run x
  have ht : r.final.tapes=![frame (ClockBinary.word x.length),List.replicate cap false,frame x,
      List.replicate scratch false] := by
    funext i; fin_cases i <;> simp [h0,h1,h2,h3]
  have ready : ClockJoin.ReadyRun HierarchyInputLength.machine (HierarchyInputLength.budget x)
      (HierarchyInputLength.input x) _ := ⟨r,hr,ht,hh,hs⟩
  have h := ready.focus countSlots count_injective (afterBound raw x bound carry reset degree)
    (by intro j; fin_cases j <;> rfl)
  have ho : install countSlots (afterBound raw x bound carry reset degree)
      ![frame (ClockBinary.word x.length),List.replicate cap false,frame x,List.replicate scratch false]=
      afterCount raw x bound carry reset degree cap scratch := by
    apply HierarchyWidth.install_eq _ count_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [countSlots,afterCount]
  rw [ho] at h
  exact ⟨cap,scratch,h⟩

theorem lower_phase (raw x bound : List Bool) (carry reset degree cap scratch : ℕ) :
    ClockJoin.ReadyRun lowerPhase (16*(width raw.length+1))
      (afterCount raw x bound carry reset degree cap scratch)
      (afterLower raw x bound carry reset degree cap scratch) := by
  have h := (ClockBoundGuard.guard_ready (width raw.length) (ClockBinary.word x.length) (normalized raw bound)).focus
    lowerSlots lower_injective (afterCount raw x bound carry reset degree cap scratch)
    (by intro j; fin_cases j <;> rfl)
  have ho : install lowerSlots (afterCount raw x bound carry reset degree cap scratch)
      (ClockBoundGuard.output (width raw.length) (ClockBinary.word x.length) (normalized raw bound))=
      afterLower raw x bound carry reset degree cap scratch := by
    apply HierarchyWidth.install_eq _ lower_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [lowerSlots,afterLower]
  rw [ho] at h
  exact h

theorem and_phase (raw x bound : List Bool) (carry reset degree cap scratch : ℕ) :
    ClockJoin.ReadyRun andPhase 1 (afterLower raw x bound carry reset degree cap scratch)
      (output raw x bound carry reset degree cap scratch) := by
  have h := (ClockBoundGuard.conjunction_ready (upperFlag raw bound) (lowerFlag raw x bound)).focus
    andSlots and_injective (afterLower raw x bound carry reset degree cap scratch)
    (by intro j; fin_cases j <;> rfl)
  have ho : install andSlots (afterLower raw x bound carry reset degree cap scratch)
      ![[upperFlag raw bound],[lowerFlag raw x bound],[flag raw x bound]]=
      output raw x bound carry reset degree cap scratch := by
    apply HierarchyWidth.install_eq _ and_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [andSlots,output]
  dsimp only [flag] at ho
  rw [ho] at h
  exact h

noncomputable def first := Composition.machine numericPhase boundPhase
noncomputable def second := Composition.machine first countPhase
noncomputable def third := Composition.machine second lowerPhase
noncomputable def machine := Composition.machine third andPhase
def budget (raw x : List Bool) := ClockPreparation.budget raw+HierarchyInputLength.budget x+
  32*(width raw.length+1)+5

theorem prepare_ready (raw x bound : List Bool) (hn : 0 < raw.length) :
    ∃ carry reset degree cap scratch, ClockJoin.ReadyRun machine (budget raw x)
      (input raw x bound) (output raw x bound carry reset degree cap scratch) := by
  obtain ⟨carry,reset,degree,hnumeric⟩ := numeric_phase raw x bound hn
  have hfirst := ClockJoin.join numericPhase boundPhase _ _ _ _ _ hnumeric (bound_phase raw x bound carry reset degree)
  obtain ⟨cap,scratch,hcount⟩ := count_phase raw x bound carry reset degree
  have hsecond := ClockJoin.join first countPhase _ _ _ _ _ hfirst hcount
  have hthird := ClockJoin.join second lowerPhase _ _ _ _ _ hsecond (lower_phase raw x bound carry reset degree cap scratch)
  have h := ClockJoin.join third andPhase _ _ _ _ _ hthird (and_phase raw x bound carry reset degree cap scratch)
  have he : ClockPreparation.budget raw+1+16*(width raw.length+1)+1+HierarchyInputLength.budget x+1+
      16*(width raw.length+1)+1+1=budget raw x := by dsimp [budget]; omega
  rw [he] at h
  exact ⟨carry,reset,degree,cap,scratch,h⟩

end NearCubicWires.RepairOrdinary.UInputScalars
