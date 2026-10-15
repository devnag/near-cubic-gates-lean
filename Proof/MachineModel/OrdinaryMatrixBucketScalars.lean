import Proof.MachineModel.OrdinaryMatrixBucketWorkspace

/-! Six executed framed copies install the exact initial bucket boundary,
rank and coordinate words into the allocated key-scanner bank. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketScalars
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceSlot : Fin 6 → Fin 34 := ![24,25,24,26,26,26]
def targetSlot : Fin 6 → Fin 34 := ![0,1,4,16,17,18]
def width (H M : ℕ) : Fin 6 → ℕ := ![H,H,H,M,M,M]
def value (B : ℕ) : Fin 6 → ℕ := ![0,B,0,0,0,0]
def slots (j : Fin 6) : Fin 4 → Fin 34 := ![sourceSlot j,targetSlot j,31,32]
theorem slots_injective (j : Fin 6) : Function.Injective (slots j) := by fin_cases j <;> decide
def pick (j : Fin 6) (i : Fin 34) : Option (Fin 4) :=
  if i=sourceSlot j then some 0 else if i=targetSlot j then some 1
  else if i=31 then some 2 else if i=32 then some 3 else none

theorem pick_slots (j : Fin 6) (i : Fin 34) : RecoveryFocus.pick (slots j) i=pick j i := by
  classical
  by_cases h : ∃ k,slots j k=i
  · obtain ⟨k,rfl⟩ := h
    rw [RecoveryFocus.pick_slot (slots j) (slots_injective j)]
    fin_cases k <;> fin_cases j <;> rfl
  · have hs : i≠sourceSlot j := by intro he; exact h ⟨0,he.symm⟩
    have ht : i≠targetSlot j := by intro he; exact h ⟨1,he.symm⟩
    have h31 : i≠31 := by intro he; exact h ⟨2,he.symm⟩
    have h32 : i≠32 := by intro he; exact h ⟨3,he.symm⟩
    simp [RecoveryFocus.pick,h,pick,hs,ht,h31,h32]

def data (D H M B count done : ℕ) : Fin 34 → List Bool := fun i =>
  if i=0 ∧ 0<done then scalar D H 0 else if i=1 ∧ 1<done then scalar D H B
  else if i=4 ∧ 2<done then scalar D H 0 else if i=16 ∧ 3<done then scalar D M 0
  else if i=17 ∧ 4<done then scalar D M 0 else if i=18 ∧ 5<done then scalar D M 0
  else MatrixBucketWorkspace.output D H M B count i
noncomputable def call (j : Fin 6) : Machine 34 6 := RecoveryFocus.machine (slots j) copyMachine
noncomputable def tail4 := Composition.machine (call 4) (call 5)
noncomputable def tail3 := Composition.machine (call 3) tail4
noncomputable def firstTail := Composition.machine (call 1) (call 2)
noncomputable def first := Composition.machine (call 0) firstTail
noncomputable def machine := Composition.machine first tail3

theorem step_ready (D H M B count : ℕ) (hH : 4*H+3 ≤ D) (hM : 4*M+3 ≤ D) (j : Fin 6) :
    ReadyRun (call j) (8*width H M j+8) (data D H M B count j.val) (data D H M B count (j.val+1)) := by
  have hwidth : 4*width H M j+3 ≤ D := by fin_cases j <;> first | exact hH | exact hM
  have base := MatrixScoreInitialize.native_copy D (width H M j) (value B j) hwidth
  have hi : ∀ i,data D H M B count j.val (slots j i)=
      (![frame (binary (width H M j) (value B j)),zeros D,zeros D,zeros D] : Fin 4 → List Bool) i := by
    intro i
    fin_cases j <;> fin_cases i <;> simp [data,slots,sourceSlot,targetSlot,width,value,MatrixBucketWorkspace.output,zeros]
  have focused := base.focus (slots j) (slots_injective j) (data D H M B count j.val) hi
  have he : install (slots j) (data D H M B count j.val)
      ![frame (binary (width H M j) (value B j)),scalar D (width H M j) (value B j),zeros D,zeros D]=
        data D H M B count (j.val+1) := by
    funext i
    fin_cases j <;> fin_cases i <;>
      simp [install,pick_slots,pick,data,sourceSlot,targetSlot,width,value,MatrixBucketWorkspace.output,zeros]
  rw [he] at focused
  exact focused

theorem bounded_ready (D H M B count : ℕ) (hH : 4*H+3 ≤ D) (hM : 4*M+3 ≤ D) (j : Fin 6) :
    ClockJoin.ReadyRun (call j) (8*width H M j+8) (data D H M B count j.val) (data D H M B count (j.val+1)) := by
  obtain ⟨actual,ha,atapes,ah,as⟩ := step_ready D H M B count hH hM j
  exact ⟨actual,ha,atapes,ah,as.le⟩

theorem first_ready (D H M B count : ℕ) (hH : 4*H+3 ≤ D) (hM : 4*M+3 ≤ D) :
    ClockJoin.ReadyRun first (24*H+26) (data D H M B count 0) (data D H M B count 3) := by
  have h0 := bounded_ready D H M B count hH hM 0
  have h1 := bounded_ready D H M B count hH hM 1
  have h2 := bounded_ready D H M B count hH hM 2
  have tail := ClockJoin.join (call 1) (call 2) _ _ _ _ _ h1 h2
  have whole := ClockJoin.join (call 0) firstTail _ _ _ _ _ h0 tail
  change ClockJoin.ReadyRun first ((8*H+8)+1+((8*H+8)+1+(8*H+8)))
    (data D H M B count 0) (data D H M B count 3) at whole
  have hb : (8*H+8)+1+((8*H+8)+1+(8*H+8))=24*H+26 := by ring
  rw [hb] at whole
  exact whole

theorem last_ready (D H M B count : ℕ) (hH : 4*H+3 ≤ D) (hM : 4*M+3 ≤ D) :
    ClockJoin.ReadyRun tail3 (24*M+26) (data D H M B count 3) (data D H M B count 6) := by
  have h3 := bounded_ready D H M B count hH hM 3
  have h4 := bounded_ready D H M B count hH hM 4
  have h5 := bounded_ready D H M B count hH hM 5
  have tail := ClockJoin.join (call 4) (call 5) _ _ _ _ _ h4 h5
  have whole := ClockJoin.join (call 3) tail4 _ _ _ _ _ h3 tail
  change ClockJoin.ReadyRun tail3 ((8*M+8)+1+((8*M+8)+1+(8*M+8)))
    (data D H M B count 3) (data D H M B count 6) at whole
  have hb : (8*M+8)+1+((8*M+8)+1+(8*M+8))=24*M+26 := by ring
  rw [hb] at whole
  exact whole

theorem scalars_ready (D H M B count : ℕ) (hH : 4*H+3 ≤ D) (hM : 4*M+3 ≤ D) :
    ClockJoin.ReadyRun machine (24*H+24*M+53) (MatrixBucketWorkspace.output D H M B count) (data D H M B count 6) := by
  have whole := ClockJoin.join first tail3 _ _ _ _ _ (first_ready D H M B count hH hM) (last_ready D H M B count hH hM)
  have hi : data D H M B count 0=MatrixBucketWorkspace.output D H M B count := by
    funext i
    simp [data]
  have hb : (24*H+26)+1+(24*M+26)=24*H+24*M+53 := by ring
  rw [hi,hb] at whole
  exact whole

end NearCubicWires.RepairOrdinary.MatrixBucketScalars
