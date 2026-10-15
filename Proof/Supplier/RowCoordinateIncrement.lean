import Proof.Supplier.RowCoefficientBounds
import Proof.Circuits.MatrixBucketDimensionsIncrement

/-! Advance the coordinate template physically and retain its head-one ABI.
The existing unary increment allocates its new terminator and rewinds; the
two surrounding head moves are actual transitions with explicit cost. -/
namespace NearCubicWires.RepairOrdinary.RowCoordinateIncrement
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shift (direction : HeadMove) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun _=>direction⟩ else none
def cfg {s : ℕ} (q : Fin s) (pos : ℕ) (bits : List Bool) : Configuration 1 s :=
  ⟨q,fun _=>pos,fun _=>bits⟩
def first := Composition.machine (shift .left) MatrixBucketDimensions.Increment.machine
def machine := Composition.machine first (shift .right)

theorem shift_run (direction : HeadMove) (pos : ℕ) (bits : List Bool) :
    ∃ r,runFrom (shift direction) 1 (cfg 0 pos bits)=some r ∧
      r.final=cfg 1 (direction.apply pos) bits ∧ r.steps=1 := by
  have hs : step (shift direction) (cfg 0 pos bits)=some (cfg 1 (direction.apply pos) bits) := by
    simp [step,shift,cfg,applyAction]
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem increment_run (j : ℕ) :
    ∃ r,runFrom machine (2*j+9) (cfg machine.start 1 (UnaryTemplate.tape j))=some r ∧
      r.final.heads=(fun _=>1) ∧ r.final.tapes=(fun _=>UnaryTemplate.tape (j+1)) ∧ r.steps=2*j+9 := by
  obtain ⟨a,ha,af,asteps⟩ := shift_run .left 1 (UnaryTemplate.tape j)
  obtain ⟨b,hb,bt,bh,bs⟩ := MatrixBucketDimensions.Increment.increment_run j
  have he : initialConfiguration MatrixBucketDimensions.Increment.machine (fun _=>UnaryTemplate.tape j)=
      Composition.restart a.final MatrixBucketDimensions.Increment.machine.start := by
    rw [af]; rfl
  unfold run at hb
  rw [he] at hb
  have ab := Composition.run_join (shift .left) MatrixBucketDimensions.Increment.machine _ _ _ a b ha hb
  let ar := Composition.joinedReceipt a b
  obtain ⟨c,hc,cf,cs⟩ := shift_run .right 0 (UnaryTemplate.tape (j+1))
  have he' : cfg 0 0 (UnaryTemplate.tape (j+1))=Composition.restart ar.final (shift .right).start := by
    apply configuration_ext
    · rfl
    · exact (funext bh).symm
    · exact bt.symm
  rw [he'] at hc
  have whole := Composition.run_join first (shift .right) _ _ _ ar c ab hc
  have ht : (1+1+(2*j+5))+1+1=2*j+9 := by omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt ar c,whole,?_,?_,?_⟩
  · change c.final.heads=_; rw [cf]; rfl
  · change c.final.tapes=_; rw [cf]; rfl
  · change (a.steps+1+b.steps)+1+c.steps=_
    rw [asteps,bs,cs,ht]

def slots : Fin 1 → Fin 32 := fun _=>15
theorem injective : Function.Injective slots := by intro a b _; exact Subsingleton.elim _ _
noncomputable def focused := RecoveryFocus.machine slots machine
theorem pick (i : Fin 32) : RecoveryFocus.pick slots i=(if i=15 then some 0 else none) := by
  fin_cases i
  all_goals first | exact RecoveryFocus.pick_slot slots injective 0 | decide

theorem focused_run (j : ℕ) (heads : Fin 32 → ℕ) (tapes : Fin 32 → List Bool)
    (hh : heads 15=1) (ht : tapes 15=UnaryTemplate.tape j) :
    ∃ r,runFrom focused (2*j+9) ⟨focused.start,heads,tapes⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=Function.update tapes 15 (UnaryTemplate.tape (j+1)) ∧ r.steps=2*j+9 := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := increment_run j
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots injective machine heads tapes _ _ base hbase
  have he : RecoveryFocus.config slots heads tapes (cfg machine.start 1 (UnaryTemplate.tape j))=
      (⟨focused.start,heads,tapes⟩ : Configuration 32 9) := by
    apply WilliamsSourceCrop.focus_same slots (⟨focused.start,heads,tapes⟩ : Configuration 32 9)
    · intro i; exact hh
    · intro i; exact ht
  rw [he] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf]
    simp only [RecoveryFocus.config,bh]
    funext i
    by_cases hi : i=15
    · subst i; simp [pick,hh]
    · simp [pick,hi]
  · rw [rf]
    change install slots tapes base.final.tapes=_
    rw [bt]
    funext i
    by_cases hi : i=15
    · subst i; simp [install,pick]
    · simp [install,pick,hi]

end NearCubicWires.RepairOrdinary.RowCoordinateIncrement
