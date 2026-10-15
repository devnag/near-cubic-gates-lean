import Proof.MachineModel.OrdinaryMatrixBucketDouble

/-! Cold canonical bucket-size entry. The 2U numerators, positive-budget
predecessor and branch flag are produced by ordinary tape runs. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketSizePrepare
open LocalBitMultitape RecoveryRootRound RecoveryExecution CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 10) : Fin 28 := i.castAdd 18
theorem native_injective : Function.Injective native := by
  intro i j h; exact Fin.ext (congrArg (fun a : Fin 28 => a.val) h)
def copySlots : Fin 5 → Fin 28 := ![10,11,12,13,14]
def predSlots : Fin 1 → Fin 28 := fun _ => 12
noncomputable def double := RecoveryFocus.machine native MatrixBucketDouble.machine
noncomputable def copy := RecoveryFocus.machine copySlots MatrixRawDimension.resetMachine
noncomputable def pred := RecoveryFocus.machine predSlots MatrixBucketPredecessor.machine
def input (U q : ℕ) : Fin 28 → List Bool := fun i =>
  if i=0 then UnaryTemplate.tape U else if i=10 then List.replicate q true else []
def guard : Machine 28 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
      some ⟨1,fun _ => none,fun i => if i=12 then .right else .stay⟩
    else if q.val=1 then
      some ⟨2,fun i => if i=15 then some (bits 12) else none,fun i => if i=12 then .left else .stay⟩
    else none
def raised (i : Fin 28) : ℕ := if i=12 then 1 else 0
def guarded (q : ℕ) (tapes : Fin 28 → List Bool) (i : Fin 28) :=
  if i=15 then [decide (1<q)] else tapes i
noncomputable def last := Composition.machine pred guard
noncomputable def tail := Composition.machine copy last
noncomputable def machine := Composition.machine double tail
def budget (U q : ℕ) := MatrixBucketDouble.budget U+1+((4*q+8)+1+((2*q+1)+1+2))

theorem guard_run (q : ℕ) (tapes : Fin 28 → List Bool)
    (h12 : tapes 12=UnaryTemplate.tape (q-1)) (h15 : tapes 15=[]) :
    ClockJoin.ReadyRun guard 2 tapes (guarded q tapes) := by
  have hb : readTapeBit (tapes 12) 1=decide (1<q) := by
    rw [h12]
    by_cases hq : 1<q
    · have h := UnaryTemplate.tape_mark (q-1) 0 (by omega)
      simpa [hq] using h
    · have hz : q-1=0 := by omega
      simp only [hz]
      simp [hq,UnaryTemplate.tape,readTapeBit,List.getD]
  have hfirst : step guard (initialConfiguration guard tapes)=some ⟨1,raised,tapes⟩ := by
    simp [step,guard,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have hlast : step guard ⟨1,raised,tapes⟩=some ⟨2,fun _ => 0,guarded q tapes⟩ := by
    have hs : (⟨1,raised,tapes⟩ : Configuration 28 3).scanned 12=decide (1<q) := hb
    simp [step,guard,hs]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      by_cases hi : i=15
      · subst i; simp [applyAction,guarded,h15]; rfl
      · simp [applyAction,guarded,hi]
  obtain ⟨actual,ha,hf,hs⟩ := ((Timed.single (by rfl) hfirst).trans
    (Timed.single (by rfl) hlast)).run (by rfl)
  exact ⟨actual,ha,by rw [hf],by intro i; rw [hf],hs.le⟩

theorem prepare_run (U q : ℕ) (hq : 0<q) : ∃ out,ClockJoin.ReadyRun machine (budget U q) (input U q) out ∧
    out 0=UnaryTemplate.tape U ∧ out 6=List.replicate (2*U) true ∧ out 7=List.replicate (2*U) true ∧
    out 8=UnaryTemplate.tape (2*U) ∧ out 11=List.replicate q true ∧
    out 12=UnaryTemplate.tape (q-1) ∧ out 13=UnaryTemplate.tape q ∧ out 15=[decide (1<q)] ∧
    (∀ i : Fin 28,16 ≤ i.val → out i=[]) := by
  obtain ⟨doubled,hd,d0,d6,d7,d8⟩ := MatrixBucketDouble.double_run U
  let stage0 := install native (input U q) doubled
  have hdouble := bounded_focus native native_injective _ _ _ hd (input U q)
    (by intro i; fin_cases i <;> rfl)
  have s0 (i : Fin 10) : stage0 (native i)=doubled i := install_slot native native_injective _ _ i
  have old (i : Fin 28) (hi : 10 ≤ i.val) : stage0 i=input U q i := by
    apply install_other
    intro j h
    have hv := congrArg Fin.val h
    dsimp [native] at hv
    omega
  obtain ⟨copied,hcopy,c1,c2,c3,ch,cs⟩ := MatrixRawDimension.reset_run q
  have copyReady : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*q+8)
      (MatrixRawDimension.resetInput q) copied.final.tapes := ⟨copied,hcopy,rfl,ch,cs.le⟩
  have copyInput : ∀ i,stage0 (copySlots i)=MatrixRawDimension.resetInput q i := by
    intro i; fin_cases i <;> exact old _ (by decide)
  let stage1 := install copySlots stage0 copied.final.tapes
  have hcopy' := bounded_focus copySlots (by decide) _ _ _ copyReady stage0 copyInput
  have s1 (i : Fin 5) : stage1 (copySlots i)=copied.final.tapes i := install_slot copySlots (by decide) _ _ i
  have o1 (i : Fin 28) (hi : ∀ j,copySlots j≠i) : stage1 i=stage0 i := install_other copySlots _ _ i hi
  obtain ⟨predecessor,hpred,pt,ph,ps⟩ := MatrixBucketPredecessor.predecessor_run q hq
  have predReady : ClockJoin.ReadyRun MatrixBucketPredecessor.machine (2*q+1)
      (fun _ => List.replicate q true) (fun _ => UnaryTemplate.tape (q-1)) :=
    ⟨predecessor,hpred,pt,ph,ps.le⟩
  let stage2 := install predSlots stage1 (fun _ => UnaryTemplate.tape (q-1))
  have hpred' := bounded_focus predSlots (by intro i j _; exact Subsingleton.elim _ _) _ _ _ predReady stage1
    (by intro i; exact (s1 2).trans c2)
  have s2 : stage2 12=UnaryTemplate.tape (q-1) := install_slot predSlots (by decide) _ _ 0
  have o2 (i : Fin 28) (hi : i≠12) : stage2 i=stage1 i := by
    apply install_other
    intro j; exact Ne.symm hi
  have blank15 : stage2 15=[] := (o2 15 (by decide)).trans
    ((o1 15 (by decide)).trans (old 15 (by decide)))
  have hg := guard_run q stage2 s2 blank15
  have hlast := ClockJoin.join pred guard _ _ _ _ _ hpred' hg
  have htail := ClockJoin.join copy last _ _ _ _ _ hcopy' hlast
  have hall := ClockJoin.join double tail _ _ _ _ _ hdouble htail
  refine ⟨guarded q stage2,hall,?_,?_,?_,?_,?_,s2,?_,rfl,?_⟩
  · exact (o2 0 (by decide)).trans ((o1 0 (by decide)).trans ((s0 0).trans d0))
  · exact (o2 6 (by decide)).trans ((o1 6 (by decide)).trans ((s0 6).trans d6))
  · exact (o2 7 (by decide)).trans ((o1 7 (by decide)).trans ((s0 7).trans d7))
  · exact (o2 8 (by decide)).trans ((o1 8 (by decide)).trans ((s0 8).trans d8))
  · exact (o2 11 (by decide)).trans ((s1 1).trans c1)
  · exact (o2 13 (by decide)).trans ((s1 3).trans c3)
  · intro i hi
    have hn : i≠15 := by intro h; subst i; omega
    change (if i=15 then _ else _) = []
    rw [if_neg hn,o2 i (by intro h; subst i; omega),o1]
    · have h0 : i≠0 := by intro h; subst i; omega
      have h10 : i≠10 := by intro h; subst i; omega
      exact (old i (by omega)).trans (by simp [input,h0,h10])
    · intro j h
      fin_cases j <;> have hv := congrArg Fin.val h <;> simp [copySlots] at hv <;> omega

end NearCubicWires.RepairOrdinary.MatrixBucketSizePrepare
