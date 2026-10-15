import Proof.Hierarchy.CompetitorSameBucketZeroGridNative

/-! Physical zero-grid scratch and second U counter from the retained
reference fields. The existing append cursor is preserved throughout. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroPrepareSpace
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) (i : Fin 19):=if i=5 then out.length else 0
def cfg {s : ℕ} (q : Fin s) (out : List Bool) (tapes : Fin 19 → List Bool) : Configuration 19 s :=⟨q,heads out,tapes⟩
def input (p m u cap : ℕ) (out : List Bool) : Fin 19 → List Bool :=
  ![UnaryTemplate.tape u,frame (binary m u),frame (binary m 0),frame (List.replicate (p+1) false),
    List.replicate cap true,out,[],[],[],[],[],[],[],[],[],[],[],[],[]]
def allocated (p m u cap : ℕ) (out : List Bool) : Fin 19 → List Bool :=
  ![UnaryTemplate.tape u,frame (binary m u),frame (binary m 0),frame (List.replicate (p+1) false),
    List.replicate cap true,out,List.replicate cap false,List.replicate cap false,
    List.replicate cap false,List.replicate cap false,List.replicate cap false,List.replicate cap false,
    List.replicate cap false,List.replicate (cap+1) false,List.replicate cap false,[],[],[],[]]
def output (p m u cap : ℕ) (out log : List Bool) : Fin 19 → List Bool :=
  ![UnaryTemplate.tape u,frame (binary m u),frame (binary m 0),frame (List.replicate (p+1) false),
    List.replicate cap true,out,List.replicate cap false,List.replicate cap false,
    List.replicate cap false,List.replicate cap false,List.replicate cap false,List.replicate cap false,
    List.replicate cap false,List.replicate (cap+1) false,List.replicate cap false,
    List.replicate u true,List.replicate u true,UnaryTemplate.tape u,log]
def scalarSlots : Fin 10 → Fin 19 := ![6,7,8,9,10,11,12,14,4,13]
def templateSlots : Fin 5 → Fin 19 := ![0,15,16,17,18]
theorem scalar_injective : Function.Injective scalarSlots := by decide
theorem template_injective : Function.Injective templateSlots := by decide
noncomputable def allocate:=RecoveryFocus.machine scalarSlots (RecoveryScratchErase.resetMachine 8)
noncomputable def template:=RecoveryFocus.machine templateSlots MatrixTemplateCopy.resetMachine
noncomputable def machine:=Composition.machine allocate template
def budget (u cap : ℕ):=(2*cap+4)+1+(4*u+12)

private theorem allocated_eq (p m u cap : ℕ) (out : List Bool) :
    install scalarSlots (input p m u cap out) (CompetitorSameBucketColdAllocate.eraseOutput 8 cap)=
      allocated p m u cap out := by
  apply HierarchyAllocation.install_eq _ scalar_injective
  · intro j
    fin_cases j <;> simp [allocated,scalarSlots,CompetitorSameBucketColdAllocate.eraseOutput,Fin.addCases]
  · intro i hi
    fin_cases i <;> simp [allocated,input]
    all_goals first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) |
      exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | exact False.elim (hi 4 rfl) |
      exact False.elim (hi 5 rfl) | exact False.elim (hi 6 rfl) | exact False.elim (hi 7 rfl) |
      exact False.elim (hi 8 rfl) | exact False.elim (hi 9 rfl)

private theorem output_eq (p m u cap : ℕ) (out : List Bool) (t : Fin 5 → List Bool)
    (h0 : t 0=UnaryTemplate.tape u) (h1 : t 1=List.replicate u true)
    (h2 : t 2=List.replicate u true) (h3 : t 3=UnaryTemplate.tape u) :
    install templateSlots (allocated p m u cap out) t=output p m u cap out (t 4) := by
  apply HierarchyAllocation.install_eq _ template_injective
  · intro j; fin_cases j
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · rfl
  · intro i hi
    fin_cases i <;> simp [output,allocated]
    all_goals first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) |
      exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | exact False.elim (hi 4 rfl)

theorem space_run (p m u cap : ℕ) (out : List Bool) :
    ∃ actual log,runFrom machine (budget u cap) (cfg machine.start out (input p m u cap out))=some actual ∧
      actual.final.heads=heads out ∧ actual.final.tapes=output p m u cap out log ∧ actual.steps≤budget u cap := by
  obtain ⟨base,hb,bt,bh,bs⟩:=CompetitorSameBucketColdAllocate.erase_ready 8 cap
  have ready : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 8) (2*cap+4)
      (CompetitorSameBucketColdAllocate.eraseInput 8 cap) (CompetitorSameBucketColdAllocate.eraseOutput 8 cap):=
    ⟨base,hb,bt,bh,bs.le⟩
  obtain ⟨first,hf,fh,ft,fs⟩:=CompetitorReusableDecision.bounded_focused_run scalarSlots scalar_injective
    _ _ _ ready (heads out) (input p m u cap out)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [allocated_eq] at ft
  obtain ⟨counter,hcounter,t0,t1,t2,t3,ch,cs⟩:=MatrixTemplateCopy.reset_run u
  have counterReady : ClockJoin.ReadyRun MatrixTemplateCopy.resetMachine (4*u+12)
      (MatrixTemplateCopy.resetInput u) counter.final.tapes:=⟨counter,hcounter,rfl,ch,cs.le⟩
  obtain ⟨last,hl,lh,lt,ls⟩:=CompetitorReusableDecision.bounded_focused_run templateSlots template_injective
    _ _ _ counterReady (heads out) (allocated p m u cap out)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [output_eq p m u cap out counter.final.tapes t0 t1 t2 t3] at lt
  have he : Composition.restart first.final template.start=cfg template.start out (allocated p m u cap out) := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact ft
  change runFrom template (4*u+12) (cfg template.start out (allocated p m u cap out))=some last at hl
  rw [←he] at hl
  have joined:=Composition.run_join allocate template _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,counter.final.tapes 4,joined,lh,lt,?_⟩
  change first.steps+1+last.steps≤budget u cap
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroPrepareSpace
