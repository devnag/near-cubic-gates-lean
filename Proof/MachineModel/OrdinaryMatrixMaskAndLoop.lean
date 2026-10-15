import Proof.MachineModel.OrdinaryMatrixMaskAndRow

/-! Actual traversal of all retained left-matrix rows using one padded
coefficient mask. Each row restores the mask and width sentinel, and both
global streams are retained until the enclosing aggregate return. -/
namespace NearCubicWires.RepairOrdinary.MatrixMaskAndLoop
open LocalBitMultitape RecoveryExecution
open MatrixMaskAndReturn (cfg)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def output (mask : List Bool) (rows : List (List Bool)) := rows.flatMap (fun bits => MatrixMaskAndRow.values (mask.zip bits))
def accepted (_ : Fin 5) (_ : Fin 4 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixMaskAndRow.machine accepted
def budget (width remaining total : ℕ) := remaining*(2*width+6)+total+3

theorem loop_run (mask : List Bool) (rows : List (List Bool)) (pre suffix out : List Bool) (total done : ℕ)
    (hcount : done+rows.length=total) (hwidth : ∀ row ∈ rows,row.length=mask.length) : ∃ actual,
    runFrom machine (budget mask.length rows.length total)
      (RepeatMachine.cfg 0 (cfg MatrixMaskAndRow.machine.start mask.length 1 0 mask
        (pre++rows.flatten++suffix) pre.length out) total (done+1))=some actual ∧
    actual.final=RepeatMachine.cfg 3 (cfg MatrixMaskAndRow.machine.start mask.length 1 0 mask
      (pre++rows.flatten++suffix) (pre.length+rows.flatten.length) (out++output mask rows)) total 1 ∧
    actual.steps≤budget mask.length rows.length total := by
  induction rows generalizing done pre out with
  | nil =>
    have hd : done=total := by simpa using hcount
    obtain ⟨actual,ha,hf,hs⟩ := (RepeatMachine.exhaust MatrixMaskAndRow.machine accepted
      (cfg MatrixMaskAndRow.machine.start mask.length 1 0 mask (pre++([] : List (List Bool)).flatten++suffix) pre.length out) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨actual,?_,?_,?_⟩
    · simpa only [machine,budget,List.length_nil,Nat.zero_mul,Nat.zero_add,hd] using ha
    · simpa only [output,List.flatMap_nil,List.flatten_nil,List.length_nil,Nat.add_zero,List.append_nil] using hf
    · simpa only [budget,List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons row rows ih =>
    have hn : done<total := by simp only [List.length_cons] at hcount; omega
    have hw := hwidth row (by simp)
    obtain ⟨body,hb,bf,bs⟩ := MatrixMaskAndRow.row_run mask row pre (rows.flatten++suffix) out hw.symm
    rw [hw] at hb bf bs
    have iteration := RepeatMachine.iteration MatrixMaskAndRow.machine accepted
      (cfg MatrixMaskAndRow.machine.start mask.length 1 0 mask (pre++row++(rows.flatten++suffix)) pre.length out)
      total done body rfl hn hb
    simp only [accepted,if_true] at iteration
    have hi : RepeatMachine.cfg 0 body.final total (done+2)=
        RepeatMachine.cfg 0 (cfg MatrixMaskAndRow.machine.start mask.length 1 0 mask
          ((pre++row)++rows.flatten++suffix) (pre++row).length (out++MatrixMaskAndRow.values (mask.zip row))) total (done+2) := by
      rw [bf]
      simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg,List.append_assoc,List.length_append,hw]
    rw [hi] at iteration
    obtain ⟨tail,ht,tf,ts⟩ := ih (pre++row) (out++MatrixMaskAndRow.values (mask.zip row)) (done+1)
      (by simp only [List.length_cons] at hcount; omega) (fun r hr => hwidth r (by simp [hr]))
    have ht' : runFrom machine (budget mask.length rows.length total)
        (RepeatMachine.cfg 0 (cfg MatrixMaskAndRow.machine.start mask.length 1 0 mask
          ((pre++row)++rows.flatten++suffix) (pre++row).length (out++MatrixMaskAndRow.values (mask.zip row))) total (done+2))=some tail := by
      simpa only [Nat.add_assoc] using ht
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨actual,ha,hf,hs,_⟩ := hprefix.followedBy tail ht'
    have hc : body.steps+2+budget mask.length rows.length total=budget mask.length (row::rows).length total := by
      rw [bs]
      unfold budget
      simp only [List.length_cons]
      ring
    rw [hc] at ha
    refine ⟨actual,?_,?_,?_⟩
    · simpa only [machine,List.flatten_cons,List.append_assoc] using ha
    · rw [hf,tf]
      simp only [output,List.flatMap_cons,List.flatten_cons,List.length_append,List.append_assoc,Nat.add_assoc]
    · rw [hs]
      omega

def padding (count : ℕ) : Fin 5 → ℕ := ![0,0,0,0,count+2]
noncomputable def nativeCfg (mask : List Bool) (rows : List (List Bool)) (phase : Fin 5) (pos : ℕ) (out : List Bool) :=
  ZeroPadding.config (padding rows.length) (RepeatMachine.cfg phase
    (cfg MatrixMaskAndRow.machine.start mask.length 1 0 mask rows.flatten pos out) rows.length 1)
def nativeBudget (width count : ℕ) := count*(2*width+7)+3

theorem native_heads (mask : List Bool) (rows : List (List Bool)) (phase : Fin 5) (pos : ℕ) (out : List Bool) :
    (nativeCfg mask rows phase pos out).heads=![1,0,pos,out.length,1] := by
  funext i; fin_cases i <;> rfl

theorem native_tapes (mask : List Bool) (rows : List (List Bool)) (phase : Fin 5) (pos : ℕ) (out : List Bool) :
    (nativeCfg mask rows phase pos out).tapes=![UnaryTemplate.tape mask.length,mask,rows.flatten,out,UnaryTemplate.tape rows.length] := by
  funext i
  fin_cases i <;> simp [nativeCfg,padding,ZeroPadding.config,ZeroPadding.pad,RepeatMachine.cfg,controlConfig,
    TapeEmbedding.config,cfg,Fin.addCases,CompareMachine.word,UnaryTemplate.tape]

theorem all_run (mask : List Bool) (rows : List (List Bool)) (out : List Bool)
    (hwidth : ∀ row ∈ rows,row.length=mask.length) : ∃ actual,
    runFrom machine (nativeBudget mask.length rows.length) (nativeCfg mask rows 0 0 out)=some actual ∧
    actual.final=nativeCfg mask rows 3 rows.flatten.length (out++output mask rows) ∧
    actual.steps≤nativeBudget mask.length rows.length := by
  obtain ⟨base,hb,bf,bs⟩ := loop_run mask rows [] [] out rows.length 0 (by omega) hwidth
  have hc : budget mask.length rows.length rows.length=nativeBudget mask.length rows.length := by
    unfold budget nativeBudget
    ring
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hb bf
  rw [hc] at hb bs
  obtain ⟨actual,ha,af,as,_⟩ := ZeroPadding.run_config machine (padding rows.length) _ _ base hb
  exact ⟨actual,ha,by rw [af,bf]; rfl,as.trans_le bs⟩

end NearCubicWires.RepairOrdinary.MatrixMaskAndLoop
