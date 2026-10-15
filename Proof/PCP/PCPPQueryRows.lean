import Proof.PCP.PCPPQueryFieldChain

/-! The support row is selected by a paid scan driven by the actual query
index and arity tapes. The source remains the explicit source PCPP object;
the row address is never supplied to the machine. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryRows
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def skip := RepeatMachine.machine (MatrixRawBlock.machine false) (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (arity : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (MatrixRawBlock.config (s:=5) 0 (UnaryTemplate.tape arity) 1 source pos out) total driver

theorem remaining (arity : ℕ) (pre : List Bool) (rows : List (List Bool))
    (suffix out : List Bool) (total pos : ℕ) (hn : pos+rows.length=total)
    (hw : ∀ row∈rows,row.length=arity) :
    Timed skip (rows.length*(2*arity+6)+total+3)
      (cfg 0 arity (pre++rows.flatten++suffix) pre.length out total (pos+1))
      (cfg 3 arity (pre++rows.flatten++suffix) (pre.length+rows.flatten.length) out total 1) := by
  induction rows generalizing pre pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa only [skip,cfg,List.flatten_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.add_zero]
      using RepeatMachine.exhaust (MatrixRawBlock.machine false) (fun _ _ => true)
        (MatrixRawBlock.config 0 (UnaryTemplate.tape arity) 1 (pre++suffix) pre.length out) total
  | cons row rows ih =>
    have hrw := hw row (by simp)
    obtain ⟨r,hr,hf,hs,_⟩ := MatrixRawBlock.block_run false pre row (rows.flatten++suffix) out
    simp only [MatrixRawBlock.selected,Bool.false_eq_true,↓reduceIte,List.append_nil] at hf
    rw [hrw] at hr hf hs
    have hstep := RepeatMachine.iteration (MatrixRawBlock.machine false) (fun _ _ => true)
      (MatrixRawBlock.config 0 (UnaryTemplate.tape arity) 1 (pre++row++(rows.flatten++suffix)) pre.length out)
      total pos r (by rfl) (by simp only [List.length_cons] at hn; omega) hr
    rw [hf,hs] at hstep
    have htail := ih (pre++row) (pos+1) (by simp only [List.length_cons] at hn; omega)
      (fun x hx => hw x (by simp [hx]))
    have hsource : (pre++row)++rows.flatten++suffix=pre++row++(rows.flatten++suffix) := by simp [List.append_assoc]
    have hmid : cfg 0 arity (pre++row++(rows.flatten++suffix)) (pre.length+arity) out total (pos+2)=
        cfg 0 arity ((pre++row)++rows.flatten++suffix) (pre++row).length out total ((pos+1)+1) := by
      rw [hsource,List.length_append,hrw]
    change Timed skip (2*arity+4+2)
      (cfg 0 arity (pre++row++(rows.flatten++suffix)) pre.length out total (pos+1))
      (cfg 0 arity (pre++row++(rows.flatten++suffix)) (pre.length+arity) out total (pos+2)) at hstep
    rw [hmid] at hstep
    have hall := hstep.trans htail
    have htime : 2*arity+4+2+(rows.length*(2*arity+6)+total+3)=
        (row::rows).length*(2*arity+6)+total+3 := by simp only [List.length_cons]; ring
    rw [htime] at hall
    simpa only [List.flatten_cons,List.append_assoc,List.length_append,hrw,Nat.add_assoc] using hall

theorem skip_run (arity : ℕ) (pre : List Bool) (rows : List (List Bool))
    (suffix out : List Bool) (hw : ∀ row∈rows,row.length=arity) :
    ∃ r,runFrom skip (rows.length*(2*arity+7)+3)
      (cfg 0 arity (pre++rows.flatten++suffix) pre.length out rows.length 1)=some r ∧
      r.final=cfg 3 arity (pre++rows.flatten++suffix) (pre.length+rows.flatten.length) out rows.length 1 ∧
      r.steps=rows.length*(2*arity+7)+3 := by
  have h := remaining arity pre rows suffix out rows.length 0 (by omega) hw
  have ht : rows.length*(2*arity+6)+rows.length+3=rows.length*(2*arity+7)+3 := by ring
  rw [ht] at h
  exact h.run (by simp [skip,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

def copy : Machine 4 5 := TapeEmbedding.machine 1 (MatrixRawBlock.machine true)
noncomputable def machine := Composition.machine skip copy
def budget (arity index : ℕ) := index*(2*arity+7)+2*arity+8

theorem row_run (arity : ℕ) (pre : List Bool) (rows : List (List Bool))
    (row suffix out : List Bool) (hw : ∀ r∈rows,r.length=arity) (hrw : row.length=arity) :
    ∃ r,runFrom machine (budget arity rows.length)
      (Composition.leftConfig 5 (cfg 0 arity (pre++rows.flatten++row++suffix) pre.length out rows.length 1))=some r ∧
      r.final.tapes 0=UnaryTemplate.tape arity ∧ r.final.heads 0=1 ∧
      r.final.tapes 1=pre++rows.flatten++row++suffix ∧ r.final.heads 1=pre.length+rows.flatten.length+arity ∧
      r.final.tapes 2=out++row ∧ r.final.heads 2=(out++row).length ∧
      r.final.tapes 3=CompareMachine.word rows.length ∧ r.final.heads 3=1 ∧
      r.steps=budget arity rows.length := by
  let source := pre++rows.flatten++row++suffix
  obtain ⟨first,hfirst,hff,hfs⟩ := skip_run arity pre rows (row++suffix) out hw
  have hsource : pre++rows.flatten++(row++suffix)=source := by simp [source,List.append_assoc]
  rw [hsource] at hfirst hff
  obtain ⟨last,hl,hlf,hls,_⟩ := MatrixRawBlock.block_run true (pre++rows.flatten) row suffix out
  simp only [MatrixRawBlock.selected,↓reduceIte] at hlf
  rw [hrw] at hl hlf hls
  have he := TapeEmbedding.run_embed (MatrixRawBlock.machine true)
    (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length) _ _ last hl
  have hi : TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length)
      (MatrixRawBlock.config 0 (UnaryTemplate.tape arity) 1 source (pre++rows.flatten).length out)=
      Composition.restart first.final copy.start := by
    rw [hff,List.length_append]
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  change runFrom copy (2*arity+4)
    (TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length)
      (MatrixRawBlock.config 0 (UnaryTemplate.tape arity) 1 source (pre++rows.flatten).length out))=_ at he
  rw [hi] at he
  have hj := Composition.run_join skip copy (rows.length*(2*arity+7)+3) (2*arity+4) _ first
    (TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length) last) hfirst he
  have htime : rows.length*(2*arity+7)+3+1+(2*arity+4)=budget arity rows.length := by unfold budget; omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first
    (TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word rows.length) last),hj,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | (change first.steps+1+last.steps=_; rw [hfs,hls]; exact htime)
    | (simp only [Composition.joinedReceipt,Composition.rightConfig,TapeEmbedding.receipt];
        rw [hlf]; simp [TapeEmbedding.config,MatrixRawBlock.config,Fin.addCases,List.length_append,Nat.add_assoc])

end NearCubicWires.RepairOrdinary.PCPPQueryRows
