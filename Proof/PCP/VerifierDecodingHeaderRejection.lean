import Proof.PCP.VerifierDecodingTableRun

/-! Both malformed-header branches of the existing two-parser machine.
A missing first unary terminator causes only one further blank-marker read;
a missing second terminator rejects after the bounded remaining prefix. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.HeaderMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dataCfg (q : Fin 4) (source : List Bool) (pos t s : ℕ) : Configuration 3 4 :=
  ⟨q,![pos,t,s],![source,List.replicate t true,List.replicate s true]⟩

theorem first_config (q : Fin 4) (source : List Bool) (pos t : ℕ) :
    TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => []) (UnaryMachine.cfg q source pos t)=
      dataCfg q source pos t 0 := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeEmbedding.config,UnaryMachine.cfg,dataCfg,Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeEmbedding.config,UnaryMachine.cfg,dataCfg,Fin.addCases]

theorem second_config (q : Fin 4) (source : List Bool) (pos t s : ℕ) :
    TapeRenaming.config swap (TapeEmbedding.config (fun _ : Fin 1 => t)
      (fun _ => List.replicate t true) (UnaryMachine.cfg q source pos s))=dataCfg q source pos t s := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,UnaryMachine.cfg,dataCfg,swap,Fin.addCases]
  · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,UnaryMachine.cfg,dataCfg,swap,Fin.addCases]

theorem missing_first (n : ℕ) :
    ∃ r, run machine (2*n+3) ![frame (List.replicate n true),[],[]]=some r ∧
      r.final.control=7 ∧ r.steps=2*n+3 := by
  obtain ⟨r,hr,hf,hs,_⟩ := UnaryMachine.reject_run n []
  have hfirst := TapeEmbedding.run_embed UnaryMachine.machine (fun _ : Fin 1 => 0) (fun _ => []) _ _ r hr
  let r' := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ => []) r
  have hrf : r'.final=dataCfg 3 (frame (List.replicate n true)) (2*n+1) n 0 := by
    simp only [r',TapeEmbedding.receipt,hf,List.nil_append,List.length_nil,Nat.zero_add,first_config]
  let source := frame (List.replicate n true)
  have hread : readTapeBit source (2*n+1)=false := by
    have hl : source.length=2*n+1 := by simp [source]
    rw [←hl]
    simp [readTapeBit,List.getD]
  have he : step second (dataCfg 0 source (2*n+1) n 0)=some (dataCfg 3 source (2*n+2) n 0) := by
    simp [step,second,first,TapeRenaming.machine,TapeEmbedding.machine,UnaryMachine.machine,
      dataCfg,Configuration.scanned,swap,hread]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,TapeRenaming.action,TapeEmbedding.action,
        UnaryMachine.action,HeadMove.apply,Fin.addCases]
    · funext i; fin_cases i <;> simp [applyAction,TapeRenaming.action,TapeEmbedding.action,
        UnaryMachine.action,Fin.addCases]
  obtain ⟨tail,ht,htf,hts⟩ := (Timed.single (by rfl : second.halted (0 : Fin 4)=false) he).run (by rfl)
  have hmid : Composition.restart r'.final second.start=dataCfg 0 source (2*n+1) n 0 := by
    rw [hrf]
    rfl
  rw [←hmid] at ht
  have hj := Composition.run_join first second (2*n+1) 1 _ r' tail hfirst ht
  have hi : Composition.leftConfig 4 (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => [])
      (UnaryMachine.cfg 0 ([]++frame (List.replicate n true)) 0 0))=
      initialConfiguration machine ![frame (List.replicate n true),[],[]] := by
    rw [List.nil_append,first_config]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  simp only [List.length_nil] at hj
  rw [hi] at hj
  have htime : (2*n+1)+1+1=2*n+3 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt r' tail,hj,?_,?_⟩
  · change tail.final.control.natAdd 4=(7 : Fin 8)
    rw [htf]
    rfl
  · change r.steps+1+tail.steps=2*n+3
    omega

def missingWord (t s : ℕ) : List Bool := List.replicate t true++false::List.replicate s true

theorem missing_second (t s : ℕ) :
    ∃ r, run machine (2*t+2*s+4) ![frame (missingWord t s),[],[]]=some r ∧
      r.final.control=7 ∧ r.steps=2*t+2*s+4 := by
  obtain ⟨r,hr,hf,hs,_⟩ := UnaryMachine.parse_run t [] (List.replicate s true)
  have hfirst := TapeEmbedding.run_embed UnaryMachine.machine (fun _ : Fin 1 => 0) (fun _ => []) _ _ r hr
  let r' := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ => []) r
  let pre := Streaming.marks (List.replicate t true++[false])
  have hpre : pre.length=2*t+2 := by simp [pre,Streaming.marks_length]
  have hword : pre++frame (List.replicate s true)=frame (missingWord t s) := by
    simp [pre,missingWord,←Streaming.frame_append,List.append_assoc]
  obtain ⟨r2,hr2,hf2,hs2,_⟩ := UnaryMachine.reject_run s pre
  rw [hword] at hr2 hf2
  have hsecond := TapeEmbedding.run_embed UnaryMachine.machine (fun _ : Fin 1 => t)
    (fun _ => List.replicate t true) _ _ r2 hr2
  have hrenamed := TapeRenaming.run_rename swap first _ _ _ hsecond
  let r2' := TapeRenaming.receipt swap
    (TapeEmbedding.receipt (fun _ : Fin 1 => t) (fun _ => List.replicate t true) r2)
  have hmid : Composition.restart r'.final second.start=
      TapeRenaming.config swap (TapeEmbedding.config (fun _ : Fin 1 => t)
        (fun _ => List.replicate t true) (UnaryMachine.cfg 0 (frame (missingWord t s)) pre.length 0)) := by
    simp only [r',TapeEmbedding.receipt,hf,List.nil_append,List.length_nil,Nat.zero_add,first_config,second_config,hpre]
    rfl
  have hcall : runFrom second (2*s+1) (Composition.restart r'.final second.start)=some r2' := by
    rw [hmid]
    exact hrenamed
  have hj := Composition.run_join first second (2*t+2) (2*s+1) _ r' r2' hfirst hcall
  have hi : Composition.leftConfig 4 (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => [])
      (UnaryMachine.cfg 0 ([]++frame (missingWord t s)) 0 0))=
      initialConfiguration machine ![frame (missingWord t s),[],[]] := by
    rw [List.nil_append,first_config]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  simp only [List.length_nil] at hj
  dsimp only [missingWord] at hi
  rw [hi] at hj
  have htime : (2*t+2)+1+(2*s+1)=2*t+2*s+4 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt r' r2',hj,?_,?_⟩
  · change r2.final.control.natAdd 4=(7 : Fin 8)
    rw [hf2]
    rfl
  · change r.steps+1+r2.steps=2*t+2*s+4
    omega

end NearCubicWires.RepairSource.VerifierDecoding.HeaderMachine
