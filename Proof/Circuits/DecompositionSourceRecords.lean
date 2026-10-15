import Proof.Circuits.DecompositionSourceFields

/-! The source child stream is copied by its decoded child count and arity.
Each native signed field is read once; both counted-loop drivers return to
their sentinel heads after the complete scan. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource.Records
open LocalBitMultitape RepairRepresentation RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev innerStates := Fintype.card (RepeatMachine.Control 6)
def target := TapeEmbedding.machine 1 Fields.machine
noncomputable def child := Composition.machine Fields.loop target
def store {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ)
    (backing out : List Bool) (n : ℕ) : Configuration 4 s :=
  ⟨q,![pos,0,out.length,1],![source,backing,out,CompareMachine.word n]⟩
def childSaved {n : ℕ} (g : ExactThresholdGate n) (backing : List Bool) :=
  Fields.saved g.target (Fields.savedList (List.ofFn g.weight) backing)
def childFinish : Fin (innerStates+6) := (5 : Fin 6).natAdd innerStates

theorem child_run {n : ℕ} (g : ExactThresholdGate n) (pre tail backing out : List Bool) :
    ∃ r,runFrom child ((exactWord g).length+6*n+7)
      (store child.start (pre++exactWord g++tail) pre.length backing out n)=some r ∧
      r.final=store childFinish (pre++exactWord g++tail) (pre.length+(exactWord g).length)
        (childSaved g backing) (out++exactWord g) n ∧
      r.steps=(exactWord g).length+6*n+7 := by
  let weights := (List.ofFn g.weight).flatMap intWord
  let source := pre++exactWord g++tail
  obtain ⟨first,hfirst,hff,hfs⟩ := Fields.list_run pre (intWord g.target++tail) backing out (List.ofFn g.weight)
  simp only [List.length_ofFn] at hfirst hff hfs
  have hsource : pre++weights++(intWord g.target++tail)=source := by simp [source,exactWord,weights,List.append_assoc]
  change runFrom Fields.loop (weights.length+6*n+3)
    (Fields.cfg 0 (pre++weights++(intWord g.target++tail)) pre.length backing out n 1)=some first at hfirst
  rw [hsource] at hfirst
  change first.final=Fields.cfg 3 (pre++weights++(intWord g.target++tail))
    (pre.length+weights.length) (Fields.savedList (List.ofFn g.weight) backing) (out++weights) n 1 at hff
  rw [hsource] at hff
  obtain ⟨last,hl,hlf,hls⟩ := Fields.int_run (pre++weights) tail
    (Fields.savedList (List.ofFn g.weight) backing) (out++weights) g.target
  have hsource2 : (pre++weights)++intWord g.target++tail=source := by simp [source,exactWord,weights,List.append_assoc]
  rw [hsource2,List.length_append] at hl
  have he := TapeEmbedding.run_embed Fields.machine (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word n) _ _ last hl
  have hi : TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word n)
      (PCPPQueryField.store 0 source (pre.length+weights.length)
        (Fields.savedList (List.ofFn g.weight) backing) (out++weights))=
      Composition.restart first.final target.start := by
    rw [hff]
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [hi] at he
  have hj := Composition.run_join Fields.loop target (weights.length+6*n+3) (Fields.cost g.target) _
    first (TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word n) last) hfirst he
  have hc : Fields.cost g.target=(intWord g.target).length+3 := by
    simp [Fields.cost,intWord_length,natBitLength,intBitLength]
  have ht : (weights.length+6*n+3)+1+Fields.cost g.target=(exactWord g).length+6*n+7 := by
    rw [hc]; simp [exactWord,weights]; omega
  rw [ht] at hj
  have hentry : Composition.leftConfig 6 (Fields.cfg 0 source pre.length backing out n 1)=
      store child.start source pre.length backing out n := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hentry] at hj
  refine ⟨Composition.joinedReceipt first
    (TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word n) last),hj,?_,?_⟩
  · change Composition.rightConfig innerStates
      (TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word n) last.final)=_
    rw [hlf,hsource2,List.length_append]
    have hp : pre.length+weights.length+(intWord g.target).length=pre.length+(exactWord g).length := by simp [exactWord,weights]; omega
    have ho : (out++weights)++intWord g.target=out++exactWord g := by simp [exactWord,weights,List.append_assoc]
    rw [hp,ho]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  · change first.steps+1+last.steps=_
    rw [hfs,hls]
    simpa [weights] using ht

noncomputable def machine := RepeatMachine.machine child (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (backing out : List Bool) (arity total driver : ℕ) :=
  RepeatMachine.cfg phase (store child.start source pos backing out arity) total driver
def savedList {n : ℕ} (gs : List (ExactThresholdGate n)) (backing : List Bool) :=
  gs.foldl (fun bs g => childSaved g bs) backing

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) (pre tail backing out : List Bool)
    (total pos : ℕ) (hn : pos+gs.length=total) :
    Timed machine ((gs.flatMap exactWord).length+(6*n+9)*gs.length+total+3)
      (cfg 0 (pre++gs.flatMap exactWord++tail) pre.length backing out n total (pos+1))
      (cfg 3 (pre++gs.flatMap exactWord++tail) (pre.length+(gs.flatMap exactWord).length)
        (savedList gs backing) (out++gs.flatMap exactWord) n total 1) := by
  induction gs generalizing pre backing out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa [machine,cfg,savedList] using RepeatMachine.exhaust child (fun _ _ => true)
      (store child.start (pre++tail) pre.length backing out n) total
  | cons g gs ih =>
    obtain ⟨r,hr,hf,hs⟩ := child_run g pre (gs.flatMap exactWord++tail) backing out
    have hb := RepeatMachine.iteration child (fun _ _ => true)
      (store child.start (pre++exactWord g++(gs.flatMap exactWord++tail)) pre.length backing out n)
      total pos r (by rfl) (by simp only [List.length_cons] at hn; omega) hr
    rw [hf,hs] at hb
    simp only [↓reduceIte] at hb
    have ht := ih (pre++exactWord g) (childSaved g backing) (out++exactWord g) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
    have hsource : (pre++exactWord g)++gs.flatMap exactWord++tail=
        pre++exactWord g++(gs.flatMap exactWord++tail) := by simp [List.append_assoc]
    rw [hsource,List.length_append] at ht
    change Timed machine ((exactWord g).length+6*n+7+2)
      (cfg 0 (pre++exactWord g++(gs.flatMap exactWord++tail)) pre.length backing out n total (pos+1))
      (cfg 0 (pre++exactWord g++(gs.flatMap exactWord++tail)) (pre.length+(exactWord g).length)
        (childSaved g backing) (out++exactWord g) n total ((pos+1)+1)) at hb
    have hall := hb.trans ht
    have htime : (exactWord g).length+6*n+7+2+
        ((gs.flatMap exactWord).length+(6*n+9)*gs.length+total+3)=
        ((g::gs).flatMap exactWord).length+(6*n+9)*(g::gs).length+total+3 := by
      simp only [List.flatMap_cons,List.length_append,List.length_cons]; ring
    rw [htime] at hall
    simpa [List.flatMap_cons,List.append_assoc,savedList,Nat.add_assoc] using hall

theorem records_run {n : ℕ} (gs : List (ExactThresholdGate n)) (pre tail backing out : List Bool) :
    ∃ r,runFrom machine ((gs.flatMap exactWord).length+(6*n+10)*gs.length+3)
      (cfg 0 (pre++gs.flatMap exactWord++tail) pre.length backing out n gs.length 1)=some r ∧
      r.final=cfg 3 (pre++gs.flatMap exactWord++tail) (pre.length+(gs.flatMap exactWord).length)
        (savedList gs backing) (out++gs.flatMap exactWord) n gs.length 1 ∧
      r.steps=(gs.flatMap exactWord).length+(6*n+10)*gs.length+3 := by
  have h := remaining gs pre tail backing out gs.length 0 (by omega)
  have ht : (gs.flatMap exactWord).length+(6*n+9)*gs.length+gs.length+3=
      (gs.flatMap exactWord).length+(6*n+10)*gs.length+3 := by ring
  rw [ht] at h
  exact h.run (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

def capacity (n m : ℕ) : Fin 5→ℕ := fun i => if i=3 then n+2 else if i=4 then m+2 else 0
theorem template_pad (n : ℕ) : ZeroPadding.pad (n+2) (CompareMachine.word n)=UnaryTemplate.tape n := by
  simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem padded_run {n : ℕ} (gs : List (ExactThresholdGate n)) (pre tail backing out : List Bool) :
    ∃ r,runFrom machine ((gs.flatMap exactWord).length+(6*n+10)*gs.length+3)
      ⟨machine.start,![pre.length,0,out.length,1,1],
        ![pre++gs.flatMap exactWord++tail,backing,out,UnaryTemplate.tape n,UnaryTemplate.tape gs.length]⟩=some r ∧
      r.final.tapes=![pre++gs.flatMap exactWord++tail,savedList gs backing,out++gs.flatMap exactWord,
        UnaryTemplate.tape n,UnaryTemplate.tape gs.length] ∧
      r.final.heads=![pre.length+(gs.flatMap exactWord).length,0,(out++gs.flatMap exactWord).length,1,1] ∧
      r.steps=(gs.flatMap exactWord).length+(6*n+10)*gs.length+3 := by
  obtain ⟨base,hb,hbf,hbs⟩ := records_run gs pre tail backing out
  obtain ⟨r,hr,hf,hs,_⟩ := ZeroPadding.run_config machine (capacity n gs.length) _ _ base hb
  have he : ZeroPadding.config (capacity n gs.length)
      (cfg 0 (pre++gs.flatMap exactWord++tail) pre.length backing out n gs.length 1)=
      ⟨machine.start,![pre.length,0,out.length,1,1],
        ![pre++gs.flatMap exactWord++tail,backing,out,UnaryTemplate.tape n,UnaryTemplate.tape gs.length]⟩ := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,cfg,RepeatMachine.cfg,
        controlConfig,TapeEmbedding.config,store,Fin.addCases,template_pad]
  rw [he] at hr
  refine ⟨r,hr,?_,?_,hs.trans hbs⟩
  · rw [hf,hbf]
    funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,cfg,RepeatMachine.cfg,
      controlConfig,TapeEmbedding.config,store,Fin.addCases,template_pad]
  · rw [hf,hbf]
    funext i; fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.DecompositionSource.Records
