import Proof.PCP.PCPPQueryFieldChain

/-! Explicit local framing of query requests. The imported PCPP constructor
keeps its original codec. A physical copy isolates precisely that framed
constructor input and leaves the query cursor at the appended natural index.
The older unframed local query record has no banked inhabitant and is not
used by this adapter. -/
namespace NearCubicWires.RepairRepresentation
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure FramedPCPPQueryRealization (a : PointwisePCPPAlgorithm) where
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0<coefficient
  support : RepairSource.OrdinaryWordFunction
    (Σ r : PCPPRequest a.minimumArity, Fin (a.output r).systematicBits)
    (fun r => frame (pcppInput r.1)++natWord r.2.val)
    (fun r => List.ofFn fun j : Fin r.1.arity => decide (j∈(a.output r.1).systematicSupport r.2))
    (fun r => coefficient*(r.1.circuit.size+r.1.arity+1)^degree)
  clause : RepairSource.OrdinaryWordFunction
    (Σ r : PCPPRequest a.minimumArity, Fin (2^(a.output r).clauseBits))
    (fun r => frame (pcppInput r.1)++natWord r.2.val)
    (fun r => natListWord [literalIndex ((a.output r.1).clauses r.2).left,
      literalIndex ((a.output r.1).clauses r.2).right])
    (fun r => coefficient*(r.1.circuit.size+r.1.arity+1)^degree)

end NearCubicWires.RepairRepresentation

namespace NearCubicWires.RepairOrdinary.PCPPQueryInput
open LocalBitMultitape RecoveryExecution RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 2) : Bool := decide (i=1)
def isolate := MaskedReset.machine Field.machine selected
def entry (source : List Bool) (pos : ℕ) : Configuration 3 5 :=
  Rewind.recording (Field.cfg 0 source pos []) 0
def isolated (source : List Bool) (pos : ℕ) (bits : List Bool) : Configuration 3 5 :=
  ⟨4,![pos,0,0],![source,frame bits,List.replicate (2*bits.length+1) false]⟩

theorem isolate_run (pre bits tail : List Bool) :
    ∃ r,runFrom isolate (4*bits.length+4)
      (entry (pre++frame bits++tail) pre.length)=some r ∧
      r.final=isolated (pre++frame bits++tail) (pre.length+2*bits.length+1) bits ∧
      r.steps=4*bits.length+4 := by
  obtain ⟨base,hb,hbf,hbs⟩ := Field.copy_run pre bits tail []
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have he : i=1 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    rw [hbf,hbs]
    simp [Field.cfg]
  obtain ⟨r,hr,hf,hs,_⟩ := MaskedReset.reset_run Field.machine selected _ _ base hb hh
  have htime : 2*base.steps+2=4*bits.length+4 := by rw [hbs]; omega
  rw [htime] at hr hs
  refine ⟨r,hr,?_,hs⟩
  rw [hf,hbf,hbs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,selected,Field.cfg,isolated,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,Field.cfg,isolated,Fin.addCases]

def slots : Fin 3 → Fin 5 := ![1,3,4]
def outer : Machine 5 5 := TapeEmbedding.machine 2 Streaming.machine
noncomputable def inner : Machine 5 5 := RecoveryFocus.machine slots isolate
noncomputable def machine := Composition.machine outer inner
def input (word : List Bool) : Fin 5 → List Bool := fun i => if i=0 then frame word else []
def budget (bits tail : List Bool) := 4*(frame bits++tail).length+4*bits.length+7
def output (bits tail : List Bool) : Configuration 5 10 :=
  ⟨9,![0,2*bits.length+1,0,0,0],![frame (frame bits++tail),frame bits++tail,
    List.replicate (frame bits++tail).length false,frame bits,List.replicate (2*bits.length+1) false]⟩

theorem input_run (bits tail : List Bool) :
    ∃ r,run machine (budget bits tail) (input (frame bits++tail))=some r ∧
      r.final=output bits tail ∧ r.steps=budget bits tail := by
  let word := frame bits++tail
  obtain ⟨base,hbase,hbf,hbs,_⟩ := Streaming.copy_run word
  have ha := TapeEmbedding.run_embed Streaming.machine (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) _ _ base hbase
  rw [StreamPrepare.embed_initial] at ha
  let ambient := TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base.final
  obtain ⟨localRun,hl,hlf,hls⟩ := isolate_run [] bits tail
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hl hlf
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) isolate ambient.heads ambient.tapes _ _ localRun hl
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes (entry word 0)=
      Composition.restart ambient inner.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hbf]
      fin_cases i <;> simp [entry,Rewind.recording,Rewind.config,Field.cfg,slots,
        Streaming.finished,Streaming.config,TapeEmbedding.config,Fin.addCases]
    · intro i
      dsimp only [ambient]
      rw [hbf]
      fin_cases i <;> simp [entry,Rewind.recording,Rewind.config,Field.cfg,slots,
        Streaming.finished,Streaming.config,TapeEmbedding.config,Fin.addCases]
  rw [hi] at hf
  have hj := Composition.run_join outer inner (4*word.length+2) (4*bits.length+4) _
    (TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base) focused ha hf
  have ht : (4*word.length+2)+1+(4*bits.length+4)=budget bits tail := by unfold budget word; omega
  rw [ht] at hj
  have he : Composition.leftConfig 5
      (initialConfiguration (TapeEmbedding.machine 2 Streaming.machine) (Fin.addCases (motive:=fun _ : Fin (3+2) => List Bool)
        (fun i : Fin 3 => if i.val=0 then frame word else []) (fun _ : Fin 2 => [])))=
      initialConfiguration machine (input word) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at hj
  have hpick : ∀ i : Fin 5,RecoveryFocus.pick slots i=(![none,some 0,none,some 1,some 2] : Fin 5→Option (Fin 3)) i := by
    intro i; fin_cases i
    · decide
    · exact RecoveryFocus.pick_slot slots (by decide) 0
    · decide
    · exact RecoveryFocus.pick_slot slots (by decide) 1
    · exact RecoveryFocus.pick_slot slots (by decide) 2
  refine ⟨Composition.joinedReceipt (TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base) focused,hj,?_,?_⟩
  · change Composition.rightConfig 5 focused.final=_
    rw [hff,hlf]
    dsimp only [ambient]
    rw [hbf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hpick,isolated,
        Streaming.finished,Streaming.config,TapeEmbedding.config,Fin.addCases,output]
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hpick,isolated,
        Streaming.finished,Streaming.config,TapeEmbedding.config,Fin.addCases,output,word]
  · change base.steps+1+focused.steps=_
    rw [hbs,hfs,hls]
    exact ht

end NearCubicWires.RepairOrdinary.PCPPQueryInput
