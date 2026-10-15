import Proof.MachineModel.OrdinaryTransitionTapeRun
import Proof.MachineModel.OrdinaryTransitionHeadLoad
import Proof.MachineModel.OrdinaryTransitionHeadAppend

/-! Actual head-array load/store phases around the per-tape transition. The
large event stream and witness/tag cursors remain in the embedded parent. -/
namespace NearCubicWires.RepairOrdinary.TransitionArray
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap : ℕ)
    (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 18 s :=
  TapeEmbedding.config (![pos,out.length] : Fin 2 → ℕ) (![source,out] : Fin 2 → List Bool)
    (TransitionTape.cfg q d w cap)
def loaded (d : TransitionTape.Store) (head : ℕ) : TransitionTape.Store :=
  {d with head:={d.head with head:=head}}

def loadSlots : Fin 3 → Fin 18 := ![16,6,10]
def appendSlots : Fin 4 → Fin 18 := ![6,7,17,10]
def incrementSlots : Fin 2 → Fin 18 := ![15,10]
noncomputable def loadProgram := RecoveryFocus.machine loadSlots FrameLoad.machine
noncomputable def tapeProgram := TapeEmbedding.machine 2 TransitionTape.machine
noncomputable def appendProgram := RecoveryFocus.machine appendSlots TransitionHeadAppend.machine
noncomputable def incrementProgram := RecoveryFocus.machine incrementSlots FramedIncrement.machine

theorem load_place {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap : ℕ)
    (source : List Bool) (pos nextPos : ℕ) (out : List Bool) (head : ℕ) :
    RecoveryFocus.config loadSlots (cfg q d w cap source pos out).heads (cfg q d w cap source pos out).tapes
      (TransitionHeadLoad.cfg q source nextPos (frame (binary w head)) cap)=
      cfg q (loaded d head) w cap source nextPos out := by
  apply TransitionEvent.focused_eq loadSlots (by decide) (cfg q d w cap source pos out)
  · rfl
  · intro j; fin_cases j <;> simp [cfg,TapeEmbedding.config,Fin.addCases,loadSlots,
      TransitionHeadLoad.cfg,TransitionTape.cfg]
  · intro j; fin_cases j <;> simp [cfg,TapeEmbedding.config,Fin.addCases,loadSlots,
      TransitionHeadLoad.cfg,TransitionTape.cfg,loaded]
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 1 rfl) | rfl

theorem load_run (d : TransitionTape.Store) (w cap head : ℕ) (pre post out : List Bool)
    (hc : 2*w+1≤cap) :
    ∃ r,runFrom loadProgram (4*w+3)
      (cfg loadProgram.start d w cap (pre++frame (binary w head)++post) pre.length out)=some r ∧
      r.final=cfg 3 (loaded d head) w cap (pre++frame (binary w head)++post)
        (pre.length+2*w+1) out := by
  let source := pre++frame (binary w head)++post
  obtain ⟨base,hb,hf,_⟩ := TransitionHeadLoad.load_run pre (binary w head) post
    (frame (binary w d.head.head)) cap (by simp) (by simpa using hc)
  simp only [binary_length] at hb hf
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config loadSlots (by decide) _
    (cfg (0 : Fin 4) d w cap source pre.length out).heads
    (cfg (0 : Fin 4) d w cap source pre.length out).tapes _ _ base hb
  have hi : RecoveryFocus.config loadSlots (cfg (0 : Fin 4) d w cap source pre.length out).heads
      (cfg (0 : Fin 4) d w cap source pre.length out).tapes
      (TransitionHeadLoad.cfg 0 source pre.length (frame (binary w d.head.head)) cap)=
      cfg 0 d w cap source pre.length out := load_place 0 d w cap source pre.length pre.length out d.head.head
  rw [hi] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hf]
  exact load_place 3 d w cap source pre.length _ out head

theorem tape_run (d : TransitionTape.Store) (w cap : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool)
    (tagPre tagTail scanPre scanTail : List Bool) (bits : TagMachine.Word) (bit : Bool)
    (hv : TagMachine.valid true bits=true)
    (ht : d.source=tagPre++Streaming.marks (TagMachine.tagWord bits)++tagTail)
    (hp : d.pos=tagPre.length) (hs : d.scans=scanPre++true::bit::scanTail)
    (hc : d.cursor=scanPre.length) (hserial : d.serial+1<2^(2*w))
    (hhead : d.head.head+1<2^w) (hback : d.head.difference.length≤2*w+1) (hcap : 4*w+3≤cap) :
    ∃ r,runFrom tapeProgram (TransitionTape.budget w) (cfg tapeProgram.start d w cap source pos out)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode TransitionTape.sizes none)
        (TransitionTape.finished d w cap bits bit) w cap source pos out := by
  obtain ⟨base,hb,hf,_⟩ := TransitionTape.tape_run d w cap tagPre tagTail scanPre scanTail bits bit
    hv ht hp hs hc hserial hhead hback hcap
  have hr := TapeEmbedding.run_embed TransitionTape.machine (![pos,out.length] : Fin 2 → ℕ)
    (![source,out] : Fin 2 → List Bool) _ _ base hb
  refine ⟨TapeEmbedding.receipt (![pos,out.length] : Fin 2 → ℕ) (![source,out] : Fin 2 → List Bool) base,hr,?_⟩
  simp only [TapeEmbedding.receipt,hf]
  rfl

theorem append_place {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap : ℕ)
    (source : List Bool) (pos : ℕ) (out nextOut : List Bool) :
    RecoveryFocus.config appendSlots (cfg q d w cap source pos out).heads (cfg q d w cap source pos out).tapes
      (KeyPrefix.ready q (frame (binary w d.head.head)) (frame (binary w 1)) nextOut cap)=
      cfg q d w cap source pos nextOut := by
  apply TransitionEvent.focused_eq appendSlots (by decide) (cfg q d w cap source pos out)
  · rfl
  · intro j; fin_cases j <;> simp [cfg,TapeEmbedding.config,Fin.addCases,appendSlots,KeyPrefix.ready,TransitionTape.cfg]
  · intro j; fin_cases j <;> simp [cfg,TapeEmbedding.config,Fin.addCases,appendSlots,KeyPrefix.ready,TransitionTape.cfg]
  · intro i h; fin_cases i <;> first | exact False.elim (h 2 rfl) | rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 2 rfl) | rfl

theorem append_run (d : TransitionTape.Store) (w cap : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool)
    (hc : 2*w≤cap) :
    ∃ r,runFrom appendProgram (4*w+4) (cfg appendProgram.start d w cap source pos out)=some r ∧
      r.final=cfg 5 d w cap source pos (out++frame (binary w d.head.head)) := by
  obtain ⟨base,hb,hf⟩ := TransitionHeadAppend.append_run (binary w d.head.head) (binary w 1) out cap
    (by simp) (by simpa using hc)
  simp only [binary_length] at hb
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config appendSlots (by decide) _
    (cfg (0 : Fin 6) d w cap source pos out).heads (cfg (0 : Fin 6) d w cap source pos out).tapes _ _ base hb
  rw [append_place] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hf]
  exact append_place 5 d w cap source pos out _

theorem increment_place {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap : ℕ)
    (source : List Bool) (pos : ℕ) (out : List Bool) (tape : ℕ) :
    RecoveryFocus.config incrementSlots (cfg q d w cap source pos out).heads (cfg q d w cap source pos out).tapes
      (⟨q,fun _ => 0,![frame (binary w tape),List.replicate cap false]⟩ : Configuration 2 s)=
      cfg q {d with tape:=tape} w cap source pos out := by
  apply TransitionEvent.focused_eq incrementSlots (by decide) (cfg q d w cap source pos out)
  · rfl
  · intro j; fin_cases j <;> simp [cfg,TapeEmbedding.config,Fin.addCases,incrementSlots,TransitionTape.cfg]
  · intro j; fin_cases j <;> simp [cfg,TapeEmbedding.config,Fin.addCases,incrementSlots,TransitionTape.cfg]
  · intro i h; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl

theorem increment_run (d : TransitionTape.Store) (w cap : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool)
    (ht : d.tape+1<2^w) (hc : 2*w≤cap) :
    ∃ r,runFrom incrementProgram (4*w+2) (cfg incrementProgram.start d w cap source pos out)=some r ∧
      r.final=cfg 4 {d with tape:=d.tape+1} w cap source pos out := by
  obtain ⟨base,hb,ht0,ht1,hh,_,_⟩ := FramedIncrement.increment_run w d.tape cap ht hc
  have hf : base.final=(⟨4,fun _ => 0,![frame (binary w (d.tape+1)),List.replicate cap false]⟩ : Configuration 2 5) := by
    apply configuration_ext
    · have halted := (prefix_of_run FramedIncrement.machine (4*w+2) _ base hb).2
      exact (by decide : ∀ q : Fin 5,FramedIncrement.machine.halted q=true → q=4) _ halted
    · exact funext hh
    · funext i; fin_cases i
      · exact ht0
      · exact ht1
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config incrementSlots (by decide) _
    (cfg (0 : Fin 5) d w cap source pos out).heads (cfg (0 : Fin 5) d w cap source pos out).tapes _ _ base hb
  have hi : RecoveryFocus.config incrementSlots (cfg (0 : Fin 5) d w cap source pos out).heads
      (cfg (0 : Fin 5) d w cap source pos out).tapes
      (initialConfiguration FramedIncrement.machine (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
        (fun _ : Fin 1 => frame (binary w d.tape)) (fun _ : Fin 1 => List.replicate cap false)))=
      cfg 0 d w cap source pos out := by
    have hin : initialConfiguration FramedIncrement.machine
        (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
          (fun _ : Fin 1 => frame (binary w d.tape)) (fun _ : Fin 1 => List.replicate cap false))=
        (⟨0,fun _ => 0,![frame (binary w d.tape),List.replicate cap false]⟩ : Configuration 2 5) := by
      apply configuration_ext
      · rfl
      · rfl
      · funext i; fin_cases i <;> rfl
    rw [hin]
    exact increment_place 0 d w cap source pos out d.tape
  rw [hi] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hf]
  exact increment_place 4 d w cap source pos out _

end NearCubicWires.RepairOrdinary.TransitionArray
