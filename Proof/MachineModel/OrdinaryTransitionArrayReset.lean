import Proof.MachineModel.OrdinaryTransitionArrayMove
import Proof.MachineModel.OrdinaryTransitionTapeZero

/-! Return only the two bounded head-array cursors after the physical array
loop. The event append cursor and both source cursors retain their endpoints. -/
namespace NearCubicWires.RepairOrdinary.TransitionArrayReuse
open LocalBitMultitape RecoveryExecution SignedSortKey TransitionArray
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 18) : Bool := i.val==16 || i.val==17
def capacities (C : ℕ) (i : Fin 18) : ℕ := if selected i then C else 0
def cfg19 {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap C : ℕ)
    (source out : List Bool) : Configuration 19 s :=
  ⟨q,Fin.addCases (motive := fun _ : Fin (18+1) => ℕ)
      (Fin.addCases (motive := fun _ : Fin (16+2) => ℕ) (TransitionTape.cfg q d w cap).heads (fun _ => 0)) (fun _ => 0),
    Fin.addCases (motive := fun _ : Fin (18+1) => List Bool)
      (Fin.addCases (motive := fun _ : Fin (16+2) => List Bool) (TransitionTape.cfg q d w cap).tapes ![source,out])
      (fun _ => List.replicate (C+1) false)⟩
def cfg {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap C : ℕ)
    (source out : List Bool) : Configuration 20 s :=
  TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => List.replicate C true) (cfg19 q d w cap C source out)

noncomputable def resetProgram := TapeEmbedding.machine 1 (MaskedReset.machine loop selected)

theorem selected_left (i : Fin 16) : selected (i.castAdd 2)=false := by
  have h16 : i.val≠16 := by omega
  have h17 : i.val≠17 := by omega
  simp [selected,h16,h17]
theorem selected_right (i : Fin 2) : selected (i.natAdd 16)=true := by fin_cases i <;> rfl

theorem pad_arrays {s : ℕ} (c : Configuration 16 s) (heads : Fin 2 → ℕ)
    (tapes : Fin 2 → List Bool) (C : ℕ) :
    ZeroPadding.config (capacities C) (TapeEmbedding.config heads tapes c)=
      TapeEmbedding.config heads (fun i => ZeroPadding.pad C (tapes i)) c := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (motive := fun i =>
      (ZeroPadding.config (capacities C) (TapeEmbedding.config heads tapes c)).tapes i=
      (TapeEmbedding.config heads (fun j => ZeroPadding.pad C (tapes j)) c).tapes i)
      (fun j : Fin 16 => ?_) (fun j : Fin 2 => ?_) i
    · simp [ZeroPadding.config,capacities,selected_left,TapeEmbedding.config]
    · simp [ZeroPadding.config,capacities,selected_right,TapeEmbedding.config]

theorem reset_heads (heads : Fin 16 → ℕ) (extra : Fin 2 → ℕ) :
    (fun i : Fin 18 => if selected i then 0 else Fin.addCases heads extra i)=
      Fin.addCases (motive := fun _ : Fin (16+2) => ℕ) heads (fun _ : Fin 2 => 0) := by
  funext i
  refine Fin.addCases (motive := fun i =>
    (if selected i then 0 else Fin.addCases heads extra i)=
      Fin.addCases (motive := fun _ : Fin (16+2) => ℕ) heads (fun _ => 0) i)
    (fun j : Fin 16 => ?_) (fun j : Fin 2 => ?_) i
  · simp [selected_left]
  · simp [selected_right]

theorem pad_recording {t s : ℕ} (c : Configuration t s) (C : ℕ) :
    ZeroPadding.config (Rewind.Workspace.capacities t C) (Rewind.recording c 0)=
      Rewind.config (c.control.castAdd 2) c.heads c.tapes 0 (List.replicate C false) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j : Fin t => ?_) (fun j : Fin 1 => ?_) i <;>
      simp [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,ZeroPadding.pad]

theorem recording_place {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap C : ℕ) (source : List Bool) :
    ZeroPadding.config (Rewind.Workspace.capacities 18 (C+1))
      (Rewind.recording (ZeroPadding.config (capacities C) (TransitionArray.cfg q d w cap source 0 [])) 0)=
      cfg19 (q.castAdd 2) d w cap C (ZeroPadding.pad C source) (List.replicate C false) := by
  rw [pad_recording]
  unfold TransitionArray.cfg
  rw [pad_arrays]
  apply configuration_ext
  · rfl
  · have hh : (![0,0] : Fin 2 → ℕ)=fun _ => 0 := by funext i; fin_cases i <;> rfl
    simp only [Rewind.config,TapeEmbedding.config,cfg19,List.length_nil]
    rw [hh]
    rfl
  · have ht : (fun i : Fin 2 => ZeroPadding.pad C (![source,[]] i))=
        (![ZeroPadding.pad C source,List.replicate C false] : Fin 2 → List Bool) := by
      funext i; fin_cases i <;> simp [ZeroPadding.pad]
    simp only [Rewind.config,TapeEmbedding.config,cfg19]
    rw [ht]
    rfl

theorem reset_place {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap C pos : ℕ) (source out : List Bool) :
    let c := ZeroPadding.config (capacities C) (TransitionArray.cfg q d w cap source pos out)
    SelectiveReset.finished (s:=s) (fun i => if selected i then 0 else c.heads i) c.tapes (C+1)=
      cfg19 ((1 : Fin 2).natAdd s) d w cap C (ZeroPadding.pad C source) (ZeroPadding.pad C out) := by
  dsimp only
  unfold TransitionArray.cfg
  rw [pad_arrays]
  change Rewind.config _ (fun i => if selected i then 0 else Fin.addCases
      (TransitionTape.cfg q d w cap).heads (![pos,out.length] : Fin 2 → ℕ) i) _ _ _=_
  rw [reset_heads]
  apply configuration_ext
  · rfl
  · rfl
  · have ht : (fun i : Fin 2 => ZeroPadding.pad C (![source,out] i))=
        (![ZeroPadding.pad C source,ZeroPadding.pad C out] : Fin 2 → List Bool) := by
      funext i; fin_cases i <;> rfl
    simp only [Rewind.config,TapeEmbedding.config,cfg19]
    rw [ht]
    rfl

theorem reset_run (w cap C : ℕ) (entries : List Item) (d : TransitionTape.Store)
    (tagPre tagTail scanPre scanTail : List Bool)
    (hvalid : ∀ e∈entries,RepairSource.VerifierDecoding.TagMachine.valid true e.tag=true)
    (hheads : ∀ e∈entries,e.head+1<2^w)
    (hserial : d.serial+entries.length<2^(2*w)) (htape : d.tape+entries.length<2^w)
    (hback : d.head.difference.length≤2*w+1) (hcap : 4*w+3≤cap) (hC : loopBudget w entries.length≤C)
    (htag : d.source=tagPre++Streaming.marks (tags entries)++tagTail) (hpos : d.pos=tagPre.length)
    (hscan : d.scans=scanPre++Streaming.marks (scans entries)++scanTail) (hcursor : d.cursor=scanPre.length) :
    ∃ r,runFrom resetProgram (2*C+2)
      (cfg resetProgram.start d w cap C (ZeroPadding.pad C (fields w entries)) (List.replicate C false))=some r ∧
      r.final=cfg ((1 : Fin 2).natAdd (bodyStates+2)) (walk w cap d entries) w cap C
        (ZeroPadding.pad C (fields w entries)) (ZeroPadding.pad C (nextFields w entries)) := by
  obtain ⟨base,hb,hf⟩ := loop_run w cap entries d [] [] tagPre tagTail scanPre scanTail
    hvalid hheads hserial htape hback hcap htag hpos hscan hcursor
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hb hf
  obtain ⟨padded,hp,hpf,hps,_⟩ := ZeroPadding.run_config loop (capacities C) _ _ base hb
  have hstart : ∀ i,selected i=true →
      (ZeroPadding.config (capacities C) (TransitionArray.cfg (RecordController.test bodyStates) d w cap (fields w entries) 0 [])).heads i=0 := by
    intro i hi
    fin_cases i <;> simp [selected] at hi <;> rfl
  have hsteps := runFrom_steps_le loop _ _ base hb
  obtain ⟨reset,hr,hrf,_,_⟩ := MaskedReset.workspace_run loop selected _ (C+1) _ padded hp hstart (by omega)
  rw [recording_place] at hr
  have hmore := runFrom_moreFuel (MaskedReset.machine loop selected) _ ((2*C+2)-(2*padded.steps+2)) _ reset hr
  have hbound : 2*padded.steps+2≤2*C+2 := by omega
  rw [Nat.add_sub_of_le hbound] at hmore
  have hfinal : reset.final=cfg19 ((1 : Fin 2).natAdd (bodyStates+2)) (walk w cap d entries) w cap C
      (ZeroPadding.pad C (fields w entries)) (ZeroPadding.pad C (nextFields w entries)) := by
    rw [hrf,hpf,hf,reset_place]
  have he := TapeEmbedding.run_embed (MaskedReset.machine loop selected) (fun _ : Fin 1 => 0)
    (fun _ => List.replicate C true) _ _ reset hmore
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ => List.replicate C true) reset,he,?_⟩
  simp only [TapeEmbedding.receipt,hfinal]
  rfl

end NearCubicWires.RepairOrdinary.TransitionArrayReuse
