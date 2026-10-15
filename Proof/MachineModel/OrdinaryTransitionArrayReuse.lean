import Proof.MachineModel.OrdinaryTransitionArrayReuseTapes

/-! One complete transition's tape-array event production, with all local
arrays and the tape id returned for the next paid transition lookup. -/
namespace NearCubicWires.RepairOrdinary.TransitionArrayReuse
open LocalBitMultitape RecoveryExecution SignedSortKey TransitionArray
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 3 → ℕ := ![bodyStates+4,4,5]
noncomputable def programs : (j : Fin 3) → Machine 20 (sizes j)
  | ⟨0,_⟩ => resetProgram
  | ⟨1,_⟩ => moveProgram
  | ⟨2,_⟩ => zeroProgram
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (_ : Fin 20 → Bool) : Option (Fin 3) :=
  if h:j.val<2 then some ⟨j.val+1,by omega⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_phase (j k : Fin 3) (d e : TransitionTape.Store) (w cap C : ℕ)
    (source out nextSource nextOut : List Bool) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 20 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d w cap C source out)=some r)
    (hf : r.final=cfg q e w cap C nextSource nextOut) (hn : ∀ c bits,next j c bits=some k) :
    ∃ n≤fuel+1,Timed machine n
      (cfg (RecoveryCalls.code sizes j (programs j).start) d w cap C source out)
      (cfg (RecoveryCalls.code sizes k (programs k).start) e w cap C nextSource nextOut) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next j k r.final hh (hn _ _)
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at h
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,h⟩

theorem stop_phase (j : Fin 3) (d e : TransitionTape.Store) (w cap C : ℕ)
    (source out nextSource nextOut : List Bool) (q : Fin (sizes j)) (fuel : ℕ)
    (r : ExecutionReceipt 20 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d w cap C source out)=some r)
    (hf : r.final=cfg q e w cap C nextSource nextOut) (hn : ∀ c bits,next j c bits=none) :
    ∃ n≤fuel+1,Timed machine n
      (cfg (RecoveryCalls.code sizes j (programs j).start) d w cap C source out)
      (cfg (RecoveryCalls.controlCode sizes none) e w cap C nextSource nextOut) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next j r.final hh (hn _ _)
  have h := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at h
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,h⟩

theorem fields_length (w : ℕ) (es : List Item) : (fields w es).length=es.length*(2*w+1) := by
  induction es with
  | nil => simp [fields]
  | cons e es ih => simp [fields,ih]; ring
theorem nextFields_length (w : ℕ) (es : List Item) : (nextFields w es).length=es.length*(2*w+1) := by
  induction es with
  | nil => simp [nextFields]
  | cons e es ih => simp [nextFields,ih]; ring
theorem fields_budget (w n : ℕ) : n*(2*w+1)≤loopBudget w n := by
  have h : n*(2*w+1)≤n*(bodyBudget w+2) := Nat.mul_le_mul_left n (by dsimp [bodyBudget]; omega)
  dsimp [loopBudget]
  omega

def finished (w cap : ℕ) (d : TransitionTape.Store) (es : List Item) : TransitionTape.Store :=
  {walk w cap d es with tape:=0}
def budget (w C : ℕ) : ℕ := 4*C+4*w+13

theorem reuse_run (w cap C : ℕ) (entries : List Item) (d : TransitionTape.Store)
    (tagPre tagTail scanPre scanTail : List Bool)
    (hvalid : ∀ e∈entries,RepairSource.VerifierDecoding.TagMachine.valid true e.tag=true)
    (hheads : ∀ e∈entries,e.head+1<2^w)
    (hserial : d.serial+entries.length<2^(2*w)) (htape : d.tape+entries.length<2^w)
    (hback : d.head.difference.length≤2*w+1) (hcap : 4*w+3≤cap) (hC : loopBudget w entries.length≤C)
    (htag : d.source=tagPre++Streaming.marks (tags entries)++tagTail) (hpos : d.pos=tagPre.length)
    (hscan : d.scans=scanPre++Streaming.marks (scans entries)++scanTail) (hcursor : d.cursor=scanPre.length) :
    ∃ r,runFrom machine (budget w C)
      (cfg machine.start d w cap C (ZeroPadding.pad C (fields w entries)) (List.replicate C false))=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (finished w cap d entries) w cap C
        (ZeroPadding.pad C (nextFields w entries)) (List.replicate C false) ∧ r.steps≤budget w C := by
  let source := ZeroPadding.pad C (fields w entries)
  let out := ZeroPadding.pad C (nextFields w entries)
  let d1 := walk w cap d entries
  have hsource : source.length=C := by
    dsimp [source]
    rw [ZeroPadding.pad_length,fields_length,max_eq_left ((fields_budget w entries.length).trans hC)]
  have hout : out.length=C := by
    dsimp [out]
    rw [ZeroPadding.pad_length,nextFields_length,max_eq_left ((fields_budget w entries.length).trans hC)]
  obtain ⟨r0,hr0,hf0⟩ := reset_run w cap C entries d tagPre tagTail scanPre scanTail
    hvalid hheads hserial htape hback hcap hC htag hpos hscan hcursor
  obtain ⟨n0,hn0,hp0⟩ := call_phase 0 1 d d1 w cap C source (List.replicate C false) source out _ _ r0 hr0 hf0
    (by intro c bits; rfl)
  obtain ⟨r1,hr1,hf1⟩ := move_run d1 w cap C source out hsource.le hout
  obtain ⟨n1,hn1,hp1⟩ := call_phase 1 2 d1 d1 w cap C source out out (List.replicate C false) _ _ r1 hr1 hf1
    (by intro c bits; rfl)
  obtain ⟨r2,hr2,hf2⟩ := zero_run d1 w cap C out (List.replicate C false) (by omega)
  obtain ⟨n2,hn2,hp2⟩ := stop_phase 2 d1 (finished w cap d entries) w cap C out (List.replicate C false)
    out (List.replicate C false) _ _ r2 hr2 hf2 (by intro c bits; rfl)
  have hj := (hp0.trans hp1).trans hp2
  have hn : n0+n1+n2≤budget w C := by dsimp [budget]; omega
  obtain ⟨r,hr,hf,hsteps⟩ := hj.run
    (by simp [machine,RecoveryCalls.machine,RecoveryCalls.controlCode,cfg,TapeEmbedding.config,cfg19])
  have hm := runFrom_moreFuel machine _ (budget w C-(n0+n1+n2)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hf,by omega⟩

end NearCubicWires.RepairOrdinary.TransitionArrayReuse
