import Proof.Supplier.RowTupleAdvance

/-! The live selected-tuple output shares the binary incrementer's erased
workspace. Appending restores the tuple head and retains its exact bytes. -/
namespace NearCubicWires.RepairOrdinary.RowTupleOutputParts
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowTupleFilterParts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (w k : ℕ) (x : Data) (flag : Bool) (out : List Bool) : Configuration 18 s :=
  TapeEmbedding.config (fun _ : Fin 1=>out.length) (fun _=>out) (RowTupleAdvance.cfg q w k x flag)
noncomputable def candidate := TapeEmbedding.machine 4 RowTupleCandidate.machine
noncomputable def advance := TapeEmbedding.machine 1 RowTupleAdvance.machine
def filtered (w k n : ℕ) (x : Data) : Data :=
  RowTupleFilterMeaning.fold (RowTupleCandidate.restarted x) (RowTupleDigits.digits w k n)

theorem candidate_run (w k n M : ℕ) (x : Data) (flag : Bool) (out : List Bool)
    (hn : n<2^(w*k)) (hM : 0<M) (hMw : M≤2^w)
    (hx : x.source=frame (binary (w*k+1) n)) (hb : x.bound=M-1) (hp : x.previous<2^w) :
    ∃ r,runFrom candidate (k*(40*w+68)+10) (cfg candidate.start w k x flag out)=some r ∧
      r.final.heads=(cfg candidate.start w k (filtered w k n x) flag out).heads ∧
      r.final.tapes=(cfg candidate.start w k (filtered w k n x) flag out).tapes ∧
      r.steps=k*(40*w+68)+10 := by
  obtain ⟨a,ha,ah,atapes,_,_,as⟩ := RowTupleCandidate.candidate_run w k n M x hn hM hMw hx hb hp
  let eh : Fin 4→ℕ := ![0,0,0,out.length]
  let et : Fin 4→List Bool := ![frame (binary (w*k+1) (2^(w*k)-1)),[flag],
    List.replicate (2*(w*k)+3) false,out]
  have hr := TapeEmbedding.run_embed RowTupleCandidate.machine eh et _ _ a ha
  have hi : TapeEmbedding.config eh et (RowTupleFilterReusable.cfg RowTupleCandidate.machine.start w k x)=
      cfg candidate.start w k x flag out := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨TapeEmbedding.receipt eh et a,hr,?_,?_,as⟩
  · change (TapeEmbedding.config eh et a.final).heads=_
    simp only [TapeEmbedding.config,ah]
    funext i; fin_cases i <;> rfl
  · change (TapeEmbedding.config eh et a.final).tapes=_
    simp only [TapeEmbedding.config,atapes]
    funext i; fin_cases i <;> rfl

theorem advance_run (w k n : ℕ) (x : Data) (flag : Bool) (out : List Bool)
    (hn : n<2^(w*k)) (hx : x.source=frame (binary (w*k+1) n)) :
    ∃ r,runFrom advance (8*(w*k)+17) (cfg advance.start w k x flag out)=some r ∧
      r.final.heads=(cfg advance.start w k (RowTupleAdvance.next w k n x) (decide (n+1<2^(w*k))) out).heads ∧
      r.final.tapes=(cfg advance.start w k (RowTupleAdvance.next w k n x) (decide (n+1<2^(w*k))) out).tapes ∧
      r.steps≤8*(w*k)+17 := by
  obtain ⟨a,ha,ah,atapes,as⟩ := RowTupleAdvance.next_run w k n x flag hn hx
  have hr := TapeEmbedding.run_embed RowTupleAdvance.machine (fun _ : Fin 1=>out.length)
    (fun _=>out) _ _ a ha
  refine ⟨TapeEmbedding.receipt (fun _=>out.length) (fun _=>out) a,hr,?_,?_,as⟩
  · change (TapeEmbedding.config _ _ a.final).heads=_
    simp only [TapeEmbedding.config,ah]
    rfl
  · change (TapeEmbedding.config _ _ a.final).tapes=_
    simp only [TapeEmbedding.config,atapes]
    rfl

def slots : Fin 3→Fin 18 := ![0,17,16]
theorem injective : Function.Injective slots := by decide
noncomputable def append := RecoveryFocus.machine slots PCPSerializerReuse.copyMachine
theorem pick (i : Fin 18) : RecoveryFocus.pick slots i=
    if i=0 then some 0 else if i=17 then some 1 else if i=16 then some 2 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2
    | decide

theorem append_run (w k n : ℕ) (x : Data) (flag : Bool) (out : List Bool)
    (hx : x.source=frame (binary (w*k+1) n)) :
    ∃ r,runFrom append (4*(w*k)+8) (cfg append.start w k x flag out)=some r ∧
      r.final.heads=(cfg append.start w k x flag (out++x.source)).heads ∧
      r.final.tapes=(cfg append.start w k x flag (out++x.source)).tapes ∧
      r.steps≤4*(w*k)+8 := by
  obtain ⟨a,ha,ah,atapes,as⟩ := PCPSerializerReuse.copy_run [] (binary (w*k+1) n) [] out (2*(w*k)+3)
    (by simp only [binary_length]; omega)
  simp only [binary_length] at ha as
  have he : 4*(w*k+1)+4=4*(w*k)+8 := by omega
  rw [he] at ha as
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots injective PCPSerializerReuse.copyMachine
    (cfg append.start w k x flag out).heads (cfg append.start w k x flag out).tapes _ _ a ha
  have hi : RecoveryFocus.config slots (cfg append.start w k x flag out).heads
      (cfg append.start w k x flag out).tapes
      (PCPSerializerReuse.copyEntry [] (binary (w*k+1) n) [] out (2*(w*k)+3))=
      cfg append.start w k x flag out := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · change x.source=[]++frame (binary (w*k+1) n)++[]
        simpa only [List.nil_append,List.append_nil] using hx
      · rfl
      · rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.le.trans as⟩
  · rw [rf]
    simp only [RecoveryFocus.config,ah,List.length_nil,←hx]
    funext i; fin_cases i <;> simp [pick,cfg,TapeEmbedding.config,Fin.addCases,
      RowTupleAdvance.cfg,RowTupleFilterReusable.cfg,RowTupleFilterReusable.heads]
  · rw [rf]
    simp only [RecoveryFocus.config,atapes,List.nil_append,List.append_nil,←hx]
    funext i; fin_cases i <;> simp [pick,cfg,TapeEmbedding.config,Fin.addCases,
      RowTupleAdvance.cfg,RowTupleAdvance.extra]
    rfl

end NearCubicWires.RepairOrdinary.RowTupleOutputParts
