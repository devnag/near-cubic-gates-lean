import Proof.Hierarchy.CompetitorRawCount

/-! One actual streaming numerator update. The raw native-width count is
loaded and widened, added to the retained accumulator, and copied back with
paid local resets. The global matrix cursor is never rewound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountAccumulator
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  accumulator : ℕ
  field : List Bool
  sum : List Bool

def Store.tapes (s : Store) (b w : ℕ) (source : List Bool) : Fin 8 → List Bool :=
  fun i => match i.val with
    | 0 => source
    | 1 => List.replicate b true
    | 2 => List.replicate w true
    | 3 => s.field
    | 4 => List.replicate (2*w+1) false
    | 5 => frame (binary w s.accumulator)
    | 6 => s.sum
    | _ => List.replicate (4*w+3) false
def heads (pos : ℕ) : Fin 8 → ℕ := fun i => if i.val=0 then pos else 0
def cfg {states : ℕ} (q : Fin states) (s : Store) (b w : ℕ) (source : List Bool) (pos : ℕ) :
    Configuration 8 states := ⟨q,heads pos,s.tapes b w source⟩
def loaded (s : Store) (w x : ℕ) : Store := {s with field := frame (binary w x)}
def added (s : Store) (w x : ℕ) : Store := {s with sum := frame (binary w (x+s.accumulator))}
def accumulated (s : Store) (x : ℕ) : Store := {s with accumulator := x+s.accumulator}

def loadProgram : Machine 8 4 := TapeEmbedding.machine 3 CompetitorRawCell.machine
def addSlots : Fin 4 → Fin 8 := ![3,5,6,7]
def copySlots : Fin 4 → Fin 8 := ![6,5,4,7]
noncomputable def addProgram := RecoveryFocus.machine addSlots BoundaryAdvance.machine
noncomputable def copyProgram := RecoveryFocus.machine copySlots copyMachine
noncomputable def tailProgram := Composition.machine addProgram copyProgram
noncomputable def machine := Composition.machine loadProgram tailProgram

theorem load_run (s : Store) (pre suffix : List Bool) (b w x : ℕ)
    (hw : b≤w) (hx : x<2^b) (hb : s.field.length≤2*w+1) :
    ∃ r : ExecutionReceipt 8 4,
      runFrom loadProgram (4*w+3)
        (cfg loadProgram.start s b w (pre++binary b x++suffix) pre.length)=some r ∧
      r.final.heads=heads (pre.length+b) ∧
      r.final.tapes=(loaded s w x).tapes b w (pre++binary b x++suffix) ∧ r.steps=4*w+3 := by
  obtain ⟨base,hr,hf,hs⟩ := CompetitorRawCell.raw_count_run pre suffix s.field b w x hw hx hb
  let extra : Fin 3 → List Bool := ![frame (binary w s.accumulator),s.sum,List.replicate (4*w+3) false]
  have hrun := TapeEmbedding.run_embed CompetitorRawCell.machine (fun _ : Fin 3 => 0) extra _ _ base hr
  have hi : TapeEmbedding.config (fun _ : Fin 3 => 0) extra
      (CompetitorRawCell.cfg 0 (pre++binary b x++suffix) pre.length b w s.field)=
      cfg loadProgram.start s b w (pre++binary b x++suffix) pre.length := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hrun
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 3 => 0) extra base,hrun,?_,?_,hs⟩
  · simp only [TapeEmbedding.receipt,hf]
    funext i; fin_cases i <;> rfl
  · simp only [TapeEmbedding.receipt,hf]
    funext i; fin_cases i <;> rfl

theorem add_run (s : Store) (source : List Bool) (pos b w x : ℕ)
    (hfit : x+s.accumulator<2^w) (hb : s.sum.length≤2*w+1) :
    ∃ r : ExecutionReceipt 8 7,
      runFrom addProgram (4*w+4)
        (cfg addProgram.start (loaded s w x) b w source pos)=some r ∧
      r.final.heads=heads pos ∧
      r.final.tapes=(added (loaded s w x) w x).tapes b w source ∧ r.steps=4*w+4 := by
  have h := HierarchyBinary.add_ready w x s.accumulator (4*w+3) s.sum hfit hb
  simp only [max_eq_left (by omega : 2*w+1≤4*w+3)] at h
  obtain ⟨r,hr,hh,ht,hs⟩ := HierarchyBinary.focused_run addSlots (by decide) _ _ _ h
    (heads pos) ((loaded s w x).tapes b w source) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,hh,?_,hs⟩
  rw [ht]
  funext i; fin_cases i
  all_goals first
    | exact install_slot addSlots (by decide) _ _ 0
    | exact install_slot addSlots (by decide) _ _ 1
    | exact install_slot addSlots (by decide) _ _ 2
    | exact install_slot addSlots (by decide) _ _ 3
    | exact install_other addSlots _ _ _ (by decide)

theorem copy_run (s : Store) (source : List Bool) (pos b w x : ℕ) :
    ∃ r : ExecutionReceipt 8 6,
      runFrom copyProgram (8*w+8)
        (cfg copyProgram.start (added (loaded s w x) w x) b w source pos)=some r ∧
      r.final.heads=heads pos ∧
      r.final.tapes=(accumulated (added (loaded s w x) w x) x).tapes b w source ∧ r.steps=8*w+8 := by
  have h := copy_ready (binary w (x+s.accumulator)) (frame (binary w s.accumulator))
    (2*w+1) (4*w+3) (by simp)
  simp only [binary_length,max_self] at h
  obtain ⟨r,hr,hh,ht,hs⟩ := HierarchyBinary.focused_run copySlots (by decide) _ _ _ h
    (heads pos) ((added (loaded s w x) w x).tapes b w source) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,hh,?_,hs⟩
  rw [ht]
  funext i; fin_cases i
  all_goals first
    | exact install_slot copySlots (by decide) _ _ 0
    | exact install_slot copySlots (by decide) _ _ 1
    | exact install_slot copySlots (by decide) _ _ 2
    | exact install_slot copySlots (by decide) _ _ 3
    | exact install_other copySlots _ _ _ (by decide)

theorem accumulate_run (s : Store) (pre suffix : List Bool) (b w x : ℕ)
    (hw : b≤w) (hx : x<2^b) (hfit : x+s.accumulator<2^w)
    (hf : s.field.length≤2*w+1) (hs : s.sum.length≤2*w+1) :
    ∃ r : ExecutionReceipt 8 17,
      runFrom machine (16*w+17)
        (cfg machine.start s b w (pre++binary b x++suffix) pre.length)=some r ∧
      r.final.heads=heads (pre.length+b) ∧
      r.final.tapes=(accumulated (added (loaded s w x) w x) x).tapes b w
        (pre++binary b x++suffix) ∧ r.steps=16*w+17 := by
  let source := pre++binary b x++suffix
  let pos := pre.length+b
  obtain ⟨load,hl,hlh,hlt,hls⟩ := load_run s pre suffix b w x hw hx hf
  obtain ⟨add,ha,hah,hat,has⟩ := add_run s source pos b w x hfit hs
  obtain ⟨copy,hc,hch,hct,hcs⟩ := copy_run s source pos b w x
  have hcopy : Composition.restart add.final copyProgram.start=
      cfg copyProgram.start (added (loaded s w x) w x) b w source pos := by
    apply configuration_ext
    · rfl
    · exact hah
    · exact hat
  have hc' : runFrom copyProgram (8*w+8) (Composition.restart add.final copyProgram.start)=some copy := by
    rw [hcopy]
    exact hc
  have htail := Composition.run_join addProgram copyProgram (4*w+4) (8*w+8) _ add copy ha hc'
  let tail := Composition.joinedReceipt add copy
  have hrestart : Composition.restart load.final tailProgram.start=
      Composition.leftConfig 6 (cfg addProgram.start (loaded s w x) b w source pos) := by
    apply configuration_ext
    · rfl
    · exact hlh
    · exact hlt
  have htail' : runFrom tailProgram ((4*w+4)+1+(8*w+8))
      (Composition.restart load.final tailProgram.start)=some tail := by
    rw [hrestart]
    exact htail
  have hall := Composition.run_join loadProgram tailProgram (4*w+3) ((4*w+4)+1+(8*w+8))
    _ load tail hl htail'
  have he : (4*w+3)+1+((4*w+4)+1+(8*w+8))=16*w+17 := by omega
  rw [he] at hall
  refine ⟨Composition.joinedReceipt load tail,hall,hch,hct,?_⟩
  change load.steps+1+(add.steps+1+copy.steps)=16*w+17
  omega

end NearCubicWires.RepairOrdinary.CompetitorCountAccumulator
