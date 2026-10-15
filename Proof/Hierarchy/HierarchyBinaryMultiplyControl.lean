import Proof.Hierarchy.HierarchyBinaryMultiplyTapes

/-! Fixed finite shift/add control: physically read one factor bit, optionally
accumulate, double the multiplicand, copy both duplicates, and return to the
retained factor cursor. Every call return is one ordinary transition. -/
namespace NearCubicWires.RepairOrdinary.HierarchyMultiply
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reader : Machine 8 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => 2≤q.val
  rule := fun q bits => if q.val=0 then
    some ⟨if bits 0 then 1 else 4,fun _ => none,
      fun i => if i.val=0 && bits 0 then .right else .stay⟩
    else if q.val=1 then some ⟨if bits 0 then 3 else 2,fun _ => none,
      fun i => if i.val=0 then .right else .stay⟩ else none
def readerConfig (q : Fin 5) (s : Store) (w pos : ℕ) (source : List Bool) : Configuration 8 5 :=
  ⟨q,heads pos,s.tapes w source⟩

theorem reader_bit (s : Store) (w : ℕ) (pre bits : List Bool) (bit : Bool) :
    Timed reader 2 (readerConfig 0 s w pre.length (pre++frame (bit::bits)))
      (readerConfig (if bit then 3 else 2) s w (pre.length+2) (pre++frame (bit::bits))) := by
  have hm : readTapeBit (pre++frame (bit::bits)) pre.length=true := by
    simpa only [frame,List.append_assoc] using Streaming.read_append pre (bit::frame bits) true
  have hb : readTapeBit (pre++frame (bit::bits)) (pre.length+1)=bit := by
    simpa [frame,List.append_assoc] using Streaming.read_append (pre++[true]) (frame bits) bit
  have h0 : step reader (readerConfig 0 s w pre.length (pre++frame (bit::bits)))=
      some (readerConfig 1 s w (pre.length+1) (pre++frame (bit::bits))) := by
    simp [step,reader,readerConfig,Configuration.scanned,Store.tapes,heads,hm]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have h1 : step reader (readerConfig 1 s w (pre.length+1) (pre++frame (bit::bits)))=
      some (readerConfig (if bit then 3 else 2) s w (pre.length+2) (pre++frame (bit::bits))) := by
    simp [step,reader,readerConfig,Configuration.scanned,Store.tapes,heads,hb]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)

theorem reader_end (s : Store) (w : ℕ) (pre : List Bool) :
    Timed reader 1 (readerConfig 0 s w pre.length (pre++frame []))
      (readerConfig 4 s w pre.length (pre++frame [])) := by
  have he : readTapeBit (pre++frame []) pre.length=false := by
    simpa only [frame,List.append_nil] using Streaming.read_append pre [] false
  apply Timed.single (by rfl)
  simp [step,reader,readerConfig,Configuration.scanned,Store.tapes,heads,he]
  rfl

def sizes : Fin 6 → ℕ := ![5,7,6,7,6,6]
noncomputable def programs : (j : Fin 6) → Machine 8 (sizes j)
  | ⟨0,_⟩ => reader
  | ⟨1,_⟩ => addProgram
  | ⟨2,_⟩ => accProgram
  | ⟨3,_⟩ => doubleProgram
  | ⟨4,_⟩ => leftProgram
  | ⟨5,_⟩ => duplicateProgram
  | ⟨n+6,h⟩ => False.elim (by omega)
def next (j : Fin 6) (q : Fin (sizes j)) (_ : Fin 8 → Bool) : Option (Fin 6) :=
  if j.val=0 then if q.val=3 then some 1 else if q.val=2 then some 3 else none
  else if j.val=1 then some 2 else if j.val=2 then some 3
  else if j.val=3 then some 4 else if j.val=4 then some 5 else some 0
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def atNode (j : Fin 6) (s : Store) (w pos : ℕ) (source : List Bool) :=
  controlConfig (RecoveryCalls.code sizes j)
    (RecoveryCalls.restarted (programs j) (heads pos) (s.tapes w source))

theorem scalar_call (j dest : Fin 6) (s out : Store) (w pos time : ℕ) (source : List Bool)
    (hr : Run (programs j) time w pos source s out)
    (hn : ∀ q bits,next j q bits=some dest) :
    Timed machine (time+1) (atNode j s w pos source) (atNode dest out w pos source) := by
  obtain ⟨r,hr,hh,ht,hs⟩ := hr
  obtain ⟨hp,hhalt⟩ := prefix_of_run (programs j) time _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next j dest r.final hhalt (hn _ _)
  rw [hs] at hb
  have htgt : RecoveryCalls.restarted (programs dest) r.final.heads r.final.tapes=
      RecoveryCalls.restarted (programs dest) (heads pos) (out.tapes w source) := by rw [hh,ht]
  rw [htgt] at he
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem shift_calls (s : Store) (w pos : ℕ) (source : List Bool)
    (hfit : s.left+s.duplicate<2^w) (hb : s.doubled.length≤2*w+1) :
    Timed machine (20*w+23) (atNode 3 s w pos source)
      (atNode 0 (shiftedBoth (doubled s w)) w pos source) := by
  have h0 := scalar_call 3 4 s (doubled s w) w pos (4*w+4) source
    (double_run s w pos source hfit hb) (by intros; rfl)
  have h1 := scalar_call 4 5 (doubled s w) (shiftedLeft (doubled s w)) w pos (8*w+8) source
    (left_run s w pos source) (by intros; rfl)
  have h2 := scalar_call 5 0 (shiftedLeft (doubled s w)) (shiftedBoth (doubled s w)) w pos (8*w+8) source
    (duplicate_run s w pos source) (by intros; rfl)
  have ht : ((4*w+4+1)+(8*w+8+1))+(8*w+8+1)=20*w+23 := by omega
  simpa only [ht] using (h0.trans h1).trans h2

theorem accumulation_calls (s : Store) (w pos : ℕ) (source : List Bool)
    (hfit : s.left+s.accumulator<2^w) (hb : s.sum.length≤2*w+1) :
    Timed machine (12*w+14) (atNode 1 s w pos source)
      (atNode 3 (accumulated (added s w)) w pos source) := by
  have h0 := scalar_call 1 2 s (added s w) w pos (4*w+4) source
    (add_run s w pos source hfit hb) (by intros; rfl)
  have h1 := scalar_call 2 3 (added s w) (accumulated (added s w)) w pos (8*w+8) source
    (accumulate_run s w pos source) (by intros; rfl)
  have ht : (4*w+4+1)+(8*w+8+1)=12*w+14 := by omega
  simpa only [ht] using h0.trans h1

end NearCubicWires.RepairOrdinary.HierarchyMultiply
