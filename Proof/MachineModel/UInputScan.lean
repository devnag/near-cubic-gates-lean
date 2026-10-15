import Proof.MachineModel.UInputSyntax

/-! One fixed finite all-input scan.  Every logical bit is read through its
external framing marker; reaching that outer delimiter certifies the end of
the actual input, rather than accepting delimiters from blank tape. -/
namespace NearCubicWires.RepairOrdinary.UInputScan
open LocalBitMultitape RecoveryExecution UInputSyntax
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outer (q : Fin 7) : Fin 15 := ⟨2*q.val,by omega⟩
def payload (q : Fin 7) : Fin 15 := ⟨2*q.val+1,by omega⟩
def phase (s : Fin 15) : Fin 7 := ⟨(s.val/2)%7,Nat.mod_lt _ (by omega)⟩
def raw : Machine 2 15 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==14
  rule := fun s scan =>
    if s.val=14 then none else if s.val%2=0 then
      some (if scan 0 then ⟨payload (phase s),fun _ => none,![.right,.stay]⟩
        else ⟨14,![none,some ((phase s).val==6)],fun _ => .stay⟩)
    else some ⟨outer (advance (phase s) (scan 0)),fun _ => none,![.right,.stay]⟩
def config (s : Fin 15) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 15 :=
  ⟨s,![pos,0],![source,out]⟩

theorem pair (q : Fin 7) (pre tail : List Bool) (b : Bool) :
    Timed raw 2 (config (outer q) (pre++frame (b::tail)) pre.length [])
      (config (outer (advance q b)) (pre++frame (b::tail)) (pre.length+2) []) := by
  have hm : readTapeBit (pre++frame (b::tail)) pre.length=true :=
    Streaming.read_append pre (b::frame tail) true
  have hb : readTapeBit (pre++frame (b::tail)) (pre.length+1)=b := by
    have h := Streaming.read_append (pre++[true]) (frame tail) b
    simpa [frame,List.append_assoc] using h
  have h1 : step raw (config (outer q) (pre++frame (b::tail)) pre.length [])=
      some (config (payload q) (pre++frame (b::tail)) (pre.length+1) []) := by
    fin_cases q <;> simp [step,raw,config,outer,payload,phase,Configuration.scanned,hm]
    all_goals
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
  have h2 : step raw (config (payload q) (pre++frame (b::tail)) (pre.length+1) [])=
      some (config (outer (advance q b)) (pre++frame (b::tail)) (pre.length+2) []) := by
    fin_cases q <;> simp [step,raw,config,outer,payload,phase,Configuration.scanned,hb]
    all_goals
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
  have hn1 : raw.halted (config (outer q) (pre++frame (b::tail)) pre.length []).control=false := by
    fin_cases q <;> rfl
  have hn2 : raw.halted (config (payload q) (pre++frame (b::tail)) (pre.length+1) []).control=false := by
    fin_cases q <;> rfl
  exact (Timed.single hn1 h1).trans (Timed.single hn2 h2)

theorem finish (q : Fin 7) (pre : List Bool) :
    Timed raw 1 (config (outer q) (pre++frame []) pre.length [])
      (config 14 (pre++frame []) pre.length [q.val==6]) := by
  have hm : readTapeBit (pre++frame []) pre.length=false := Streaming.read_append pre [] false
  have h : step raw (config (outer q) (pre++frame []) pre.length [])=
      some (config 14 (pre++frame []) pre.length [q.val==6]) := by
    fin_cases q <;> simp [step,raw,config,outer,phase,Configuration.scanned,hm]
    all_goals
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
  exact Timed.single (by fin_cases q <;> rfl) h

theorem scan (q : Fin 7) (pre bits : List Bool) :
    Timed raw (2*bits.length+1) (config (outer q) (pre++frame bits) pre.length [])
      (config 14 (pre++frame bits) (pre.length+2*bits.length) [accepts q bits]) := by
  induction bits generalizing q pre with
  | nil => simpa using finish q pre
  | cons b tail ih =>
    have hp := pair q pre tail b
    have ht := ih (advance q b) (pre++[true,b])
    have he : (pre++[true,b])++frame tail=pre++frame (b::tail) := by simp [frame,List.append_assoc]
    rw [he,show (pre++[true,b]).length=pre.length+2 by simp] at ht
    have h := hp.trans ht
    simpa [List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,accepts_cons] using h

theorem raw_run (bits : List Bool) :
    ∃ r,run raw (2*bits.length+1) ![frame bits,[]]=some r ∧
      r.final=config 14 (frame bits) (2*bits.length) [accepts 0 bits] ∧
      r.steps=2*bits.length+1 := by
  have h := scan 0 [] bits
  have hi : config (outer 0) ([]++frame bits) 0 []=
      initialConfiguration raw ![frame bits,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  simp only [List.length_nil] at h
  rw [hi] at h
  simpa only [run,List.nil_append,List.length_nil,Nat.zero_add] using h.run (by rfl)

def machine := Rewind.machine raw
def input (bits : List Bool) : Fin 3 → List Bool := ![frame bits,[],[]]
def output (bits : List Bool) : Fin 3 → List Bool :=
  ![frame bits,[accepts 0 bits],List.replicate (2*bits.length+1) false]

theorem ready (bits : List Bool) :
    ClockJoin.ReadyRun machine (4*bits.length+4) (input bits) (output bits) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run bits
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw
    (2*bits.length+1) ![frame bits,[]] base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![frame bits,[]] (fun _ : Fin 1 => []))=input bits := by
    funext i; fin_cases i <;> rfl
  change run machine (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![frame bits,[]] (fun _ : Fin 1 => []))=some r at hr
  rw [hi,hs,show 2*(2*bits.length+1)+2=4*bits.length+4 by omega] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · simpa [output,hf,config] using ht 0
  · simpa [output,hf,config] using ht 1
  · simpa [output,hs] using hcounter

theorem entry_run (bits : List Bool) :
    ∃ r,run machine (4*bits.length+4) (input bits)=some r ∧
      r.final.tapes 0=frame bits ∧
      (r.final.tapes 1=[true] ↔ Fields bits) ∧
      (bits.length < 2 → r.final.tapes 1=[false]) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ 4*bits.length+4 := by
  obtain ⟨r,hr,hf,hh,hs⟩ := ready bits
  refine ⟨r,hr,by simp [hf,output],?_,?_,hh,hs⟩
  · simpa [hf,output] using accepts_iff bits
  · intro h
    simp [hf,output,short_reject bits (by omega)]

end NearCubicWires.RepairOrdinary.UInputScan
