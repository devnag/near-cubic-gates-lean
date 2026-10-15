import Proof.MachineModel.OrdinaryMemoryEmitReady

/-! One entire ordinary memory-event emission. The exact read/after bits,
serial and cell key are appended as one framed record. Both scalar inputs
and width drivers are restored; the event stream is never rewound. -/
namespace NearCubicWires.RepairOrdinary.MemoryRecordEmitter
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (serial key out : List Bool) (read after : Bool)
    (cap : ℕ) : Configuration 8 s :=
  ⟨state, ![0,0,out.length,0,0,0,0,0],
    ![serial,List.replicate serial.length true,out,List.replicate cap false,
      key,List.replicate key.length true,[read],[after]]⟩
@[simp] theorem config_cells {s : ℕ} (state : Fin s) (serial key out : List Bool)
    (read after : Bool) (cap : ℕ) :
    (config state serial key out read after cap).tapeCells =
      2*serial.length+2*key.length+out.length+cap+2 := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega
def headerAction (next : Fin 5) (bit : Bool) : Action 8 5 :=
  ⟨next, fun i => if i = 2 then some bit else none,
    fun i => if i = 2 then .right else .stay⟩
def header : Machine 8 5 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 4
  rule := fun s scanned =>
    if s.val = 0 then some (headerAction 1 true)
    else if s.val = 1 then some (headerAction 2 (scanned 6))
    else if s.val = 2 then some (headerAction 3 true)
    else if s.val = 3 then some (headerAction 4 (scanned 7)) else none

theorem header_step (phase : Fin 4) (serial key out : List Bool) (read after : Bool) (cap : ℕ) :
    step header (config phase.castSucc serial key out read after cap) =
      some (config phase.succ serial key (out++[![true,read,true,after] phase]) read after cap) := by
  fin_cases phase <;> simp [step, header, config, Configuration.scanned, readTapeBit]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;>
    simp [applyAction, headerAction, HeadMove.apply, Streaming.write_append])

theorem header_run (serial key out : List Bool) (read after : Bool) (cap : ℕ) :
    ∃ r : ExecutionReceipt 8 5,
      runFrom header 4 (config 0 serial key out read after cap) = some r ∧
      r.final = config 4 serial key (out++[true,read,true,after]) read after cap ∧ r.steps = 4 := by
  let space := 2*serial.length+2*key.length+out.length+cap+6
  have tail : Prefix header space 0
      (config 4 serial key (out++[true,read,true,after]) read after cap)
      (config 4 serial key (out++[true,read,true,after]) read after cap) :=
    Prefix.refl _ (by simp [space]; omega)
  have p3 := Prefix.step (by simp [space]; omega :
      (config (3 : Fin 5) serial key (out++[true,read,true]) read after cap).tapeCells ≤ space)
    (by rfl : header.halted (3 : Fin 5) = false)
    (header_step 3 serial key (out++[true,read,true]) read after cap)
    (by simpa [List.append_assoc] using tail)
  have p2 := Prefix.step (by simp [space]; omega :
      (config (2 : Fin 5) serial key (out++[true,read]) read after cap).tapeCells ≤ space)
    (by rfl : header.halted (2 : Fin 5) = false)
    (header_step 2 serial key (out++[true,read]) read after cap)
    (by simpa [List.append_assoc] using p3)
  have p1 := Prefix.step (by simp [space]; omega :
      (config (1 : Fin 5) serial key (out++[true]) read after cap).tapeCells ≤ space)
    (by rfl : header.halted (1 : Fin 5) = false)
    (header_step 1 serial key (out++[true]) read after cap)
    (by simpa [List.append_assoc] using p2)
  have p0 := Prefix.step (by simp [space] :
      (config (0 : Fin 5) serial key out read after cap).tapeCells ≤ space)
    (by rfl : header.halted (0 : Fin 5) = false) (header_step 0 serial key out read after cap) p1
  obtain ⟨r, hr, hf, hs, _⟩ := p0.run (by rfl) (by simp [space]; omega)
  exact ⟨r, hr, hf, hs⟩

def serialMachine : Machine 8 5 := TapeEmbedding.machine 4 (MemoryEmitReady.machine false)
def keyLayout : Fin 8 ≃ Fin 8 where
  toFun := ![4,5,2,3,0,1,6,7]
  invFun := ![4,5,2,3,0,1,6,7]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem key_inverse : (keyLayout.symm : Fin 8 → Fin 8) = ![4,5,2,3,0,1,6,7] := rfl
def keyMachine : Machine 8 5 :=
  TapeRenaming.machine keyLayout (TapeEmbedding.machine 4 (MemoryEmitReady.machine true))
def fieldsMachine : Machine 8 10 := Composition.machine serialMachine keyMachine
def machine : Machine 8 15 := Composition.machine header fieldsMachine

theorem serial_run (serial key out : List Bool) (read after : Bool) (cap : ℕ)
    (hcap : 2*serial.length+1 ≤ cap) :
    ∃ r : ExecutionReceipt 8 5,
      runFrom serialMachine (4*serial.length+4) (config 0 serial key out read after cap) = some r ∧
      r.final = config 4 serial key (out++Streaming.marks serial) read after cap := by
  obtain ⟨r, hr, hf, _⟩ := MemoryEmitReady.field_run false serial out cap hcap
  let extra : Fin 4 → List Bool := ![key,List.replicate key.length true,[read],[after]]
  have he := TapeEmbedding.run_embed (MemoryEmitReady.machine false)
    (fun _ : Fin 4 => 0) extra _ _ r hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 4 => 0) extra r, ?_, ?_⟩
  · have hi : TapeEmbedding.config (fun _ : Fin 4 => 0) extra
        (MemoryEmitReady.config (0 : Fin 5) serial out cap) =
        config 0 serial key out read after cap := by
      apply configuration_ext
      · rfl
      · funext i
        fin_cases i <;> simp [TapeEmbedding.config, MemoryEmitReady.config, config, Fin.addCases]
      · funext i
        fin_cases i <;> simp [TapeEmbedding.config, MemoryEmitReady.config, config, extra, Fin.addCases]
    rw [hi] at he
    exact he
  · simp only [TapeEmbedding.receipt, hf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, MemoryEmitReady.config, config,
        MemoryEmitField.suffix, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, MemoryEmitReady.config, config,
        MemoryEmitField.suffix, extra, Fin.addCases]

theorem key_run (serial key out : List Bool) (read after : Bool) (cap : ℕ)
    (hcap : 2*key.length+1 ≤ cap) :
    ∃ r : ExecutionReceipt 8 5,
      runFrom keyMachine (4*key.length+4) (config 0 serial key out read after cap) = some r ∧
      r.final = config 4 serial key (out++Streaming.marks key++[false]) read after cap := by
  obtain ⟨r, hr, hf, _⟩ := MemoryEmitReady.field_run true key out cap hcap
  let extra : Fin 4 → List Bool := ![serial,List.replicate serial.length true,[read],[after]]
  have he := TapeEmbedding.run_embed (MemoryEmitReady.machine true)
    (fun _ : Fin 4 => 0) extra _ _ r hr
  have hn := TapeRenaming.run_rename keyLayout (TapeEmbedding.machine 4 (MemoryEmitReady.machine true))
    _ _ _ he
  have hi : TapeRenaming.config keyLayout (TapeEmbedding.config (fun _ : Fin 4 => 0) extra
      (MemoryEmitReady.config (0 : Fin 5) key out cap)) = config 0 serial key out read after cap := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config,
        MemoryEmitReady.config, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config,
        MemoryEmitReady.config, config, extra, Fin.addCases]
  rw [hi] at hn
  refine ⟨TapeRenaming.receipt keyLayout (TapeEmbedding.receipt (fun _ : Fin 4 => 0) extra r), hn, ?_⟩
  simp only [TapeRenaming.receipt, TapeEmbedding.receipt, hf]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config,
      MemoryEmitReady.config, config, MemoryEmitField.suffix, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config,
      MemoryEmitReady.config, config, MemoryEmitField.suffix, extra, Fin.addCases]

theorem record_run (serial key out : List Bool) (read after : Bool) (cap : ℕ)
    (hs : 2*serial.length+1 ≤ cap) (hk : 2*key.length+1 ≤ cap) :
    ∃ r : ExecutionReceipt 8 15,
      runFrom machine (4*serial.length+4*key.length+14)
        (config 0 serial key out read after cap) = some r ∧
      r.final = config 14 serial key (out++frame (read::after::serial++key)) read after cap := by
  let headerBits := out++[true,read,true,after]
  obtain ⟨head, hh, hhf, _⟩ := header_run serial key out read after cap
  obtain ⟨first, hf, hff⟩ := serial_run serial key headerBits read after cap hs
  obtain ⟨last, hl, hlf⟩ := key_run serial key (headerBits++Streaming.marks serial) read after cap hk
  have hmid : Composition.restart first.final keyMachine.start =
      config 0 serial key (headerBits++Streaming.marks serial) read after cap := by rw [hff]; rfl
  rw [← hmid] at hl
  have hj := Composition.run_join serialMachine keyMachine (4*serial.length+4) (4*key.length+4)
    (config 0 serial key headerBits read after cap) first last hf hl
  have hhead : Composition.restart head.final fieldsMachine.start =
      Composition.leftConfig 5 (config 0 serial key headerBits read after cap) := by rw [hhf]; rfl
  rw [← hhead] at hj
  have hall := Composition.run_join header fieldsMachine 4
    ((4*serial.length+4)+1+(4*key.length+4))
    (config 0 serial key out read after cap) head (Composition.joinedReceipt first last) hh hj
  have htime : 4+1+((4*serial.length+4)+1+(4*key.length+4)) =
      4*serial.length+4*key.length+14 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt head (Composition.joinedReceipt first last), hall, ?_⟩
  simp only [Composition.joinedReceipt, hlf]
  have hframe (bits : List Bool) : Streaming.marks bits++[false] = frame bits := by
    simpa only [List.append_nil, frame] using (Streaming.frame_append bits []).symm
  have hout : (headerBits++Streaming.marks serial)++Streaming.marks key++[false] =
      out++frame (read::after::serial++key) := by
    calc
      _ = headerBits++(Streaming.marks serial++Streaming.marks key++[false]) := by
        simp only [List.append_assoc]
      _ = headerBits++frame (serial++key) := by rw [← Streaming.marks_append, hframe]
      _ = _ := by simp [headerBits, frame, List.append_assoc]
  rw [hout]
  rfl

end NearCubicWires.RepairOrdinary.MemoryRecordEmitter
