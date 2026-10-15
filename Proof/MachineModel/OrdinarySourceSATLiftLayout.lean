import Proof.MachineModel.OrdinarySourceSATLiftCodec
import Proof.MachineModel.OrdinaryOracleComposeHandoff

/-! Fixed reusable query kernel. Four finite arithmetic banks share only
successive result/operand fields. The original query is a borrowed read-only
source; one external unary capacity drives every paid workspace clear. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlot (i : Fin 153) : Fin 156 := ⟨3 + i.val, by omega⟩
def bank (k : Fin 4) (i : Fin 38) : Fin 156 := ⟨3 + 38*k.val + i.val, by omega⟩
def pairSlots (k : Fin 4) (i : Fin 38) : Fin 156 :=
  if k.val = 1 ∧ i.val = 2 then bank 0 26
  else if k.val = 2 ∧ i.val = 2 then bank 1 26
  else if k.val = 3 ∧ i.val = 3 then bank 2 26
  else bank k i
def oneSlot (k : Fin 4) : Fin 156 := if k.val = 0 ∨ k.val = 3 then bank k 2 else bank k 3
def eraseSlots : Fin 155 → Fin 156 :=
  Fin.addCases (m := 154) (n := 1) (motive := fun _ => Fin 156)
    (Fin.addCases (m := 153) (n := 1) (motive := fun _ => Fin 156) workSlot
      (fun _ : Fin 1 => 1)) (fun _ : Fin 1 => 2)
def printerSlots (k : Fin 4) : Fin 2 → Fin 156 := ![oneSlot k,155]
def queryCopySlots : Fin 3 → Fin 156 := ![0,bank 0 3,155]

theorem work_injective : Function.Injective workSlot := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 156 => x.val) h
  dsimp [workSlot] at hv
  omega

theorem bank_injective (k : Fin 4) : Function.Injective (bank k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 156 => x.val) h
  dsimp [bank] at hv
  omega

theorem pair_injective (k : Fin 4) : Function.Injective (pairSlots k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 156 => x.val) h
  have hi := i.isLt
  have hj := j.isLt
  fin_cases k <;> dsimp [pairSlots, bank] at hv <;> (try split_ifs at hv) <;>
    (try dsimp at hv) <;> omega

theorem pair_work (k : Fin 4) (i : Fin 38) : 3 ≤ (pairSlots k i).val ∧ (pairSlots k i).val < 155 := by
  have hk := k.isLt
  have hi := i.isLt
  dsimp [pairSlots, bank]
  split_ifs <;> dsimp <;> omega

theorem erase_injective : Function.Injective eraseSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 156 => x.val) h
  have he (i : Fin 155) : (eraseSlots i).val = if i.val < 153 then 3+i.val else i.val-152 := by
    refine Fin.addCases (m := 154) (n := 1) (fun a => ?_) (fun a => ?_) i
    · refine Fin.addCases (m := 153) (n := 1) (fun b => ?_) (fun b => ?_) a
      · simp [eraseSlots, workSlot]
      · fin_cases b; simp [eraseSlots]; rfl
    · fin_cases a; simp [eraseSlots]; rfl
  rw [he, he] at hv
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at hv <;> omega

theorem printer_injective (k : Fin 4) : Function.Injective (printerSlots k) := by
  have hk := k.isLt
  have h : oneSlot k ≠ (155 : Fin 156) := by
    intro he
    have hv := congrArg (fun x : Fin 156 => x.val) he
    dsimp [oneSlot, bank] at hv
    split_ifs at hv <;> dsimp at hv <;> omega
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [printerSlots]

theorem copy_injective : Function.Injective queryCopySlots := by decide

abbrev Packed := Σ s : ℕ, Machine 156 s
def pack {s : ℕ} (p : Machine 156 s) : Packed := ⟨s,p⟩
noncomputable def focused {t s : ℕ} (slot : Fin t → Fin 156) (p : Machine t s) : Packed :=
  pack (RecoveryFocus.machine slot p)

noncomputable def call (j : Fin 10) : Packed :=
  match j.val with
  | 0 => focused eraseSlots (RecoveryScratchErase.resetMachine 153)
  | 1 => focused (printerSlots 0) (HierarchyFixedWord.machine (frame [true]))
  | 2 => focused (printerSlots 1) (HierarchyFixedWord.machine (frame [true]))
  | 3 => focused (printerSlots 2) (HierarchyFixedWord.machine (frame [true]))
  | 4 => focused (printerSlots 3) (HierarchyFixedWord.machine (frame [true]))
  | 5 => focused queryCopySlots PCPFieldMoves.readyMachine
  | 6 => focused (pairSlots 0) PCPPairCanonical.machine
  | 7 => focused (pairSlots 1) PCPPairCanonical.machine
  | 8 => focused (pairSlots 2) PCPPairCanonical.machine
  | _ => focused (pairSlots 3) PCPPairCanonical.machine
noncomputable def sizes (j : Fin 10) := (call j).1
noncomputable def programs (j : Fin 10) : Machine 156 (sizes j) := (call j).2
def next (j : Fin 10) (_ : Fin (sizes j)) (_ : Fin 156 → Bool) : Option (Fin 10) :=
  if j.val = 9 then none else some ⟨(j.val+1)%10, Nat.mod_lt _ (by decide)⟩
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

noncomputable def atCall (j : Fin 10) (tapes : Fin 156 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) tapes)
def Path (j k : Fin 10) (fuel : ℕ) (before after : Fin 156 → List Bool) : Prop :=
  ∃ n ≤ fuel, Timed machine n (atCall j before) (atCall k after)

theorem Path.trans {j k l : Fin 10} {a b : ℕ} {x y z : Fin 156 → List Bool}
    (h : Path j k a x y) (g : Path k l b y z) : Path j l (a+b) x z := by
  obtain ⟨n,hn,ht⟩ := h
  obtain ⟨m,hm,gt⟩ := g
  exact ⟨n+m,by omega,ht.trans gt⟩

theorem ready_path (j k : Fin 10) (p : Packed) (hp : call j = p)
    (fuel : ℕ) (input output : Fin 156 → List Bool)
    (h : ClockJoin.ReadyRun p.2 fuel input output)
    (hn : ∀ q scanned, next j q scanned = some k) : Path j k (fuel+1) input output := by
  subst p
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  obtain ⟨n,hb,hpath⟩ := call_receipt sizes programs 0 next j k fuel
    (initialConfiguration (programs j) input) r hr (hn _ _)
  have he : RecoveryCalls.restarted (programs k) r.final.heads r.final.tapes =
      initialConfiguration (programs k) output := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [he] at hpath
  exact ⟨n,hb,hpath⟩

theorem finish_path {fuel last : ℕ} {input middle output : Fin 156 → List Bool}
    (h : Path 0 9 fuel input middle)
    (g : ClockJoin.ReadyRun (programs 9) last middle output) :
    ClockJoin.ReadyRun machine (fuel+last+1) input output := by
  obtain ⟨n,hn,hpath⟩ := h
  obtain ⟨r,hr,ht,hh,hs⟩ := g
  obtain ⟨m,hm,hlast⟩ := stop_receipt sizes programs 0 next 9 last
    (initialConfiguration (programs 9) middle) r hr (by rfl)
  have he : RecoveryCalls.stopped sizes r.final.heads r.final.tapes =
      RecoveryCalls.stopped sizes (fun _ : Fin 156 => 0) output := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [he] at hlast
  have whole := hpath.trans hlast
  obtain ⟨out,ho,hf,hsteps⟩ := whole.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb : n+m ≤ fuel+last+1 := by omega
  have hmore := runFrom_moreFuel machine (n+m) (fuel+last+1-(n+m)) _ out ho
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨out,hmore,by simp [hf,RecoveryCalls.stopped],
    by intro i; simp [hf,RecoveryCalls.stopped],hsteps.trans_le hb⟩

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
