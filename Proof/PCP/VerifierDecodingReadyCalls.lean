import Proof.PCP.VerifierDecodingReadyLayout

/-! Fixed enclosing controller for guarded decode, successful counter
restoration, and tag-width production. Rejected codes stop immediately. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Ready
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 3 → ℕ := ![Fintype.card (RecoveryCalls.Control Whole.sizes),6,13]
noncomputable def programs : (j : Fin 3) → Machine 21 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 1 Whole.machine
  | ⟨1,_⟩ => TapeEmbedding.machine 1 ReadyCounters.machine
  | ⟨2,_⟩ => ReadyLayout.machine
  | ⟨n+3,h⟩ => False.elim (by omega)
def next : (j : Fin 3) → Fin (sizes j) → (Fin 21 → Bool) → Option (Fin 3)
  | ⟨0,_⟩,_,bits => if bits 19 then some 1 else none
  | ⟨1,_⟩,_,_ => some 2
  | ⟨2,_⟩,_,_ => none
  | ⟨n+3,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (c : ℕ) := 128*(c+1)^2
noncomputable def initial (word : List Bool) (limit : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 0)
    (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) (Whole.initial word limit))
noncomputable def endpoint (word fields : List Bool) (limit t s x y : ℕ) (out : State) :=
  let last := ReadyLayout.output (ReadyCounters.output (Whole.endpoint word fields limit t s x y out)) t
  RecoveryCalls.stopped sizes last.heads last.tapes
def Outcome (word : List Bool) (limit : ℕ)
    (final : Configuration 21 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  final.scanned 19=Whole.valid word limit ∧
    (Whole.valid word limit=true → ∃ t s fields x y, ∃ out : State,
      HeaderMachine.parts word=some (t,s,fields) ∧ 2≤t ∧ 0<s ∧
    final=endpoint word fields limit t s x y out ∧ out.bits=[] ∧
    out.pre++frame out.bits=(FrontTable.tableState fields t s).pre++
      frame (FrontTable.tableState fields t s).bits)

theorem call_prefix (node dest : Fin 3) (fuel : ℕ)
    (input : Configuration 21 (sizes node)) (r : ExecutionReceipt 21 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=some dest) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (controlConfig (RecoveryCalls.code sizes dest)
        (RecoveryCalls.restarted (programs dest) r.final.heads r.final.tapes)) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next node dest r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem stop_prefix (node : Fin 3) (fuel : ℕ)
    (input : Configuration 21 (sizes node)) (r : ExecutionReceipt 21 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem success_tail (word fields : List Bool) (limit t s x y : ℕ) (out : State)
    (hp : HeaderMachine.parts word=some (t,s,fields)) (he : 2^t*s ≤ word.length) :
    ∃ n, n≤11*word.length+16 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1)
        (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
          (ReadyCounters.input (Whole.endpoint word fields limit t s x y out))))
        (endpoint word fields limit t s x y out) := by
  obtain ⟨r,hr,hf,hs,hbound⟩ := ReadyCounters.endpoint_reset word fields limit t s x y out hp he
  have hembed := TapeEmbedding.run_embed ReadyCounters.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => []) _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) r
  have hcall := call_prefix 1 2 (s+2^t*s+5) _ first hembed (by rfl)
  have hfirst : first.final=TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [])
      (ReadyCounters.output (Whole.endpoint word fields limit t s x y out)) := by
    change TapeEmbedding.config _ _ r.final=_
    rw [hf]
  rw [hfirst] at hcall
  have htape := ReadyLayout.endpoint_tape word fields limit t s x y out
  have hlen := GuardedPreparation.parts_lengths hp
  obtain ⟨tail,htail,hfinal,hsteps⟩ := ReadyLayout.width_run
    (ReadyCounters.output (Whole.endpoint word fields limit t s x y out)) word.length t
    (by omega) htape.1 htape.2
  have hstop := stop_prefix 2 (9*t+9) _ tail htail (by rfl)
  rw [hfinal] at hstop
  have hall := hcall.trans hstop
  refine ⟨_,?_,hall⟩
  change r.steps+1+tail.steps+1≤_
  omega

end NearCubicWires.RepairSource.VerifierDecoding.Ready
