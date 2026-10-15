import Proof.PCP.VerifierDecodingPreparationLayout
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! Enclosing decoder preparation from the literal code and blank work tapes.
All four component executions and all finite call-return transitions are
paid. Padding is removed only by the actual interpreter reverse simulation. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Preparation
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 4 → ℕ := ![6,8,4,4]
def programs : (j : Fin 4) → Machine 4 (sizes j)
  | ⟨0,_⟩ => lengthProgram
  | ⟨1,_⟩ => headerProgram
  | ⟨2,_⟩ => tProgram
  | ⟨3,_⟩ => sProgram
  | ⟨n+4,h⟩ => False.elim (by omega)
def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 4 → Bool) : Option (Fin 4) :=
  if j.val = 0 then some 1 else if j.val = 1 then some 2 else if j.val = 2 then some 3 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

private theorem call (j l : Fin 4) (time : ℕ) (c : Configuration 4 (sizes j))
    (d : Configuration 4 (sizes l)) (q : Fin (sizes j))
    (h : ∃ receipt, runFrom (programs j) time c = some receipt ∧
      receipt.final = ⟨q,d.heads,d.tapes⟩ ∧ receipt.steps = time)
    (hd : d.control = (programs l).start)
    (hn : ∀ state bits, next j state bits = some l) :
    Timed machine (time+1) (controlConfig (RecoveryCalls.code sizes j) c)
      (controlConfig (RecoveryCalls.code sizes l) d) := by
  obtain ⟨r,hr,hf,hs⟩ := h
  have hp := prefix_of_run (programs j) time c r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp.1⟩
  rw [hs] at hb
  have ht := RecoveryCalls.return_step sizes programs 0 next j l r.final hp.2 (hn _ _)
  have he : RecoveryCalls.restarted (programs l) r.final.heads r.final.tapes = d := by
    apply configuration_ext
    · exact hd.symm
    · simp [RecoveryCalls.restarted,hf]
    · simp [RecoveryCalls.restarted,hf]
  rw [he] at ht
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,RecoveryCalls.code,controlConfig]) ht)

private theorem stop (j : Fin 4) (time : ℕ) (c d : Configuration 4 (sizes j))
    (h : ∃ receipt, runFrom (programs j) time c = some receipt ∧ receipt.final = d ∧ receipt.steps = time)
    (hn : ∀ state bits, next j state bits = none) :
    Timed machine (time+1) (controlConfig (RecoveryCalls.code sizes j) c)
      (RecoveryCalls.stopped sizes d.heads d.tapes) := by
  obtain ⟨r,hr,hf,hs⟩ := h
  have hp := prefix_of_run (programs j) time c r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp.1⟩
  rw [hs] at hb
  have ht := RecoveryCalls.stop_step sizes programs 0 next j r.final hp.2 (hn _ _)
  rw [hf] at ht hb
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,RecoveryCalls.code,controlConfig]) ht)

theorem prepared_prefix (t s : ℕ) (fields : List Bool) :
    let word := HeaderMachine.word t s fields
    Timed machine (8*word.length+2*t+2*s+18)
      (controlConfig (RecoveryCalls.code sizes 0) (initial word))
      (RecoveryCalls.stopped sizes (finished word t s).heads (finished word t s).tapes) := by
  dsimp only
  let word := HeaderMachine.word t s fields
  have ht : t ≤ word.length := by simp [word,HeaderMachine.word]
  have hs : s ≤ word.length := by simp [word,HeaderMachine.word]; omega
  have h0 := call 0 1 (4*word.length+3) (initial word) (headerInput word) (5 : Fin 6)
    (length_layout word) rfl (by intro state bits; rfl)
  have h1 := call 1 2 (2*t+2*s+5) (headerInput word) (tInput word t s) (6 : Fin 8)
    (header_layout t s fields) rfl (by intro state bits; rfl)
  have h2 := call 2 3 (2*word.length+3) (tInput word t s) (sInput word t s) (3 : Fin 4)
    (t_layout word t s ht) rfl (by intro state bits; rfl)
  have h3 := stop 3 (2*word.length+3) (sInput word t s) (finished word t s)
    (s_layout word t s hs) (by intro state bits; rfl)
  have hp := h0.trans (h1.trans (h2.trans h3))
  have he : (4*word.length+3+1)+((2*t+2*s+5+1)+((2*word.length+3+1)+(2*word.length+3+1))) =
      8*word.length+2*t+2*s+18 := by omega
  rw [he] at hp
  exact hp

def inputCapacity (word : List Bool) : Fin 4 → ℕ := ![0,word.length+2,word.length+2,word.length+2]

/-- The entire code/header adapter starts with blank workspace. The final
padding equation is observationally exact and supplies the capped ABI to
later ordinary programs without allocating any false templates for free. -/
theorem prepared_run (t s : ℕ) (fields : List Bool) :
    let word := HeaderMachine.word t s fields
    ∃ receipt,
      run machine (8*word.length+2*t+2*s+18) ![frame word,[],[],[]] = some receipt ∧
      ZeroPadding.config (inputCapacity word) receipt.final =
        RecoveryCalls.stopped sizes (finished word t s).heads (finished word t s).tapes ∧
      receipt.steps = 8*word.length+2*t+2*s+18 := by
  dsimp only
  let word := HeaderMachine.word t s fields
  obtain ⟨r,hr,hf,hs⟩ := (prepared_prefix t s fields).run (by
    simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hi : ZeroPadding.config (inputCapacity word)
      (initialConfiguration machine ![frame word,[],[],[]]) =
      controlConfig (RecoveryCalls.code sizes 0) (initial word) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,inputCapacity,initialConfiguration,
        controlConfig,initial,zeros]
  rw [←hi] at hr
  obtain ⟨actual,ha,hfa,hsa,_⟩ := ZeroPadding.run_unpad machine (inputCapacity word) _ _ r hr
  exact ⟨actual,ha,hfa.trans hf,hsa.trans hs⟩

theorem code_as_header (v : OrdinaryVerifier) :
    VerifierEncoding.code v = HeaderMachine.word v.tapeCount v.stateCount
      (VerifierEncoding.fixedBits (natBitLength v.stateCount) v.machine.start.val ++ flags v ++ table v) := by
  rw [code_split]
  simp [HeaderMachine.word,List.append_assoc]

/-- Exact first consumer for the canonical literal verifier encoding. -/
theorem code_preparation (v : OrdinaryVerifier) :
    let word := VerifierEncoding.code v
    ∃ receipt,
      run machine (8*word.length+2*v.tapeCount+2*v.stateCount+18) ![frame word,[],[],[]] = some receipt ∧
      ZeroPadding.config (inputCapacity word) receipt.final =
        RecoveryCalls.stopped sizes (finished word v.tapeCount v.stateCount).heads
          (finished word v.tapeCount v.stateCount).tapes ∧
      receipt.steps = 8*word.length+2*v.tapeCount+2*v.stateCount+18 := by
  dsimp only
  rw [code_as_header]
  exact prepared_run _ _ _

end NearCubicWires.RepairSource.VerifierDecoding.Preparation
