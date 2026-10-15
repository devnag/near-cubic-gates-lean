import Proof.MachineModel.GeneratedAmplifierHeader
import Proof.MachineModel.OrdinaryMatrixUnaryTemplate

/-! The actual framed arity header supplies its own bit width and unary
arity. The table cursor survives the complete conversion, including n=0. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Arity
open LocalBitMultitape RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bits_value (n : ℕ) : value n.bits=n := by
  have h (bits : List Bool) : value bits=CanonicalBinary.bitsValue bits := by
    induction bits with
    | nil => rfl
    | cons b bits ih => simp only [value,CanonicalBinary.bitsValue,ih]
  exact (h n.bits).trans (CanonicalBinary.bitsValue_natBits n)
theorem binary_bits (n : ℕ) : binary n.bits.length n=n.bits := by
  simpa only [bits_value] using BoundedCounter.binary_of_value n.bits
theorem bits_fit (n : ℕ) : n<2^n.bits.length := by
  simpa only [bits_value] using value_lt n.bits

def slots : Fin 7→Fin 9 := ![2,4,5,6,7,1,8]
def header := TapeEmbedding.machine 5 Header.machine
noncomputable def unary := RecoveryFocus.machine slots MatrixUnaryTemplate.machine
noncomputable def machine := Composition.machine header unary
def input (source : List Bool) : Fin 9→List Bool := fun i => if i=0 then source else []
def budget (n : ℕ) := 4*n.bits.length+4+1+MatrixUnaryTemplate.budget n.bits.length n

theorem arity_run (n : ℕ) (tail : List Bool) :
    ∃ r,run machine (budget n) (input (frame n.bits++tail))=some r ∧ r.steps≤budget n ∧
      r.final.tapes 0=frame n.bits++tail ∧ r.final.heads 0=2*n.bits.length+1 ∧
      r.final.tapes 8=UnaryTemplate.tape n ∧ r.final.heads 8=1 := by
  obtain ⟨base,hb,hf,hs⟩ := Header.header_run [] n.bits tail
  simp only [List.nil_append,List.length_nil] at hb hf
  have he := TapeEmbedding.run_embed Header.machine (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base.final
  obtain ⟨last,hl,_,_,hout,hhead,_,hsteps⟩ := MatrixUnaryTemplate.template_run n.bits.length n (bits_fit n)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes
      (initialConfiguration MatrixUnaryTemplate.machine (MatrixUnaryTemplate.input n.bits.length n))=
      Composition.restart ambient unary.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,TapeEmbedding.config,Header.finished,initialConfiguration,Fin.addCases]
    · intro i
      dsimp only [ambient]
      rw [hf]
      fin_cases i <;> simp [slots,TapeEmbedding.config,Header.finished,initialConfiguration,MatrixUnaryTemplate.input,binary_bits,Fin.addCases]
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixUnaryTemplate.machine
    ambient.heads ambient.tapes _ _ last hl
  rw [hi] at hfocus
  have hj := Composition.run_join header unary _ _ _
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused he hfocus
  have hentry : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 5 => 0)
      (fun _ : Fin 5 => []) (Header.entry (frame n.bits++tail) 0))=
      initialConfiguration machine (input (frame n.bits++tail)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hentry] at hj
  have hn : RecoveryFocus.pick slots (0 : Fin 9)=none := by decide
  have hother : focused.final.tapes 0=frame n.bits++tail ∧ focused.final.heads 0=2*n.bits.length+1 := by
    simp only [hff,RecoveryFocus.config,hn]
    dsimp only [ambient]
    rw [hf]
    simp [TapeEmbedding.config,Header.finished,Fin.addCases]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused,hj,?_,hother.1,hother.2,?_,?_⟩
  · change base.steps+1+focused.steps≤_
    rw [hs,hfs]
    unfold budget
    omega
  · change focused.final.tapes (slots 6)=_
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact hout
  · change focused.final.heads (slots 6)=_
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
    exact hhead

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Arity
