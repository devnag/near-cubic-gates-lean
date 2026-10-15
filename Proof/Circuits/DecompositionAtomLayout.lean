import Proof.Circuits.DecompositionSignedTail

/-! One finite ordinary signed-atom controller. The native parser runs once;
its physical nonzero flag selects the shared serializer/pair tail or a
one-transition empty-code field for zero. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtom
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : ℕ} (_ : Machine t s) := s
noncomputable def prepare := TapeEmbedding.machine 165 DecompositionMagnitudeReady.machine
def zeroMachine : Machine 175 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun i => if i=162 then some false else none,fun _ => .stay⟩
noncomputable def sizes : Fin 3 → ℕ := ![18,stateCount DecompositionSignedTail.machine,2]
noncomputable def programs : (j : Fin 3) → Machine 175 (sizes j)
  | ⟨0,_⟩ => prepare
  | ⟨1,_⟩ => DecompositionSignedTail.machine
  | ⟨2,_⟩ => zeroMachine
  | ⟨n+3,h⟩ => False.elim (by omega)
noncomputable def next (j : Fin 3) (_ : Fin (sizes j)) (bs : Fin 175 → Bool) : Option (Fin 3) :=
  ![some (if bs 8 then 1 else 2),none,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def initial (source : List Bool) (pos : ℕ) :=
  TapeEmbedding.config (fun _ : Fin 165 => 0) (fun _ => [])
    (DecompositionMagnitudeReady.entry source pos)
noncomputable def entry (source : List Bool) (pos : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 0) (initial source pos)
def prepared (pre tail : List Bool) (z : ℤ) :=
  TapeEmbedding.config (fun _ : Fin 165 => 0) (fun _ => [])
    (DecompositionMagnitudeReady.prepared (pre++intWord z++tail) (pre.length+(intWord z).length) z)
def budget (z : ℤ) := 20*natBitLength z.natAbs+DecompositionSignedTail.budget z+28

theorem prepare_run (pre tail : List Bool) (z : ℤ) :
    ∃ r,runFrom prepare (20*natBitLength z.natAbs+24)
      (initial (pre++intWord z++tail) pre.length)=some r ∧
      r.final=prepared pre tail z ∧ r.steps=20*natBitLength z.natAbs+24 := by
  obtain ⟨base,hb,bf,bs⟩ := DecompositionMagnitudeReady.ready_run pre tail z
  have h := TapeEmbedding.run_embed DecompositionMagnitudeReady.machine
    (fun _ : Fin 165 => 0) (fun _ => []) _ _ base hb
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 165 => 0) (fun _ => []) base,h,?_,bs⟩
  change TapeEmbedding.config (fun _ : Fin 165 => 0) (fun _ => []) base.final=_
  rw [bf]
  rfl

theorem prepared_flag (pre tail : List Bool) (z : ℤ) :
    (prepared pre tail z).scanned 8=decide (0<z.natAbs) := by
  change readTapeBit [DecompositionBitFields.present
    (SignedSortKey.binary (natBitLength z.natAbs) z.natAbs)] 0=_
  exact DecompositionMagnitudeReady.native_present _

theorem positive_entry (pre tail : List Bool) (z : ℤ) :
    RecoveryCalls.restarted (programs 1) (prepared pre tail z).heads (prepared pre tail z).tapes=
      DecompositionSignedTail.entry pre tail z := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def zeroOutput (heads : Fin 175 → ℕ) (tapes : Fin 175 → List Bool) : Configuration 175 2 :=
  ⟨1,heads,Function.update tapes 162 [false]⟩

theorem zero_run (heads : Fin 175 → ℕ) (tapes : Fin 175 → List Bool)
    (hh : heads 162=0) (ht : tapes 162=[]) :
    ∃ r,runFrom zeroMachine 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=zeroOutput heads tapes ∧ r.steps=1 := by
  have h : step zeroMachine ⟨0,heads,tapes⟩=some (zeroOutput heads tapes) := by
    simp only [step,zeroMachine,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i; rfl
    · funext i
      by_cases hi : i=162
      · subst i; simp [applyAction,zeroOutput,hh,ht,writeTapeBit]
      · simp [applyAction,zeroOutput,hi]
  exact (Timed.single (by rfl) h).run (by rfl)

end NearCubicWires.RepairOrdinary.DecompositionAtom
