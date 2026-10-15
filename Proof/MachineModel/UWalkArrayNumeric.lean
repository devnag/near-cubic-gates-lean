import Proof.MachineModel.UWalkOrdinary
import Proof.MachineModel.UHeadArrayReady

/-! The actual135-tape numeric supplier embedded with the four fresh tapes
reserved for the subsequent139-tape head-array consumer. -/
namespace NearCubicWires.RepairOrdinary.UWalkArray
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 139 → List Bool
abbrev Heads := Fin 139 → ℕ
def old (i : Fin 135) : Fin 139 := i.castAdd 4
theorem old_injective : Function.Injective old := by
  intro a b h
  have hv := congrArg (fun i : Fin 139 => i.val) h
  exact Fin.ext hv
def numbers (k : Fin 42) := old (UWalkOrdinary.slots k)
noncomputable def numericPhase := RecoveryFocus.machine old UWalkOrdinary.machine
def Fresh (H : Heads) (T : Store) : Prop := ∀ i,97 ≤ i.val → H i=0 ∧ T i=[]
def Preserved {s : ℕ} (H : Heads) (T : Store) (a : Configuration 139 s) : Prop :=
  ∀ i,i.val<97 → i.val≠20 → i.val≠50 → i.val≠58 → i.val≠73 → a.tapes i=T i ∧ a.heads i=H i
def Numeric {s : ℕ} (w t j c : ℕ) (a : Configuration 139 s) : Prop :=
  (∀ k,a.tapes (numbers k)=UWalkNumbers.afterUnit w t j c k) ∧
  (∀ k,a.heads (numbers k)=UWalkNumbers.heads k)
def ArrayFresh {s : ℕ} (a : Configuration 139 s) : Prop :=
  ∀ i,135 ≤ i.val → a.heads i=0 ∧ a.tapes i=[]

theorem numeric_run (w t j c : ℕ) (hw : 1 ≤ w) (H : Heads) (T : Store)
    (hh : H 20=0 ∧ H 50=1 ∧ H 58=1 ∧ H 73=1)
    (ht : T 20=List.replicate w true ∧ T 50=CapMachine.counter c t ∧
      T 58=CompareMachine.word j ∧ T 73=CompareMachine.word w)
    (hfresh : Fresh H T) :
    ∃ r,runFrom numericPhase (UWalkNumbers.budget w t j)
      (RecoveryCalls.restarted numericPhase H T)=some r ∧ Numeric w t j c r.final ∧
      Preserved H T r.final ∧ ArrayFresh r.final ∧ r.steps ≤ UWalkNumbers.budget w t j := by
  have hlocal : UWalkOrdinary.Fresh (H ∘ old) (T ∘ old) := by
    intro i hi
    exact hfresh (old i) hi
  obtain ⟨base,hb,hbt,hbh,hbp,hbs⟩ := UWalkOrdinary.entry_run w t j c hw (H ∘ old) (T ∘ old) hh ht hlocal
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config old old_injective UWalkOrdinary.machine
    H T (UWalkNumbers.budget w t j) _ base hb
  have he := UWitness.focus_config_eq old old_injective (UWalkOrdinary.entry (H ∘ old) (T ∘ old))
    H T (by intro i; rfl) (by intro i; rfl)
  rw [he] at hr
  have hv (i : Fin 135) : r.final.tapes (old i)=base.final.tapes i ∧ r.final.heads (old i)=base.final.heads i := by
    simp [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ old_injective]
  refine ⟨r,hr,⟨?_,?_⟩,?_,?_,hrs.trans_le hbs⟩
  · intro k
    exact (hv (UWalkOrdinary.slots k)).1.trans (hbt k)
  · intro k
    exact (hv (UWalkOrdinary.slots k)).2.trans (hbh k)
  · intro i hi h20 h50 h58 h73
    let a : Fin 135 := ⟨i.val,by omega⟩
    have hae : old a=i := Fin.ext rfl
    have hnone : ∀ k,UWalkOrdinary.slots k≠a := by
      intro k heq
      have hval := congrArg Fin.val heq
      rw [UWalkOrdinary.slot_value] at hval
      dsimp only [a] at hval
      split_ifs at hval <;> omega
    obtain ⟨ht0,hh0⟩ := hbp a hnone
    rw [←hae]
    exact ⟨(hv a).1.trans ht0,(hv a).2.trans hh0⟩
  · intro i hi
    have hn := UWitness.pick_other old i (by
      intro k heq
      have hv := congrArg Fin.val heq
      change k.val=i.val at hv
      omega)
    have hfreshi := hfresh i (by omega)
    simpa [hf,RecoveryFocus.config,hn] using hfreshi

theorem numeric_inputs {s : ℕ} (w t j c : ℕ) (a : Configuration 139 s) (h : Numeric w t j c a) :
    a.tapes 20=List.replicate w true ∧ a.tapes 50=CapMachine.counter c t ∧
    a.heads 20=0 ∧ a.heads 50=1 := by
  refine ⟨?_,?_,h.2 0,h.2 1⟩
  · have ht := h.1 0
    simpa [numbers,old,UWalkOrdinary.slots,UWalkNumbers.afterUnit,UWalkNumbers.afterOne,UWalkNumbers.afterZ3,UWalkNumbers.afterZ2,
      UWalkNumbers.afterZ1,UWalkNumbers.afterC,UWalkNumbers.afterQ,UWalkNumbers.afterK,UWalkNumbers.afterP,
      UWalkNumbers.afterD,UWalkNumbers.afterW,UWalkNumbers.afterJ,UWalkNumbers.afterT,UWalkNumbers.input] using ht
  · have ht := h.1 1
    simpa [numbers,old,UWalkOrdinary.slots,UWalkNumbers.afterUnit,UWalkNumbers.afterOne,UWalkNumbers.afterZ3,UWalkNumbers.afterZ2,
      UWalkNumbers.afterZ1,UWalkNumbers.afterC,UWalkNumbers.afterQ,UWalkNumbers.afterK,UWalkNumbers.afterP,
      UWalkNumbers.afterD,UWalkNumbers.afterW,UWalkNumbers.afterJ,UWalkNumbers.afterT,UWalkNumbers.input] using ht

end NearCubicWires.RepairOrdinary.UWalkArray
