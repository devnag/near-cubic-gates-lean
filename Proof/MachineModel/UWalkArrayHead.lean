import Proof.MachineModel.UWalkArrayNumeric

/-! Consume the numeric supplier's actual restored width/tape-count fields
to build and rewind the exact serialized array of initial zero heads. -/
namespace NearCubicWires.RepairOrdinary.UWalkArray
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def arraySlots : Fin 6 → Fin 139 := ![135,20,136,137,50,138]
theorem array_injective : Function.Injective arraySlots := by decide
noncomputable def arrayPhase := RecoveryFocus.machine arraySlots UHeadArray.readyMachine
def arrayBudget (w t : ℕ) := 2*UHeadArray.budget w t+2

theorem array_run {s : ℕ} (w t j c : ℕ) (a : Configuration 139 s)
    (hnumeric : Numeric w t j c a) (hfresh : ArrayFresh a) :
    ∃ r,runFrom arrayPhase (arrayBudget w t)
      (RecoveryCalls.restarted arrayPhase a.heads a.tapes)=some r ∧
      r.final.heads=a.heads ∧ (∀ i,i.val<135 → r.final.tapes i=a.tapes i) ∧
      r.final.tapes 136=UHeadArray.fields w t ∧ r.final.heads 136=0 ∧ r.steps ≤ arrayBudget w t := by
  obtain ⟨hw,ht,hhw,hht⟩ := numeric_inputs w t j c a hnumeric
  obtain ⟨base,hb,hbs,hbh,hbw,hbout,hbt,_⟩ := UHeadArray.ready_run w t c
  have hiH : ∀ i,a.heads (arraySlots i)=(UHeadArray.readyEntry w t c).heads i := by
    intro i
    fin_cases i
    · exact (hfresh 135 (by decide)).1
    · exact hhw
    · exact (hfresh 136 (by decide)).1
    · exact (hfresh 137 (by decide)).1
    · exact hht
    · exact (hfresh 138 (by decide)).1
  have hiT : ∀ i,a.tapes (arraySlots i)=(UHeadArray.readyEntry w t c).tapes i := by
    intro i
    fin_cases i
    · exact (hfresh 135 (by decide)).2
    · exact hw
    · exact (hfresh 136 (by decide)).2
    · exact (hfresh 137 (by decide)).2
    · exact ht
    · exact (hfresh 138 (by decide)).2
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config arraySlots array_injective UHeadArray.readyMachine
    a.heads a.tapes (arrayBudget w t) _ base hb
  have he := UWitness.focus_config_eq arraySlots array_injective (UHeadArray.readyEntry w t c)
    a.heads a.tapes hiH hiT
  rw [he] at hr
  have hv (i : Fin 6) : r.final.tapes (arraySlots i)=base.final.tapes i ∧
      r.final.heads (arraySlots i)=base.final.heads i := by
    simp [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ array_injective]
  have hbheads : base.final.heads=(UHeadArray.readyEntry w t c).heads := by
    rw [hbh]
    funext i; fin_cases i <;> rfl
  have hheads : r.final.heads=a.heads := by
    funext i
    cases hp : RecoveryFocus.pick arraySlots i with
    | none => simp [hf,RecoveryFocus.config,hp]
    | some k =>
      have hk := RecoveryFocus.slot_of_pick arraySlots hp
      rw [←hk]
      exact (hv k).2.trans ((congrFun hbheads k).trans (hiH k).symm)
  refine ⟨r,hr,hheads,?_,(hv 2).1.trans hbout,?_,hrs.trans_le hbs⟩
  · intro i hi
    by_cases hi20 : i.val=20
    · have he20 : i=20 := Fin.ext hi20
      subst i
      exact (hv 1).1.trans (hbw.trans hw.symm)
    by_cases hi50 : i.val=50
    · have he50 : i=50 := Fin.ext hi50
      subst i
      exact (hv 4).1.trans (hbt.trans ht.symm)
    have hn := UWitness.pick_other arraySlots i (by
      intro k hk
      have hh := congrArg Fin.val hk
      fin_cases k <;> simp [arraySlots] at hh <;> omega)
    simp [hf,RecoveryFocus.config,hn]
  · rw [hheads]
    exact (hfresh 136 (by decide)).1

theorem array_preserves_numeric {s z : ℕ} (w t j c : ℕ)
    (a : Configuration 139 s) (b : Configuration 139 z) (h : Numeric w t j c a)
    (hh : b.heads=a.heads) (ht : ∀ i,i.val<135 → b.tapes i=a.tapes i) : Numeric w t j c b := by
  refine ⟨?_,?_⟩
  · intro k
    exact (ht (numbers k) (UWalkOrdinary.slots k).isLt).trans (h.1 k)
  · intro k
    rw [hh]
    exact h.2 k

theorem array_preserves_old {s z : ℕ} (H : Heads) (T : Store)
    (a : Configuration 139 s) (b : Configuration 139 z) (h : Preserved H T a)
    (hh : b.heads=a.heads) (ht : ∀ i,i.val<135 → b.tapes i=a.tapes i) : Preserved H T b := by
  intro i hi h20 h50 h58 h73
  obtain ⟨hti,hhi⟩ := h i hi h20 h50 h58 h73
  exact ⟨(ht i (by omega)).trans hti,by rw [hh]; exact hhi⟩

end NearCubicWires.RepairOrdinary.UWalkArray
