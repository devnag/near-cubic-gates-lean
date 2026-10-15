import Proof.Amplification.RecoveryRowStructureChildrenCopy

/-! The paired-row caller executes the three-count automaton on its actual
parent count, copied left count and second lookup's retained right count.
Both overflowing arithmetic and malformed balance are rejected. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def childrenCountSlots : Fin 5→Fin 68 := ![47,46,60,50,22]
theorem childrenCountSlots_injective : Function.Injective childrenCountSlots := by decide
noncomputable def childrenCountMachine := RecoveryFocus.machine childrenCountSlots RecoveryRowCounts.reusableMachine
def childrenCounted (x : Children) : Children :=
  {x with base:=setValid x.base (RecoveryRowCounts.relation x.base.count x.base.code x.bank.saved)}

theorem childrenCounted_tapes (x : Children) :
    (childrenCounted x).tapes=Function.update x.tapes 50
      [RecoveryRowCounts.relation x.base.count x.base.code x.bank.saved] := by
  change Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
    (cfg (setValid x.base (RecoveryRowCounts.relation x.base.count x.base.code x.bank.saved))
      x.copyCapacity (0 : Fin 1)).tapes
    (RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity)=_
  rw [cfg_valid,bank_update_left]
  rfl

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem children_count_output (ambient : Fin 68→List Bool) (parent left right : List Bool) (capacity : Nat)
    (hp : ambient 47=frame parent) (hl : ambient 46=frame left) (hr : ambient 60=frame right)
    (hc : ambient 22=List.replicate capacity false) :
    install childrenCountSlots ambient ![frame parent,frame left,frame right,
      [RecoveryRowCounts.relation parent left right],List.replicate capacity false]=
      Function.update ambient 50 [RecoveryRowCounts.relation parent left right] := by
  apply install_eq childrenCountSlots childrenCountSlots_injective
  · intro j
    fin_cases j
    · exact hp.symm
    · exact hl.symm
    · exact hr.symm
    · simp [childrenCountSlots]
    · exact hc.symm
  · intro i hi
    have h50 : i≠50 := by intro he; exact hi 3 he.symm
    simp only [Function.update_of_ne h50]

theorem children_count_run (x : Children) (word bits : List Bool) (hx : x.Valid word bits)
    (hp : x.base.count.length=x.base.state.bits.length) (hl : x.base.code.length=x.base.state.bits.length) :
    ∃ r,runFrom childrenCountMachine (4*x.base.count.length+4) (x.cfg childrenCountMachine.start)=some r ∧
      r.final=(childrenCounted x).cfg r.final.control ∧ r.steps=4*x.base.count.length+4 ∧
      (childrenCounted x).Valid word bits := by
  have hs : x.bank.saved.length=x.base.state.bits.length := hx.2.2.2.1.trans hx.2.1.2.1
  have hreset : 2*x.base.count.length+1≤x.base.state.capacity := by
    have hb := hx.1.2.1.reset
    change 8192*(x.base.state.bits.length+1)^2+1≤x.base.state.capacity at hb
    rw [hp]
    nlinarith
  have h := RecoveryRowCounts.counts_ready x.base.count x.base.code x.bank.saved x.base.valid x.base.state.capacity
    (hp.trans hl.symm) (hl.trans hs.symm)
  rw [Nat.max_eq_left hreset] at h
  obtain ⟨r,hr,hheads,htapes,hsteps⟩ := h.focus_at childrenCountSlots childrenCountSlots_injective x.heads x.tapes
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,?_,hsteps,hx⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans ((children_count_output x.tapes x.base.count x.base.code x.bank.saved x.base.state.capacity
      (by rfl) (by rfl) (by rfl) (by rfl)).trans (childrenCounted_tapes x).symm)

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
