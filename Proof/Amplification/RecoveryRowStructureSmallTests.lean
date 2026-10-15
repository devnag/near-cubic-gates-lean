import Proof.Amplification.RecoveryRowStructureCountKind

/-! Actual zero-code and singleton-payload checks in the shared streamed
row workspace. The physical result bit survives the following count pass. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def codePredSlots : Fin 3→Fin 52 := ![46,50,22]
theorem codePredSlots_injective : Function.Injective codePredSlots := by decide
noncomputable def codePredMachine := RecoveryFocus.machine codePredSlots RecoveryListPredecessor.machine
def codePredicted (d : Data) : Data :=
  setValid (setCode d (RecoveryListPredecessor.result d.code true)) (decide (value d.code≠0))

def payloadSlots : Fin 5→Fin 52 := ![24,0,50,44,22]
theorem payloadSlots_injective : Function.Injective payloadSlots := by decide
noncomputable def payloadMachine := RecoveryFocus.machine payloadSlots RecoveryRowComparison.machine
def payloadCompared (d : Data) (child : List Bool) : Data :=
  setValid (setFlag d 1 (decide (value d.state.bits≤value child))) (decide (value child=value d.state.bits))

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem codePredicted_tapes (d : Data) (capacity : Nat) :
    (cfg (codePredicted d) capacity (0 : Fin 1)).tapes=
      Function.update (Function.update (cfg d capacity (0 : Fin 1)).tapes 46
        (frame (RecoveryListPredecessor.result d.code true))) 50 [decide (value d.code≠0)] := by
  unfold codePredicted
  rw [cfg_valid,cfg_code]

theorem code_pred_output (ambient : Fin 52→List Bool) (code : List Bool) (capacity : Nat)
    (hreset : ambient 22=List.replicate capacity false) :
    install codePredSlots ambient ![frame (RecoveryListPredecessor.result code true),
      [decide (value code≠0)],List.replicate capacity false]=
      Function.update (Function.update ambient 46 (frame (RecoveryListPredecessor.result code true)))
        50 [decide (value code≠0)] := by
  apply install_eq codePredSlots codePredSlots_injective
  · intro j
    fin_cases j
    · simp [codePredSlots]
    · simp [codePredSlots]
    · exact hreset.symm
  · intro i hi
    have h46 : i≠46 := by intro he; exact hi 0 he.symm
    have h50 : i≠50 := by intro he; exact hi 1 he.symm
    simp only [Function.update_of_ne h46,Function.update_of_ne h50]

theorem code_pred_run (d : Data) (capacity : Nat) (word : List Bool) (hd : d.Valid word) :
    ∃ r,runFrom codePredMachine (4*d.code.length+4) (cfg d capacity codePredMachine.start)=some r ∧
      r.final=cfg (codePredicted d) capacity r.final.control ∧ r.steps=4*d.code.length+4 ∧
      (codePredicted d).Valid word := by
  have hreset : 2*d.code.length+1≤d.state.capacity := by
    have hwidth := hd.2.2.2.1
    have hcap := hd.2.1.reset
    change 8192*(d.state.bits.length+1)^2+1≤d.state.capacity at hcap
    nlinarith
  have h := RecoveryListPredecessor.predecessor_ready d.code d.valid d.state.capacity
  rw [Nat.max_eq_left hreset] at h
  obtain ⟨r,hr,hheads,htapes,hsteps⟩ := h.focus_at codePredSlots codePredSlots_injective
    (cfg d capacity codePredMachine.start).heads (cfg d capacity codePredMachine.start).tapes
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,?_,hsteps,?_⟩
  · apply configuration_ext
    · rfl
    · exact hheads
    · exact htapes.trans ((code_pred_output (cfg d capacity (0 : Fin 1)).tapes d.code d.state.capacity
        (by rfl)).trans (codePredicted_tapes d capacity).symm)
  · exact setCode_valid d (RecoveryListPredecessor.result d.code true) word hd
      (by simpa only [RecoveryListPredecessor.result_length] using hd.2.2.2.1)

theorem payloadCompared_tapes (d : Data) (capacity : Nat) (child : List Bool) :
    (cfg (payloadCompared d child) capacity (0 : Fin 1)).tapes=
      Function.update (Function.update (cfg d capacity (0 : Fin 1)).tapes 44
        [decide (value d.state.bits≤value child)]) 50 [decide (value child=value d.state.bits)] := by
  unfold payloadCompared
  rw [cfg_valid,cfg_flag]
  rfl

theorem payload_output (ambient : Fin 52→List Bool) (child payload : List Bool) (capacity : Nat)
    (hc : ambient 24=frame child) (hp : ambient 0=frame payload)
    (hreset : ambient 22=List.replicate capacity false) :
    install payloadSlots ambient (RecoveryRowComparison.tapes child payload
      ![decide (value child=value payload),decide (value payload≤value child)] capacity)=
      Function.update (Function.update ambient 44 [decide (value payload≤value child)])
        50 [decide (value child=value payload)] := by
  apply install_eq payloadSlots payloadSlots_injective
  · intro j
    fin_cases j
    · exact hc.symm
    · exact hp.symm
    · simp [payloadSlots,RecoveryRowComparison.tapes]
    · simp [payloadSlots,RecoveryRowComparison.tapes]
    · exact hreset.symm
  · intro i hi
    have h50 : i≠50 := by intro he; exact hi 2 he.symm
    have h44 : i≠44 := by intro he; exact hi 3 he.symm
    simp only [Function.update_of_ne h50,Function.update_of_ne h44]

theorem payload_run (d : Data) (capacity : Nat) (child word : List Bool) (hd : d.Valid word)
    (hw : child.length=d.state.bits.length) (hc : d.state.fields 0=frame child) :
    ∃ r,runFrom payloadMachine (8*child.length+20) (cfg d capacity payloadMachine.start)=some r ∧
      r.final=cfg (payloadCompared d child) capacity r.final.control ∧ r.steps=8*child.length+20 ∧
      (payloadCompared d child).Valid word := by
  have hreset : 2*child.length+3≤d.state.capacity := by
    have hcap := hd.2.1.reset
    change 8192*(d.state.bits.length+1)^2+1≤d.state.capacity at hcap
    rw [hw]
    nlinarith
  have h := RecoveryRowComparison.equal_ready child d.state.bits ![d.valid,d.flags 1] d.state.capacity hw
  rw [Nat.max_eq_left hreset] at h
  obtain ⟨r,hr,hheads,htapes,hsteps⟩ := h.focus_at payloadSlots payloadSlots_injective
    (cfg d capacity payloadMachine.start).heads (cfg d capacity payloadMachine.start).tapes
    (by intro j; fin_cases j <;> first | exact hc | rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,?_,hsteps,hd⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans ((payload_output (cfg d capacity (0 : Fin 1)).tapes child d.state.bits d.state.capacity
      hc (by rfl) (by rfl)).trans (payloadCompared_tapes d capacity child).symm)

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
