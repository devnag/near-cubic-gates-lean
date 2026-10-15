import Proof.MachineModel.OrdinaryMatrixPacketStateAdvance

/-! One whole bit iteration: execute the positive and negative native
Williams packets, then physically advance the retained offset. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketSignPair
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open MatrixPacketState (State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first (a : WilliamsAlgorithm) (E : ℕ) :=
  Composition.machine (MatrixPacketReuse.machine a E false) (MatrixPacketReuse.machine a E true)
noncomputable def machine (a : WilliamsAlgorithm) (E : ℕ) :=
  Composition.machine (first a E) (MatrixPacketStateAdvance.machine a E)
def wordPair (r : Request) (bit : ℕ) := packet r false bit++packet r true bit
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) (bit cap : ℕ) :=
  (MatrixPacketReuse.budget a r false bit cap+1+MatrixPacketReuse.budget a r true bit cap)+1+MatrixPacketOffset.budget bit
noncomputable def input (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) := RecoveryCalls.restarted (machine a E) st.heads st.tapes

theorem pair_run (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) (ht : bit<r.p)
    (hcap : ∀ negative,MatrixVariablePacketWorkspace.footprint a r bit negative≤cap) :
    ∃ next : State a E cap r (bit+1) (out++wordPair r bit),∃ actual,
      runFrom (machine a E) (budget a r bit cap) (input a E cap r bit out st)=some actual ∧
      actual.final.heads=next.heads ∧ actual.final.tapes=next.tapes ∧
      actual.steps≤budget a r bit cap := by
  obtain ⟨positive,pos,hp,ph,pt,ps⟩ := MatrixPacketState.state_run a E cap r bit out false st ht (hcap false)
  obtain ⟨negative,neg,hn,nh,nt,ns⟩ := MatrixPacketState.state_run a E cap r bit
    (out++packet r false bit) true positive ht (hcap true)
  have hpn : Composition.restart pos.final (MatrixPacketReuse.machine a E true).start=
      MatrixPacketState.data a E cap r bit (out++packet r false bit) true positive := by
    apply configuration_ext
    · rfl
    · exact ph
    · exact pt
  rw [←hpn] at hn
  have hj := Composition.run_join (MatrixPacketReuse.machine a E false) (MatrixPacketReuse.machine a E true)
    _ _ _ pos neg hp hn
  let paired := Composition.joinedReceipt pos neg
  obtain ⟨advanced,adv,ha,ah,atapes,as⟩ := MatrixPacketStateAdvance.state_run a E cap r bit
    ((out++packet r false bit)++packet r true bit) negative
  have hpa : Composition.restart paired.final (MatrixPacketStateAdvance.machine a E).start=
      MatrixPacketStateAdvance.input a E cap r bit ((out++packet r false bit)++packet r true bit) negative := by
    apply configuration_ext
    · rfl
    · exact nh
    · exact nt
  rw [←hpa] at ha
  have whole := Composition.run_join (first a E) (MatrixPacketStateAdvance.machine a E)
    _ _ _ paired adv hj ha
  let actual := Composition.joinedReceipt paired adv
  have hc : ∃ next : State a E cap r (bit+1) (out++wordPair r bit),
      actual.final.heads=next.heads ∧ actual.final.tapes=next.tapes := by
    change ∃ next : State a E cap r (bit+1) (out++wordPair r bit),
      adv.final.heads=next.heads ∧ adv.final.tapes=next.tapes
    unfold wordPair
    rw [←List.append_assoc]
    exact ⟨advanced,ah,atapes⟩
  obtain ⟨next,hheads,htapes⟩ := hc
  refine ⟨next,actual,whole,hheads,htapes,?_⟩
  change (pos.steps+1+neg.steps)+1+adv.steps≤budget a r bit cap
  unfold budget
  omega

theorem budget_bound (a : WilliamsAlgorithm) (r : Request) (bit cap : ℕ)
    (ht : bit<r.p) (hcap : ∀ negative,MatrixVariablePacketWorkspace.footprint a r bit negative≤cap) :
    budget a r bit cap≤6*cap+16*(word r).length+8*r.p+47 := by
  have h0:=hcap false
  have h1:=hcap true
  unfold MatrixVariablePacketWorkspace.footprint at h0 h1
  unfold budget MatrixPacketReuse.budget MatrixPacketRestore.budget MatrixPacketOffset.budget
  omega

end NearCubicWires.RepairOrdinary.MatrixPacketSignPair
