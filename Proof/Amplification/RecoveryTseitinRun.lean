import Proof.Amplification.RecoveryTseitinPrepare

/-! Execute the whole six-cell clause producer from retained, framed
original variable indices and physically allocated scratch. The finite signs
and source-port map are fixed control choices, never numeric advice. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def kernel (signs : Fin 3→Bool) (sources : Fin 3→Fin 3) :=
  Composition.machine (Prepare.machine signs sources) machine
def clauseSlot : Fin 239 := bank 5 26

theorem clause_run (cap log : Nat) (signs : Fin 3→Bool) (sources : Fin 3→Fin 3) (indices : Fin 3→Nat)
    (ambient : Fin 239→List Bool) (padding : Fin 3→List Bool)
    (hcap : capacity (Prepare.literals signs indices) ≤ cap) (hb : Bounded cap ambient)
    (hd : ambient 3=List.replicate cap true) (hl : ambient 4=List.replicate log false)
    (hz : log ≤ cap+1)
    (hp : ∀ k,ambient (Prepare.sourceSlot sources k)=frame (indices k).bits++padding k) :
    ∃ out : Fin 239→List Bool,
      ClockJoin.ReadyRun (kernel signs sources) (16*cap) ambient out ∧
      out clauseSlot=ZeroPadding.pad cap (frame (Encodable.encode (clause (Prepare.literals signs indices))).bits) ∧
      (∀ i : Fin 239,i.val<3 → out i=ambient i) ∧
      out 3=List.replicate cap true ∧ out 4=List.replicate (cap+1) false ∧ Bounded cap out := by
  have hprepare := Prepare.prepare_run cap log signs sources indices ambient padding hcap hb hd hl hz hp
  obtain ⟨out,hcore,hclause,hlow,hbound⟩ := core_run cap (Prepare.literals signs indices)
    (Prepare.cleared cap ambient) hcap
  have whole := ClockJoin.join _ _ _ _ _ _ _ hprepare hcore
  have htime : (2*cap+4*Prepare.bytes indices+46)+1+6*cap ≤ 16*cap := by
    have h0 := (argument_widths (Prepare.literals signs indices) 0).2
    have h1 := (argument_widths (Prepare.literals signs indices) 1).2
    have h2 := (argument_widths (Prepare.literals signs indices) 2).2
    change (indices 0).bits.length ≤ width (Prepare.literals signs indices) at h0
    change (indices 1).bits.length ≤ width (Prepare.literals signs indices) at h1
    change (indices 2).bits.length ≤ width (Prepare.literals signs indices) at h2
    have hw : width (Prepare.literals signs indices)+1 ≤ (width (Prepare.literals signs indices)+1)^2 := by nlinarith
    unfold capacity at hcap
    unfold Prepare.bytes
    omega
  refine ⟨out,ClockJoin.enlarge _ _ _ _ _ whole htime,hclause,?_,?_,?_,hbound⟩
  · intro i hi
    rw [hlow i (by omega)]
    simp [Prepare.cleared,hi]
  · exact hlow 3 (by decide)
  · exact hlow 4 (by decide)

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
