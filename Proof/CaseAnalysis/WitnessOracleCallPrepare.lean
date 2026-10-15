import Proof.CaseAnalysis.WitnessOracleCallLayout

/-! The three actual copies which preserve the complete selected-source bank.
Only parser inputs and the paid copy logs change; all parser scratch is cold. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCall
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem extra_injective (t : ℕ) : Function.Injective (extra t):=by
  intro a b h
  have hv:=congrArg Fin.val h
  simp only [extra,Fin.val_natAdd] at hv
  exact Fin.ext (by omega)

theorem copiedX_extra {t : ℕ} (base : Fin t→List Bool) (bits x : List Bool) (i : Fin 1385) :
    copiedX base bits x (extra t i)=if i=1381 then List.replicate (2*x.length+1) false
      else if i=0 then frame x else if i.val=1 then frame bits else []:=by
  by_cases h1:i=1381
  · subst i; simp [copiedX]
  by_cases h0:i=0
  · subst i
    rw [copiedX,Function.update_of_ne (fun h=>h1 ((extra_injective t) h)),Function.update_self]
    simp
  rw [copiedX,Function.update_of_ne (fun h=>h1 ((extra_injective t) h)),
    Function.update_of_ne (fun h=>h0 ((extra_injective t) h)),input_extra]
  simp only [h1,h0,if_false]

theorem copied_extra {t : ℕ} (base : Fin t→List Bool) (bits x arityBits : List Bool) (i : Fin 1385) :
    copied base bits x arityBits (extra t i)=if i=1382 then List.replicate (2*arityBits.length+1) false
      else if i=2 then frame arityBits else if i=1381 then List.replicate (2*x.length+1) false
      else if i=0 then frame x else if i.val=1 then frame bits else []:=by
  by_cases h2:i=1382
  · subst i; simp [copied]
  by_cases h0:i=2
  · subst i
    rw [copied,Function.update_of_ne (fun h=>h2 ((extra_injective t) h)),Function.update_self]
    simp
  rw [copied,Function.update_of_ne (fun h=>h2 ((extra_injective t) h)),
    Function.update_of_ne (fun h=>h0 ((extra_injective t) h)),copiedX_extra]
  simp only [h2,h0,if_false]

theorem copy_x_ready {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x : List Bool) (hx : base (fields 0)=frame x) :
    ClockJoin.ReadyRun (copy fields 0) (4*x.length+4) (input base bits) (copiedX base bits x):=by
  have h:=OrdinaryOracleCompose.copy_ready (copySlots fields 0) (copy_injective fields 0)
    (input base bits) x [] (by simpa [copySlots,input_old] using hx)
    (by simp [copySlots,input_extra]) (by simp [copySlots,input_extra])
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem copy_q_ready {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool) (hq : base (fields 1)=frame arityBits) :
    ClockJoin.ReadyRun (copy fields 1) (4*arityBits.length+4)
      (copiedX base bits x) (copied base bits x arityBits):=by
  have h:=OrdinaryOracleCompose.copy_ready (copySlots fields 1) (copy_injective fields 1)
    (copiedX base bits x) arityBits [] (by simpa [copySlots,copiedX_old] using hq)
    (by simp [copySlots,copiedX_extra]) (by simp [copySlots,copiedX_extra])
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem raw_input {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool) (hq : base (fields 2)=List.replicate (value arityBits) true)
    (i : Fin 4) : copied base bits x arityBits (rawSlots fields i)=
      ![List.replicate (value arityBits) true,[],[],[]] i:=by
  fin_cases i <;> simp [rawSlots,copied_old,copied_extra,hq]

theorem raw_ready {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool) (hq : base (fields 2)=List.replicate (value arityBits) true) :
    ClockJoin.ReadyRun (raw fields) (2*value arityBits+6)
      (copied base bits x arityBits) (prepared fields base bits x arityBits):=by
  have h:=ClockUnarySum.sum_ready (value arityBits) 0
  simp only [Nat.add_zero,List.replicate_zero] at h
  exact h.focus (rawSlots fields) (raw_injective fields) (copied base bits x arityBits)
    (raw_input fields base bits x arityBits hq)

theorem prepare_run {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool) (hx : base (fields 0)=frame x)
    (hqb : base (fields 1)=frame arityBits)
    (hqr : base (fields 2)=List.replicate (value arityBits) true) :
    ClockJoin.ReadyRun (prepare fields) (prepareBudget x arityBits)
      (input base bits) (prepared fields base bits x arityBits):=by
  have hxrun:=copy_x_ready fields base bits x hx
  have hqrun:=copy_q_ready fields base bits x arityBits hqb
  have hcopies:=ClockJoin.join (copy fields 0) (copy fields 1) _ _ _ _ _ hxrun hqrun
  exact ClockJoin.join (copies fields) (raw fields) _ _ _ _ _ hcopies
    (raw_ready fields base bits x arityBits hqr)

end NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCall
