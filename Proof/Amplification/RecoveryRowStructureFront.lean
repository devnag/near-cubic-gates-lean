import Proof.Amplification.RecoveryRowStructureValidity

/-! Whole physical tag front for a streamed structural row. The parsed code
is copied and unpaired, its tag is compared with the retained claimed kind,
and the padded tag selects exactly kinds zero, one and two. Every other
branch writes false to the common row result cell. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def stateCount {t s : Nat} (_ : Machine t s) : Nat := s
noncomputable def frontSizes : Fin 4→Nat :=
  ![stateCount prepareMachine,stateCount tagKindMachine,2,2]
noncomputable def frontPrograms : (j : Fin 4)→Machine 52 (frontSizes j)
  | ⟨0,_⟩=>prepareMachine
  | ⟨1,_⟩=>tagKindMachine
  | ⟨2,_⟩=>validMachine true
  | ⟨3,_⟩=>validMachine false
  | ⟨n+4,h⟩=>False.elim (by omega)
def frontNext (j : Fin 4) (_ : Fin (frontSizes j)) (scanned : Fin 52→Bool) : Option (Fin 4) :=
  if j.val=0 then if scanned 43 then some 1 else some 3 else
    if j.val=1 then if scanned 43 || scanned 44 || scanned 45 then some 2 else some 3 else none
noncomputable def frontMachine := RecoveryCalls.machine frontSizes frontPrograms 0 frontNext
noncomputable def frontCfg (d : Data) (capacity : Nat) (j : Fin 4) :=
  cfg d capacity (RecoveryCalls.code frontSizes j (frontPrograms j).start)
noncomputable def frontStop (d : Data) (capacity : Nat) :=
  RecoveryCalls.stopped frontSizes (cfg d capacity (0 : Fin 1)).heads (cfg d capacity (0 : Fin 1)).tapes

def tagAllowed (tag : List Bool) : Bool :=
  decide (value tag=0) || decide (value tag=1) || decide (value tag=2)
def frontAnswer (d : Data) : Bool := (prepared d).flags 0 && tagAllowed (RecoveryFixedUnpair.leftWord d.code)
def frontOutput (d : Data) : Data :=
  if (prepared d).flags 0 then
    setValid (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)) (tagAllowed (RecoveryFixedUnpair.leftWord d.code))
  else setValid (prepared d) false
def frontTime (d : Data) : Nat := prepareTime d+RecoveryRowKind.time (RecoveryFixedUnpair.leftWord d.code)+5

private theorem front_call (j l : Fin 4) (d out : Data) (capacity fuel : Nat)
    (r : ExecutionReceipt 52 (frontSizes j))
    (hr : runFrom (frontPrograms j) fuel (cfg d capacity (frontPrograms j).start)=some r)
    (hf : r.final=cfg out capacity r.final.control)
    (hn : frontNext j r.final.control r.final.scanned=some l) :
    ∃ n≤fuel+1,Timed frontMachine n (frontCfg d capacity j) (frontCfg out capacity l) := by
  obtain ⟨n,hb,h⟩ := call_receipt frontSizes frontPrograms 0 frontNext j l fuel _ r hr hn
  rw [hf] at h
  exact ⟨n,hb,h⟩

private theorem front_stop (j : Fin 4) (d out : Data) (capacity fuel : Nat)
    (r : ExecutionReceipt 52 (frontSizes j))
    (hr : runFrom (frontPrograms j) fuel (cfg d capacity (frontPrograms j).start)=some r)
    (hf : r.final=cfg out capacity r.final.control)
    (hn : frontNext j r.final.control r.final.scanned=none) :
    ∃ n≤fuel+1,Timed frontMachine n (frontCfg d capacity j) (frontStop out capacity) := by
  obtain ⟨n,hb,h⟩ := stop_receipt frontSizes frontPrograms 0 frontNext j fuel _ r hr hn
  rw [hf] at h
  exact ⟨n,hb,h⟩

private theorem finish_true (d : Data) (capacity : Nat) :
    ∃ n≤2,Timed frontMachine n (frontCfg d capacity 2) (frontStop (setValid d true) capacity) := by
  obtain ⟨r,hr,hf,_⟩ := valid_run d capacity true
  exact front_stop 2 d (setValid d true) capacity 1 r hr (by rw [hf]; rfl) (by rfl)

private theorem finish_false (d : Data) (capacity : Nat) :
    ∃ n≤2,Timed frontMachine n (frontCfg d capacity 3) (frontStop (setValid d false) capacity) := by
  obtain ⟨r,hr,hf,_⟩ := valid_run d capacity false
  exact front_stop 3 d (setValid d false) capacity 1 r hr (by rw [hf]; rfl) (by rfl)

theorem front_trace (d : Data) (capacity : Nat) (word : List Bool) (hd : d.Valid word)
    (hw : d.code.length=d.state.bits.length) (hk : d.kind.length=d.state.bits.length)
    (hc : 2*d.code.length+1≤capacity) (hr : 4*d.code.length+3≤d.state.capacity) :
    ∃ n≤frontTime d,Timed frontMachine n (cfg d capacity frontMachine.start) (frontStop (frontOutput d) capacity) := by
  change ∃ n≤frontTime d,Timed frontMachine n (frontCfg d capacity 0) (frontStop (frontOutput d) capacity)
  obtain ⟨first,hr0,hf0,_,hv0,_⟩ := prepare_run d capacity word hd hw hk hc hr
  cases heq : (prepared d).flags 0
  · obtain ⟨n0,hb0,h0⟩ := front_call 0 3 d (prepared d) capacity (prepareTime d) first hr0 hf0 (by
      rw [hf0]
      change (if (prepared d).flags 0 then some (1 : Fin 4) else some 3)=some 3
      rw [heq]; rfl)
    obtain ⟨n1,hb1,h1⟩ := finish_false (prepared d) capacity
    refine ⟨n0+n1,by unfold frontTime; omega,?_⟩
    simpa only [frontOutput,heq,Bool.false_eq_true,if_false] using h0.trans h1
  · obtain ⟨n0,hb0,h0⟩ := front_call 0 1 d (prepared d) capacity (prepareTime d) first hr0 hf0 (by
      rw [hf0]
      change (if (prepared d).flags 0 then some (1 : Fin 4) else some 3)=some 1
      rw [heq]; rfl)
    have hlen : (RecoveryFixedUnpair.leftWord d.code).length=(prepared d).state.bits.length :=
      (RecoveryFixedUnpair.word_lengths d.code).1.trans hw
    have htag : (cfg (prepared d) capacity (0 : Fin 1)).tapes 17=
        ZeroPadding.pad (RecoveryReusableUnpair.capacity (prepared d).state.bits)
          (frame (RecoveryFixedUnpair.leftWord d.code)) := by
      rw [prepared_tag d capacity hw]
      have he : RecoveryReusableUnpair.capacity d.code=RecoveryReusableUnpair.capacity (prepared d).state.bits := by
        change 8192*(d.code.length+1)^2=8192*(d.state.bits.length+1)^2
        rw [hw]
      rw [he]
    obtain ⟨second,hr1,hf1,_,_,_⟩ := tag_kind_run (prepared d) capacity (RecoveryFixedUnpair.leftWord d.code) word hv0 hlen htag
    cases ha : tagAllowed (RecoveryFixedUnpair.leftWord d.code)
    · obtain ⟨n1,hb1,h1⟩ := front_call 1 3 (prepared d) (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code))
        capacity (RecoveryRowKind.time (RecoveryFixedUnpair.leftWord d.code)) second hr1 hf1 (by
          rw [hf1]
          change (if ((classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)).flags 0 ||
            (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)).flags 1 ||
            (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)).flags 2) then some (2 : Fin 4) else some 3)=some 3
          simp only [classified_flags]
          change (if tagAllowed (RecoveryFixedUnpair.leftWord d.code) then some (2 : Fin 4) else some 3)=some 3
          rw [ha]; rfl)
      obtain ⟨n2,hb2,h2⟩ := finish_false (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)) capacity
      refine ⟨n0+n1+n2,by unfold frontTime; omega,?_⟩
      simpa only [frontOutput,heq,if_true,ha] using (h0.trans h1).trans h2
    · obtain ⟨n1,hb1,h1⟩ := front_call 1 2 (prepared d) (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code))
        capacity (RecoveryRowKind.time (RecoveryFixedUnpair.leftWord d.code)) second hr1 hf1 (by
          rw [hf1]
          change (if ((classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)).flags 0 ||
            (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)).flags 1 ||
            (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)).flags 2) then some (2 : Fin 4) else some 3)=some 2
          simp only [classified_flags]
          change (if tagAllowed (RecoveryFixedUnpair.leftWord d.code) then some (2 : Fin 4) else some 3)=some 2
          rw [ha]; rfl)
      obtain ⟨n2,hb2,h2⟩ := finish_true (classified (prepared d) (RecoveryFixedUnpair.leftWord d.code)) capacity
      refine ⟨n0+n1+n2,by unfold frontTime; omega,?_⟩
      simpa only [frontOutput,heq,if_true,ha] using (h0.trans h1).trans h2

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
