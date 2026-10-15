import Proof.Amplification.RecoveryRowStructureDispatch

/-! Complete ordinary structural-row execution for every parsed fixed-width
row, including all malformed tag and missing-child branches. The retained
source prefix and its physical row-count driver remain explicit inputs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem structure_trace (x : Children) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hw : x.base.code.length=x.base.state.bits.length)
    (hk : x.base.kind.length=x.base.state.bits.length) (hc : x.base.count.length=x.base.state.bits.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    ∃ n≤ structureTime x,Timed structureMachine n (x.cfg structureMachine.start) (structureStop (structureOutput x bits)) ∧
      (structureOutput x bits).Valid word bits := by
  change ∃ n≤ structureTime x,Timed structureMachine n (structureCfg x 0) (structureStop (structureOutput x bits)) ∧ _
  have hcopy : 2*x.base.code.length+1≤x.copyCapacity := by rw [hw]; exact hx.2.2.2.2.1
  have hreset : 4*x.base.code.length+3≤x.base.state.capacity := by
    have hb := hx.1.2.1.reset
    change 8192*(x.base.state.bits.length+1)^2+1≤x.base.state.capacity at hb
    rw [hw]
    nlinarith
  obtain ⟨base,hr0,hf0,_,_,_⟩ := front_run x.base x.copyCapacity word hx.1 hw hk hcopy hreset
  obtain ⟨first,hfirst,hfirstFinal,_⟩ := base_run frontMachine x (frontOutput x.base) (frontTime x.base) base hr0 hf0
  have hv : (structureFront x).Valid word bits := structureFront_valid x word bits hx hw
  cases ha : (frontOutput x.base).valid
  · obtain ⟨n,hn,h⟩ := structure_stop 0 x (structureFront x) (frontTime x.base) first hfirst hfirstFinal (by
      rw [hfirstFinal]
      change (if (frontOutput x.base).valid then
        if (frontOutput x.base).flags 0 then some (1 : Fin 4) else if (frontOutput x.base).flags 1 then some 2 else some 3 else none)=none
      rw [ha]; rfl)
    refine ⟨n,by unfold structureTime; omega,?_,?_⟩
    · simpa only [structureOutput,ha,Bool.false_eq_true,if_false] using h
    · simpa only [structureOutput,ha,Bool.false_eq_true,if_false] using hv
  · cases hz : (frontOutput x.base).flags 0
    · cases ho : (frontOutput x.base).flags 1
      · obtain ⟨n0,hb0,h0⟩ := structure_call 0 3 x (structureFront x) (frontTime x.base) first hfirst hfirstFinal (by
          rw [hfirstFinal]
          change (if (frontOutput x.base).valid then
            if (frontOutput x.base).flags 0 then some (1 : Fin 4) else if (frontOutput x.base).flags 1 then some 2 else some 3 else none)=some 3
          rw [ha,hz,ho]; rfl)
        have hpair : (pairWord x.base).length=(structureFront x).base.state.bits.length :=
          (RecoveryChildSelection.word_length false x.base.code).trans (hw.trans (congrArg List.length (front_retained x.base).2.2.2.1).symm)
        have hcount : (structureFront x).base.count.length=(structureFront x).base.state.bits.length := by
          change (frontOutput x.base).count.length=(frontOutput x.base).state.bits.length
          rw [(front_retained x.base).2.2.1,(front_retained x.base).2.2.2.1]
          exact hc
        obtain ⟨last,hr,hf,_,hvlast⟩ := children_run (structureFront x) (pairWord x.base) word bits rows rest hv hpair (front_field x.base) hp hcount
        obtain ⟨n1,hb1,h1⟩ := structure_stop 3 (structureFront x)
          (childrenOutput (structureFront x) (pairWord x.base) bits) (childrenTime (structureFront x) (pairWord x.base)) last hr hf (by rfl)
        refine ⟨n0+n1,?_,?_,?_⟩
        · have hb := (Nat.le_max_right (oneTime (frontOutput x.base) (pairWord x.base))
            (childrenTime (structureFront x) (pairWord x.base))).trans (Nat.le_max_right (zeroTime (frontOutput x.base)) _)
          unfold structureTime
          omega
        · simpa only [structureOutput,ha,if_true,hz,ho,Bool.false_eq_true,if_false] using h0.trans h1
        · simpa only [structureOutput,ha,if_true,hz,ho,Bool.false_eq_true,if_false] using hvlast
      · obtain ⟨n0,hb0,h0⟩ := structure_call 0 2 x (structureFront x) (frontTime x.base) first hfirst hfirstFinal (by
          rw [hfirstFinal]
          change (if (frontOutput x.base).valid then
            if (frontOutput x.base).flags 0 then some (1 : Fin 4) else if (frontOutput x.base).flags 1 then some 2 else some 3 else none)=some 2
          rw [ha,hz,ho]; rfl)
        have hpair : (pairWord x.base).length=(frontOutput x.base).state.bits.length :=
          (RecoveryChildSelection.word_length false x.base.code).trans (hw.trans (congrArg List.length (front_retained x.base).2.2.2.1).symm)
        obtain ⟨small,hr,hf,_,hvsmall⟩ := one_run (frontOutput x.base) x.copyCapacity (pairWord x.base) word hv.1 hpair (front_field x.base)
        obtain ⟨last,hlast,hlastFinal,_⟩ := base_run oneMachine (structureFront x) (oneOutput (frontOutput x.base) (pairWord x.base))
          (oneTime (frontOutput x.base) (pairWord x.base)) small hr hf
        obtain ⟨n1,hb1,h1⟩ := structure_stop 2 (structureFront x) (structureOne x)
          (oneTime (frontOutput x.base) (pairWord x.base)) last hlast hlastFinal (by rfl)
        have hvlast : (structureOne x).Valid word bits := withBase_valid (structureFront x) _ word bits hv hvsmall rfl
        refine ⟨n0+n1,?_,?_,?_⟩
        · have hb := (Nat.le_max_left (oneTime (frontOutput x.base) (pairWord x.base))
            (childrenTime (structureFront x) (pairWord x.base))).trans (Nat.le_max_right (zeroTime (frontOutput x.base)) _)
          unfold structureTime
          omega
        · simpa only [structureOutput,ha,if_true,hz,ho,Bool.false_eq_true,if_false] using h0.trans h1
        · simpa only [structureOutput,ha,if_true,hz,ho,Bool.false_eq_true,if_false] using hvlast
    · obtain ⟨n0,hb0,h0⟩ := structure_call 0 1 x (structureFront x) (frontTime x.base) first hfirst hfirstFinal (by
        rw [hfirstFinal]
        change (if (frontOutput x.base).valid then
          if (frontOutput x.base).flags 0 then some (1 : Fin 4) else if (frontOutput x.base).flags 1 then some 2 else some 3 else none)=some 1
        rw [ha,hz]; rfl)
      obtain ⟨small,hr,hf,_,hvsmall⟩ := zero_run (frontOutput x.base) x.copyCapacity word hv.1
      obtain ⟨last,hlast,hlastFinal,_⟩ := base_run zeroMachine (structureFront x) (zeroOutput (frontOutput x.base))
        (zeroTime (frontOutput x.base)) small hr hf
      obtain ⟨n1,hb1,h1⟩ := structure_stop 1 (structureFront x) (structureZero x)
        (zeroTime (frontOutput x.base)) last hlast hlastFinal (by rfl)
      have hvlast : (structureZero x).Valid word bits := withBase_valid (structureFront x) _ word bits hv hvsmall rfl
      refine ⟨n0+n1,?_,?_,?_⟩
      · have hb := Nat.le_max_left (zeroTime (frontOutput x.base))
          (max (oneTime (frontOutput x.base) (pairWord x.base)) (childrenTime (structureFront x) (pairWord x.base)))
        unfold structureTime
        omega
      · simpa only [structureOutput,ha,if_true,hz] using h0.trans h1
      · simpa only [structureOutput,ha,if_true,hz] using hvlast

theorem structure_run (x : Children) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hw : x.base.code.length=x.base.state.bits.length)
    (hk : x.base.kind.length=x.base.state.bits.length) (hc : x.base.count.length=x.base.state.bits.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    ∃ r,runFrom structureMachine (structureTime x) (x.cfg structureMachine.start)=some r ∧
      r.final=(structureOutput x bits).cfg r.final.control ∧ r.steps≤ structureTime x ∧
      (structureOutput x bits).Valid word bits := by
  obtain ⟨n,hn,h,hv⟩ := structure_trace x word bits rows rest hx hw hk hc hp
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [structureMachine,structureStop,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel structureMachine n (structureTime x-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,?_,hs.le.trans hn,hv⟩
  rw [hf]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
