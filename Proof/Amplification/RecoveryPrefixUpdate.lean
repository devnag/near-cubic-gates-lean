import Proof.Amplification.RecoveryPrefixUpdateLayout

/-! The complete executed non-oracle tail of one prefix iteration: copy the
answer, advance the canonical sentinel field, and increment the binary count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixUpdate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open private install_pair from Proof.MachineModel.OrdinarySourceSATLiftMoves
open private install_second from Proof.MachineModel.OrdinaryOracleComposeHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flag_run (cap : Nat) (old answer : Bool) (ambient : Fin 360→List Bool)
    (ha : readTapeBit (ambient 356) 0=answer)
    (ho : ambient 357=ZeroPadding.pad cap [old]) :
    ClockJoin.ReadyRun flagMachine 1 ambient (first cap answer ambient) := by
  classical
  have h := (RecoveryPrefixFlag.copy_ready cap (ambient 356) old answer ha).focus
    flagSlots flag_injective ambient (by
      intro j
      fin_cases j
      · rfl
      · exact ho)
  have he : install flagSlots ambient ![ambient 356,ZeroPadding.pad cap [answer]]=first cap answer ambient := by
    funext i
    by_cases h0 : i=356
    · subst i
      have hl := install_slot flagSlots flag_injective ambient ![ambient 356,ZeroPadding.pad cap [answer]] 0
      simpa [flagSlots,first] using hl
    by_cases h1 : i=357
    · subst i
      have hl := install_slot flagSlots flag_injective ambient ![ambient 356,ZeroPadding.pad cap [answer]] 1
      simpa [flagSlots,first] using hl
    rw [install_other flagSlots ambient _ i (by intro j; fin_cases j <;> simpa [flagSlots] using (by first | exact Ne.symm h0 | exact Ne.symm h1))]
    simp [first,h1]
  rw [he] at h
  exact h

theorem tail_run (cap : Nat) (xs : List Bool) (answer : Bool) (ambient : Fin 360→List Bool)
    (hc : 2*xs.length+13 ≤ cap)
    (hx : ambient 1=ZeroPadding.pad cap (frame (xs++[false,true])))
    (ha : ambient 357=ZeroPadding.pad cap [answer]) (hr : ambient 358=List.replicate cap false) :
    ClockJoin.ReadyRun tailMachine (4*xs.length+28) ambient
      (Function.update ambient 1 (ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true])))) := by
  classical
  have h := (RecoveryPrefixTail.advance_padded cap xs answer hc).focus tailSlots tail_injective ambient
    (by intro j; fin_cases j <;> simpa [tailSlots] using (by assumption))
  rw [←ha,←hr] at h
  have hi := install_second tailSlots tail_injective ambient
    (ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true]))) (ambient 358)
  change install tailSlots ambient
      ![ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true])),ambient 357,ambient 358]=
    Function.update (Function.update ambient 1 (ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true]))))
      358 (ambient 358) at hi
  rw [hi] at h
  have he : Function.update (Function.update ambient 1 (ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true]))))
      358 (ambient 358)=Function.update ambient 1 (ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true]))) := by
    apply Function.update_eq_self_iff.mpr
    simp
  change ClockJoin.ReadyRun tailMachine _ ambient
    (Function.update (Function.update ambient 1 (ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true]))))
      358 (ambient 358)) at h
  rw [he] at h
  exact h

theorem count_run (cap n : Nat) (ambient : Fin 360→List Bool)
    (hc : ClockIncrement.work n.bits ≤ cap)
    (hn : ambient 2=ZeroPadding.pad cap (frame n.bits))
    (hr : ambient 359=List.replicate cap false) :
    ClockJoin.ReadyRun countMachine (4*n.bits.length+8) ambient
      (Function.update ambient 2 (ZeroPadding.pad cap (frame (n+1).bits))) := by
  have h := (RecoveryPrefixCounter.increment_ready cap n hc).focus countSlots count_injective ambient
    (by intro j; fin_cases j <;> simpa [countSlots] using (by assumption))
  rw [←hr] at h
  have hi := install_pair countSlots count_injective ambient (ZeroPadding.pad cap (frame (n+1).bits))
  change install countSlots ambient ![ZeroPadding.pad cap (frame (n+1).bits),ambient 359]=
    Function.update ambient 2 (ZeroPadding.pad cap (frame (n+1).bits)) at hi
  rw [hi] at h
  exact h

theorem update_run (cap n : Nat) (xs : List Bool) (old answer : Bool) (ambient : Fin 360→List Bool)
    (hxcap : 2*xs.length+13 ≤ cap) (hncap : ClockIncrement.work n.bits ≤ cap)
    (hx : ambient 1=ZeroPadding.pad cap (frame (xs++[false,true])))
    (hn : ambient 2=ZeroPadding.pad cap (frame n.bits))
    (ha : readTapeBit (ambient 356) 0=answer) (ho : ambient 357=ZeroPadding.pad cap [old])
    (hr : ambient 358=List.replicate cap false) (hs : ambient 359=List.replicate cap false) :
    ClockJoin.ReadyRun machine (4*xs.length+4*n.bits.length+39) ambient
      (finished cap n xs answer ambient) := by
  have hflag := flag_run cap old answer ambient ha ho
  have htail := tail_run cap xs answer (first cap answer ambient) hxcap
    (by simpa [first] using hx) (by simp [first]) (by simpa [first] using hr)
  have hcount := count_run cap n (second cap xs answer ambient) hncap
    (by simpa [second,first] using hn) (by simpa [second,first] using hs)
  have whole := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hflag htail) hcount
  have he : 1+1+(4*xs.length+28)+1+(4*n.bits.length+8)=4*xs.length+4*n.bits.length+39 := by omega
  rw [he] at whole
  exact whole

end NearCubicWires.RepairOrdinary.RecoveryPrefixUpdate
