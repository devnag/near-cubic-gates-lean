import Proof.MachineModel.OrdinarySourceSATLiftRequestCold

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header_call (code : List Bool) (C D n b np bp : ℕ) (out : List Bool)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool)
    (ready : Ready D n b np bp out heads data) : ∃ hh tt,
    Path code C D 2 3 ((header code).length+1) heads hh data tt ∧
      Ready D n b np bp (out++header code) hh tt := by
  obtain ⟨r,hr,hs,hh,ht,other⟩ := RequestMoves.print_run (outSlot D) (header code) out heads data ready.out_head ready.out_data
  exact ⟨r.final.heads,r.final.tapes,call_run code C D 2 3 _ heads data r hr hs.le (fun _ => rfl) rfl,
    ready.print hh ht other⟩

theorem separator_call (code : List Bool) (C D n b np bp : ℕ) (out : List Bool)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool)
    (ready : Ready D n b np bp out heads data) : ∃ hh tt,
    Path code C D 4 5 7 heads hh data tt ∧ Ready D n b np bp (out++separator) hh tt := by
  obtain ⟨r,hr,hs,hh,ht,other⟩ := RequestMoves.print_run (outSlot D) separator out heads data ready.out_head ready.out_data
  exact ⟨r.final.heads,r.final.tapes,call_run code C D 4 5 _ heads data r hr hs.le (fun _ => rfl) rfl,
    ready.print hh ht other⟩

theorem scale_n_call (code : List Bool) (C D n b bp : ℕ) (out : List Bool)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool)
    (ready : Ready D n b 0 bp out heads data) : ∃ hh tt,
    Path code C D 3 4 (10*n+2) heads hh data tt ∧
      Ready D n b n bp (out++List.replicate (8*n) true) hh tt := by
  obtain ⟨r,hr,hs,hn,tn,ho,tout,other⟩ := RequestMoves.scale_run (scaleSlots D false) (scale_injective D false)
    8 n out heads data ready.n_head ready.out_head ready.n_data ready.out_data
  have hb := other (bSlot D) (by
    intro j; fin_cases j
    · exact n_ne_b D
    · exact Ne.symm (power_ne_out D _))
  refine ⟨r.final.heads,r.final.tapes,?_,hn,tn,hb.1.trans ready.b_head,hb.2.trans ready.b_data,ho,tout⟩
  exact call_run code C D 3 4 _ heads data r hr hs.le (fun _ => rfl) rfl

theorem scale_b_call (code : List Bool) (C D n b np : ℕ) (out : List Bool)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool)
    (ready : Ready D n b np 0 out heads data) : ∃ hh tt,
    Path code C D 5 6 (6*b+2) heads hh data tt ∧
      Ready D n b np b (out++List.replicate (4*b) true) hh tt := by
  obtain ⟨r,hr,hs,hb,tb,ho,tout,other⟩ := RequestMoves.scale_run (scaleSlots D true) (scale_injective D true)
    4 b out heads data ready.b_head ready.out_head ready.b_data ready.out_data
  have hn := other (nSlot D) (by
    intro j; fin_cases j
    · exact Ne.symm (n_ne_b D)
    · exact Ne.symm (power_ne_out D _))
  refine ⟨r.final.heads,r.final.tapes,?_,hn.1.trans ready.n_head,hn.2.trans ready.n_data,hb,tb,ho,tout⟩
  exact call_run code C D 5 6 _ heads data r hr hs.le (fun _ => rfl) rfl

theorem trailer_call (code : List Bool) (C D n b np bp : ℕ) (out : List Bool)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool)
    (ready : Ready D n b np bp out heads data) : ∃ final,
    OrdinaryOracleTrace RecoveryOracle.correctedSat (program code C D) 4
      (atCall code C D 6 heads data) final ∧
      (program code C D).base.machine.halted final.control=true ∧
      final.tapes (outSlot D)=out++trailer := by
  obtain ⟨r,hr,hs,_hh,ht,_other⟩ := RequestMoves.print_run (outSlot D) trailer out heads data ready.out_head ready.out_data
  have run := stop_run code C D trailer.length heads data r hr
  rw [hs] at run
  refine ⟨_,run,?_,ht⟩
  simp [program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]

def emitBudget (code : List Bool) (C D n : ℕ) := (header code).length+10*n+6*(C*(n+1)^D)+16

theorem emit (code : List Bool) (C D n : ℕ)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool)
    (ready : Ready D n (C*(n+1)^D) 0 0 [] heads data) : ∃ used final,
    used ≤ emitBudget code C D n ∧ OrdinaryOracleTrace RecoveryOracle.correctedSat (program code C D) used
      (atCall code C D 2 heads data) final ∧
      (program code C D).base.machine.halted final.control=true ∧
      final.tapes (outSlot D)=frame (value code C D n) := by
  obtain ⟨h1,t1,p1,r1⟩ := header_call code C D n _ 0 0 [] heads data ready
  obtain ⟨h2,t2,p2,r2⟩ := scale_n_call code C D n _ 0 _ h1 t1 r1
  obtain ⟨h3,t3,p3,r3⟩ := separator_call code C D n _ n 0 _ h2 t2 r2
  obtain ⟨h4,t4,p4,r4⟩ := scale_b_call code C D n _ n _ h3 t3 r3
  obtain ⟨final,last,hhalt,hout⟩ := trailer_call code C D n _ n _ _ h4 t4 r4
  obtain ⟨used,hused,htrace⟩ := ((p1.trans p2).trans p3).trans p4
  refine ⟨used+4,final,?_,OrdinaryOracleCompose.trans htrace last,hhalt,?_⟩
  · unfold emitBudget
    omega
  · rw [frame_value]
    simpa only [List.nil_append,List.append_assoc] using hout

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
