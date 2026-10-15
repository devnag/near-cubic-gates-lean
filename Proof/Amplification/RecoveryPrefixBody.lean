import Proof.Amplification.RecoveryPrefixBodyLayout
import Proof.Amplification.RecoveryPrefixBudget

/-! One whole prefix-search iteration executes the exact compact SAT
query, copies its answer, advances the canonical sentinel commitment and
increments the actual binary count. The same workspace is retained. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixBody
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open RecoveryPrefixUpdate RecoveryPrefix RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def answer (flat : Bool) (payload : Nat) (xs : List Bool) : Bool :=
  RecoveryOracle.correctedSat (code flat payload (commitment xs) (queryCount xs))

private theorem query_halted {t s : Nat} (p : Machine t s) (slot : Fin t) (out : Fin t→List Bool) :
    (RecoveryQueryCall.piece p slot).machine.halted (RecoveryQueryCall.stopped p slot out).control=true := by
  simp [RecoveryQueryCall.piece,graph,RecoveryCalls.machine,RecoveryQueryCall.stopped,RecoveryCalls.stopped]

theorem body_trace (cap log : Nat) (flat : Bool) (payload : Nat) (xs : List Bool)
    (old : Bool) (ambient : Fin 360→List Bool) (padding : List Bool)
    (hcap : capacity payload (commitment xs) (queryCount xs) ≤ cap)
    (hb : RecoveryQueryKernel.Bounded cap (ambient ∘ querySlots))
    (hd : ambient 3=List.replicate cap true) (hl : ambient 4=List.replicate log false) (hz : log ≤ cap+1)
    (hp : ambient 0=frame payload.bits++padding)
    (hx : ambient 1=ZeroPadding.pad cap (frame (xs++[false,true])))
    (hn : ambient 2=ZeroPadding.pad cap (frame (queryCount xs).bits))
    (ho : ambient 357=ZeroPadding.pad cap [old])
    (hr : ambient 358=List.replicate cap false) (hs : ambient 359=List.replicate cap false) :
    ∃ cost ≤ 20*cap,∃ middle : Fin 357→List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program flat) cost (start flat ambient)
        (stopped flat (finished cap (queryCount xs) xs (answer flat payload xs) (queryOutput ambient middle))) ∧
      (∀ i : Fin 357,i.val<3 → middle i=ambient (querySlots i)) ∧
      middle 3=List.replicate cap true ∧ middle 4=List.replicate (cap+1) false ∧
      RecoveryQueryKernel.Bounded cap middle := by
  obtain ⟨queryCost,hqueryCost,middle,hquery,hanswer,hkeep,hdriver,hlog,hbound⟩ :=
    RecoveryQueryStep.step_trace cap log flat payload (commitment xs) (queryCount xs)
      (ambient ∘ querySlots) padding
      (List.replicate (cap-(frame (commitment xs).bits).length) false)
      (List.replicate (cap-(frame (queryCount xs).bits).length) false)
      hcap hb hd hl hz hp (by simpa [commitment_bits,Function.comp_def,querySlots,ZeroPadding.pad] using hx) hn
  let after := queryOutput ambient middle
  have hread : readTapeBit (after 356) 0=answer flat payload xs := by
    have he := query_output_slot ambient middle (356 : Fin 357)
    change after 356=middle 356 at he
    rw [he]
    exact hanswer
  have hx' : after 1=ZeroPadding.pad cap (frame (xs++[false,true])) :=
    (query_output_slot ambient middle 1).trans ((hkeep 1 (by decide)).trans hx)
  have hn' : after 2=ZeroPadding.pad cap (frame (queryCount xs).bits) :=
    (query_output_slot ambient middle 2).trans ((hkeep 2 (by decide)).trans hn)
  have ho' : after 357=ZeroPadding.pad cap [old] := (query_output_other ambient middle 357 (by decide)).trans ho
  have hr' : after 358=List.replicate cap false := (query_output_other ambient middle 358 (by decide)).trans hr
  have hs' : after 359=List.replicate cap false := (query_output_other ambient middle 359 (by decide)).trans hs
  obtain ⟨hxt,hnt,hbudget⟩ := update_capacity cap payload xs hcap
  obtain ⟨last,hrun,htapes,hheads,hsteps⟩ := update_run cap (queryCount xs) xs old
    (answer flat payload xs) after hxt hnt hx' hn' hread ho' hr' hs'
  have focusedQuery := focus_trace ports querySlots query_injective (by rfl) (fun _=>0) ambient hquery
  have queryBody := graph_trace ports (pieces flat) 0 (next flat) 0 focusedQuery
  rw [query_final] at queryBody
  have queryHalted : (pieces flat 0).machine.halted (RecoveryQueryStep.stopped flat middle).control=true := by
    exact query_halted (RecoveryQueryKernel.kernel flat) RecoveryQueryStep.answerSlot middle
  have ret := graph_return RecoveryOracle.correctedSat ports (pieces flat) 0 (next flat) 0 1
    (⟨(RecoveryQueryStep.stopped flat middle).control,fun _=>0,after⟩ :
      Configuration 360 (RecoveryQueryStep.program flat).base.stateCount) queryHalted (by rfl)
  have updateBody := graph_trace ports (pieces flat) 0 (next flat) 1
    (ordinary_trace (o:=RecoveryOracle.correctedSat) ports RecoveryPrefixUpdate.machine _ _ last hrun)
  have updateHalted := (prefix_of_run RecoveryPrefixUpdate.machine _ _ last hrun).2
  have stop := graph_stop RecoveryOracle.correctedSat ports (pieces flat) 0 (next flat) 1
    last.final updateHalted (by rfl)
  have hh : last.final.heads=(fun _=>0) := funext hheads
  rw [hh,htapes] at stop
  have whole := OrdinaryOracleCompose.trans (OrdinaryOracleCompose.trans
    (OrdinaryOracleCompose.trans queryBody ret) updateBody) stop
  exact ⟨queryCost+1+last.steps+1,by omega,middle,whole,hkeep,hdriver,hlog,hbound⟩

end NearCubicWires.RepairSource.RecoveryPrefixBody
