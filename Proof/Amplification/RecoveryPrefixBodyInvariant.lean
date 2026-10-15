import Proof.Amplification.RecoveryPrefixBody
import Proof.Amplification.RecoveryPrefixQuery

/-! The executed whole body reproduces its literal tape invariant for the
next zero-first prefix query, preserving the one physical workspace driver. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixBody
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open RecoveryPrefixUpdate RecoveryPrefix RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Inv (cap payload log : Nat) (xs : List Bool) (old : Bool) (padding : List Bool)
    (ambient : Fin 360→List Bool) : Prop where
  payloadField : ambient 0=frame payload.bits++padding
  prefixField : ambient 1=ZeroPadding.pad cap (frame (xs++[false,true]))
  countField : ambient 2=ZeroPadding.pad cap (frame (queryCount xs).bits)
  driver : ambient 3=List.replicate cap true
  logField : ambient 4=List.replicate log false
  bounded : RecoveryQueryKernel.Bounded cap (ambient ∘ querySlots)
  answerField : ambient 357=ZeroPadding.pad cap [old]
  tailReset : ambient 358=List.replicate cap false
  countReset : ambient 359=List.replicate cap false

noncomputable def nextPrefix (flat : Bool) (payload : Nat) (xs : List Bool) := xs++[!answer flat payload xs]
noncomputable def search (flat : Bool) (payload : Nat) : Nat→List Bool→List Bool
  | 0,xs => xs
  | n+1,xs => search flat payload n (nextPrefix flat payload xs)
@[simp] theorem nextPrefix_length (flat : Bool) (payload : Nat) (xs : List Bool) :
    (nextPrefix flat payload xs).length=xs.length+1 := by simp [nextPrefix]
@[simp] theorem search_length (flat : Bool) (payload n : Nat) (xs : List Bool) :
    (search flat payload n xs).length=xs.length+n := by
  induction n generalizing xs with
  | zero => simp [search]
  | succ n ih => simp [search,ih,Nat.add_comm,Nat.add_left_comm]

theorem body_inv (cap payload log : Nat) (flat : Bool) (xs : List Bool) (old : Bool)
    (padding : List Bool) (ambient : Fin 360→List Bool)
    (hi : Inv cap payload log xs old padding ambient)
    (hc : capacity payload (commitment xs) (queryCount xs) ≤ cap) (hz : log ≤ cap+1) :
    ∃ cost ≤ 20*cap,∃ out : Fin 360→List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program flat) cost (start flat ambient) (stopped flat out) ∧
      Inv cap payload (cap+1) (nextPrefix flat payload xs) (answer flat payload xs) padding out := by
  classical
  obtain ⟨cost,hcost,middle,htrace,hkeep,hdriver,hlog,hbound⟩ := body_trace cap log flat payload xs old ambient padding
    hc hi.bounded hi.driver hi.logField hz hi.payloadField hi.prefixField hi.countField hi.answerField hi.tailReset hi.countReset
  let out := finished cap (queryCount xs) xs (answer flat payload xs) (queryOutput ambient middle)
  refine ⟨cost,hcost,out,htrace,?_⟩
  constructor
  · have h0 := (query_output_slot ambient middle 0).trans ((hkeep 0 (by decide)).trans hi.payloadField)
    simpa [out,finished,second,first,querySlots] using h0
  · simp [out,finished,second,first,nextPrefix]
  · simp [out,finished,second,first,nextPrefix,queryCount,Nat.add_assoc]
  · have h3 := (query_output_slot ambient middle 3).trans hdriver
    simpa [out,finished,second,first,querySlots] using h3
  · have h4 := (query_output_slot ambient middle 4).trans hlog
    simpa [out,finished,second,first,querySlots] using h4
  · intro i hlow
    have h357 : querySlots i≠357 := by intro he; have hv:=congrArg (fun j : Fin 360=>j.val) he; change i.val=357 at hv; omega
    have h1 : querySlots i≠1 := by intro he; have hv:=congrArg (fun j : Fin 360=>j.val) he; change i.val=1 at hv; omega
    have h2 : querySlots i≠2 := by intro he; have hv:=congrArg (fun j : Fin 360=>j.val) he; change i.val=2 at hv; omega
    change (out (querySlots i)).length ≤ cap
    simp only [out,finished,second,first,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h357]
    rw [query_output_slot]
    exact hbound i hlow
  · simp [out,finished,second,first]
  · have h358 := (query_output_other ambient middle 358 (by decide)).trans hi.tailReset
    simpa [out,finished,second,first] using h358
  · have h359 := (query_output_other ambient middle 359 (by decide)).trans hi.countReset
    simpa [out,finished,second,first] using h359

end NearCubicWires.RepairSource.RecoveryPrefixBody
