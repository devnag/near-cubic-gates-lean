import Proof.MachineModel.UPreparedRun
import Proof.MachineModel.OrdinaryTransitionWalkInitialConsumer
import Proof.MachineModel.OrdinaryMemoryCheckerCost
import Proof.MachineModel.UMemoryClose
import Proof.MachineModel.ClockTotal

/-! Fixed U's aggregate clock ledger. The prefix fuel already depends on
the global L cap. Both emitter returns and its rejection branch are paid,
and closing uses the accepted doubled-emitter/checker bound. -/
namespace NearCubicWires.RepairOrdinary.UAggregateClock
open LocalBitMultitape PCPResourceLedger RepairSource VerifierEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient : ℕ := 2097152
def exponent : ℕ := 5
def offset : ℕ := 23
def eventCap (N : ℕ) : ℕ := ClockDyadicLedger.limit N*(Nat.log 2 N+5)
def prefixFuel (N : ℕ) : ℕ := 600*(N+1)*q N^2+
  400*(ClockDyadicLedger.limit N+1)*(ClockDyadicLedger.width N+1)+
  32768*(Nat.log 2 N+1)*(ClockDyadicLedger.width N+1)+7
def walkFuel (N : ℕ) : ℕ := 2048*(eventCap N+1)*(ClockDyadicLedger.width N+Nat.log 2 N+1)^2
def checkerFuel (N : ℕ) : ℕ := 2048*(eventCap N+1)*(2*ClockDyadicLedger.width N+3)^2
/-- +2 pays the two successful returns; +4 also covers prefix, reject and stop. -/
def emissionFuel (N : ℕ) : ℕ := prefixFuel N+walkFuel N+4
/-- Closing pays +10; +3 reserves the final control-based acceptance gate. -/
def fuel (N : ℕ) : ℕ := 2*emissionFuel N+checkerFuel N+13
def scale (N : ℕ) : ℕ := (N+ClockDyadicLedger.limit N+1)*q N^5
def envelope (N : ℕ) : ℕ := coefficient*scale N
def time (N : ℕ) : ℕ := ClockEnvelope.clock offset exponent N

theorem log_bound (N : ℕ) : Nat.log 2 N+1 ≤ q N := by
  have h := (Nat.log_mono_right (Nat.le_succ N)).trans (Nat.log_le_clog 2 (N+1))
  dsimp [q,ell]
  omega

theorem short_bounds (N : ℕ) :
    1 ≤ q N ∧ ClockDyadicLedger.width N+1 ≤ 4*q N^2 ∧
    ClockDyadicLedger.width N+Nat.log 2 N+1 ≤ 4*q N^2 ∧
    2*ClockDyadicLedger.width N+3 ≤ 9*q N^2 := by
  have hq : 1 ≤ q N := by simp [q]
  have hq2 : q N ≤ q N^2 := Nat.le_self_pow (by decide) _
  have hw := (ClockDyadicLedger.width_bounds N).2
  have hl := log_bound N
  refine ⟨hq,?_,?_,?_⟩ <;> nlinarith

theorem scale_positive (N : ℕ) : 1 ≤ scale N := by
  have hq := Nat.one_le_pow 5 (q N) (short_bounds N).1
  dsimp [scale]
  nlinarith

theorem event_cap_bound (N : ℕ) : eventCap N+1 ≤ 5*(N+ClockDyadicLedger.limit N+1)*q N := by
  have hq := (short_bounds N).1
  have hl := log_bound N
  have hlog : Nat.log 2 N+5 ≤ 5*q N := by omega
  have he := Nat.mul_le_mul_left (ClockDyadicLedger.limit N) hlog
  dsimp [eventCap]
  nlinarith

theorem prefix_bound (N : ℕ) : prefixFuel N ≤ 133279*scale N := by
  have hq := (short_bounds N).1
  have hw := (short_bounds N).2.1
  have hl := log_bound N
  have h2 : q N^2 ≤ q N^5 := Nat.pow_le_pow_right hq (by decide)
  have h3 : q N^3 ≤ q N^5 := Nat.pow_le_pow_right hq (by decide)
  have hN : (N+1)*q N^2 ≤ scale N :=
    Nat.mul_le_mul (by omega) h2
  have hL : (ClockDyadicLedger.limit N+1)*(ClockDyadicLedger.width N+1) ≤ 4*scale N := by
    calc _ ≤ (ClockDyadicLedger.limit N+1)*(4*q N^2) := Nat.mul_le_mul_left _ hw
         _ ≤ (N+ClockDyadicLedger.limit N+1)*(4*q N^5) := by gcongr; omega
         _=4*scale N := by dsimp [scale]; ring
  have hlog : (Nat.log 2 N+1)*(ClockDyadicLedger.width N+1) ≤ 4*scale N := by
    calc _ ≤ q N*(4*q N^2) := Nat.mul_le_mul hl hw
         _=4*q N^3 := by ring
         _ ≤ 4*((N+ClockDyadicLedger.limit N+1)*q N^5) := by
           apply Nat.mul_le_mul_left
           exact h3.trans (Nat.le_mul_of_pos_left _ (by omega))
         _=4*scale N := rfl
  have hp := scale_positive N
  dsimp only [prefixFuel]
  nlinarith

theorem walk_bound (N : ℕ) : walkFuel N ≤ 163840*scale N := by
  calc _ ≤ 2048*(5*(N+ClockDyadicLedger.limit N+1)*q N)*(4*q N^2)^2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (event_cap_bound N))
            (Nat.pow_le_pow_left (short_bounds N).2.2.1 2)
       _=163840*scale N := by dsimp [scale]; ring

theorem checker_bound (N : ℕ) : checkerFuel N ≤ 829440*scale N := by
  calc _ ≤ 2048*(5*(N+ClockDyadicLedger.limit N+1)*q N)*(9*q N^2)^2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (event_cap_bound N))
            (Nat.pow_le_pow_left (short_bounds N).2.2.2 2)
       _=829440*scale N := by dsimp [scale]; ring

theorem emission_bound (N : ℕ) : emissionFuel N ≤ 297123*scale N := by
  have hp := prefix_bound N
  have hw := walk_bound N
  have hs := scale_positive N
  dsimp [emissionFuel]
  omega

theorem fuel_bound (N : ℕ) : fuel N ≤ 1423699*scale N ∧ fuel N ≤ envelope N := by
  have he := emission_bound N
  have hc := checker_bound N
  have hs := scale_positive N
  have hb : fuel N ≤ 1423699*scale N := by dsimp [fuel]; omega
  exact ⟨hb,hb.trans (by dsimp [envelope,coefficient]; omega)⟩

theorem time_bounds (N : ℕ) : envelope N ≤ time N ∧
    time N ≤ 268435456*(N+ClockDyadicLedger.limit N+1)*q N^5 := by
  have h := ClockEnvelope.envelope coefficient offset exponent N (by norm_num [coefficient,offset])
  simpa only [ClockEnvelope.original,envelope,scale,time,exponent,offset,Nat.mul_assoc,show 2^(23+5)=268435456 by norm_num] using h

theorem fuel_le_time (N : ℕ) : fuel N ≤ time N := (fuel_bound N).2.trans (time_bounds N).1

theorem input_le_time (N : ℕ) : N ≤ time N := by
  have hq := Nat.one_le_pow 5 (q N) (short_bounds N).1
  have hs : N ≤ scale N := (show N ≤ N+ClockDyadicLedger.limit N+1 by omega).trans
    (by simpa only [scale,mul_one] using Nat.mul_le_mul_left (N+ClockDyadicLedger.limit N+1) hq)
  exact (hs.trans (by dsimp [envelope,coefficient]; omega)).trans (time_bounds N).1

theorem witness_le_time (N witnessBits : ℕ)
    (h : witnessBits ≤ 4*ClockDyadicLedger.limit N*q N^2) : witnessBits ≤ time N := by
  have hq := (short_bounds N).1
  have hp : q N^2 ≤ q N^5 := Nat.pow_le_pow_right hq (by decide)
  have hs : 4*ClockDyadicLedger.limit N*q N^2 ≤ 4*scale N := by
    dsimp [scale]
    calc _ ≤ 4*(N+ClockDyadicLedger.limit N+1)*q N^5 := by gcongr; omega
         _=4*((N+ClockDyadicLedger.limit N+1)*q N^5) := by ring
  exact (h.trans hs).trans ((by dsimp [envelope,coefficient]; omega : 4*scale N ≤ envelope N).trans (time_bounds N).1)

theorem prepared_prefix_bound (raw : List Bool) : UPrepared.budget raw ≤ prefixFuel raw.length :=
  UPrepared.budget_bound raw

theorem emission_valid_bound (raw : List Bool) (walkSteps : ℕ)
    (hw : walkSteps ≤ walkFuel raw.length) :
    UPrepared.budget raw+walkSteps+2 ≤ emissionFuel raw.length := by
  have hp := prepared_prefix_bound raw
  dsimp [emissionFuel]
  omega

theorem emission_reject_bound (raw : List Bool) : UPrepared.budget raw+4 ≤ emissionFuel raw.length := by
  have hp := prepared_prefix_bound raw
  dsimp [emissionFuel]
  omega

theorem event_bound (N E c : ℕ) (hE : E ≤ ClockDyadicLedger.limit N*(c+5))
    (hc : c ≤ Nat.log 2 N) : E ≤ eventCap N :=
  hE.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hc 5))

theorem actual_walk_bound (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) (input witness : List Bool) (m : ℕ)
    (hc : (code v).length ≤ Nat.log 2 N)
    (he : events input.length witness.length m v.tapeCount ≤ eventCap N) :
    (m+1)*TransitionWalk.cycleBudget
      (TransitionWalk.initialStore N v codePos scans scanPos input witness m) ≤ walkFuel N := by
  have h := TransitionWalk.initial_walk_budget N v codePos scans scanPos input witness m
  exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right he 1))
    (Nat.pow_le_pow_left (by omega) 2))

theorem guarded_event_bound (N n B m t c : ℕ) (hN : 2 ≤ N)
    (hn : n ≤ B) (hB : B ≤ ClockDyadicLedger.limit N) (hm : m ≤ B)
    (ht : t ≤ c) (hc : c ≤ Nat.log 2 N) : events n B m t ≤ eventCap N := by
  have hL := hN.trans (ClockEnvelope.input_le_limit N)
  exact event_bound N (events n B m t) c
    (PCPResourceLedger.record_count n B m t c (ClockDyadicLedger.limit N) hL hn hB hm ht) hc

theorem actual_checker_bound (N : ℕ) (req : MemoryChecker.Request)
    (he : req.count ≤ eventCap N) (hi : req.indexBits=2*ClockDyadicLedger.width N) :
    MemoryChecker.rawBudget req ≤ checkerFuel N := by
  have h := MemoryChecker.whole_budget req
  have hb : MemoryChecker.rawBudget req ≤ 2048*(req.count+1)*(req.indexBits+3)^2 := by omega
  rw [hi] at hb
  exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right he 1)))

theorem answer_budget_bound (N : ℕ) (answer : Option MemoryChecker.Request)
    (h : ∀ req,answer=some req → req.count ≤ eventCap N ∧ req.indexBits=2*ClockDyadicLedger.width N) :
    UMemoryClose.answerBudget answer ≤ checkerFuel N := by
  cases answer with
  | none => simp [UMemoryClose.answerBudget]
  | some req => exact actual_checker_bound N req (h req rfl).1 (h req rfl).2

theorem actual_closing_bound (N emissionSteps : ℕ) (answer : Option MemoryChecker.Request)
    (he : emissionSteps ≤ emissionFuel N)
    (ha : ∀ req,answer=some req → req.count ≤ eventCap N ∧ req.indexBits=2*ClockDyadicLedger.width N) :
    2*emissionSteps+UMemoryClose.answerBudget answer+10 ≤ fuel N ∧
    2*emissionSteps+UMemoryClose.answerBudget answer+10 ≤ time N := by
  have hc := answer_budget_bound N answer ha
  have hb : 2*emissionSteps+UMemoryClose.answerBudget answer+10 ≤ fuel N := by dsimp [fuel]; omega
  exact ⟨hb,hb.trans (fuel_le_time N)⟩

theorem total_clock_producer (bits : List Bool) :
    ∃ r : ExecutionReceipt 34 (Fintype.card (RecoveryCalls.Control (ClockTotal.sizes offset exponent))),
      run (ClockTotal.machine offset exponent) (ClockTotal.budget offset exponent bits)
        (ClockFromInput.input bits)=some r ∧
      r.final.tapes 29=frame (SignedSortKey.binary (ClockEnvelope.exponent offset exponent bits.length+1)
        (time bits.length)) ∧
      r.final.tapes 27=List.replicate (ClockEnvelope.exponent offset exponent bits.length) true ∧
      r.final.tapes 12=frame bits ∧ (∀ i,r.final.heads i=0) ∧
      r.steps ≤ 11658*(bits.length+1)*q bits.length^2 := by
  obtain ⟨r,hr,ht,he,hi,hh,hs⟩ := ClockTotal.entry_run offset exponent bits
  refine ⟨r,hr,ht,he,hi,hh,?_⟩
  simpa only [ClockTotal.budget,offset,exponent,show 402*(5+23+1)=11658 by decide] using hs

theorem producer_budget_bound (bits : List Bool) : ClockTotal.budget offset exponent bits ≤ time bits.length := by
  have hq := (short_bounds bits.length).1
  have hp : q bits.length^2 ≤ q bits.length^5 := Nat.pow_le_pow_right hq (by decide)
  have hs : (bits.length+1)*q bits.length^2 ≤ scale bits.length :=
    Nat.mul_le_mul (by omega) hp
  have hb : ClockTotal.budget offset exponent bits ≤ envelope bits.length := by
    simp only [ClockTotal.budget,offset,exponent,show 402*(5+23+1)=11658 by decide]
    dsimp [envelope,coefficient]
    nlinarith
  exact hb.trans (time_bounds bits.length).1

theorem final_carrier_bound (N emissionSteps : ℕ) (answer : Option MemoryChecker.Request)
    (he : emissionSteps ≤ emissionFuel N)
    (ha : ∀ req,answer=some req → req.count ≤ eventCap N ∧ req.indexBits=2*ClockDyadicLedger.width N) :
    2*emissionSteps+UMemoryClose.answerBudget answer+13 ≤ fuel N ∧
    2*emissionSteps+UMemoryClose.answerBudget answer+13 ≤ time N := by
  have hc := answer_budget_bound N answer ha
  have hb : 2*emissionSteps+UMemoryClose.answerBudget answer+13 ≤ fuel N := by dsimp [fuel]; omega
  exact ⟨hb,hb.trans (fuel_le_time N)⟩

end NearCubicWires.RepairOrdinary.UAggregateClock
