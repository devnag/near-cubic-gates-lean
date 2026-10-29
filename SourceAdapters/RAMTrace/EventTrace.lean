import SourceAdapters.RAMTrace.Theorem
import SourceAdapters.Joins.RAMEventTrace

/-!
# The join `RAMEventTrace`: `thm:trace` and `cor:trace-verifier`

`app:event-trace`. `thm:trace` is `event_trace_iff`. `cor:trace-verifier` (Step 1 of the short PCP, machine side) composes P02's
`mn_bhram_clock` (`V` accepts `x` with a `t`-bit witness iff `(x̄, 1^τ, 1^τ) ∈ BH_RAM(M_n)`) with `thm:trace` at
`M = M_n`, whose arithmetic unit is `add, sub, and, cmp` (`mnAlu_kind`); the side conditions of `app:event-trace` Setting are
P02's clock facts (`mn_setting`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.ShortPCP

/-- `M_n`'s arithmetic unit is `(add, sub, and, cmp)`. -/
theorem mnAlu_kind (w : ℕ) (op : Fin 4) : mnAlu w op = (mnKind op).fn := by
  fin_cases op <;> rfl

/-- `app:event-trace` Setting at the clock parameters: `w_n = 2^ω`, `1 ≤ τ`, `ω ≤ τ`, `τ < w_n`, `|x̄| ≤ 2^τ`. -/
theorem mn_setting (V : OrdinaryVerifier) (c n t : ℕ) (hc : clockConst V ≤ c) (hn : 1 ≤ n) (hnt : n ≤ t)
    (x : BitInput n) :
    wordWidth c t = 2 ^ Nat.log 2 (wordWidth c t) ∧ 1 ≤ timeExp c t ∧ Nat.log 2 (wordWidth c t) ≤ timeExp c t ∧
      timeExp c t < wordWidth c t ∧ (padInput c t x).length ≤ 2 ^ timeExp c t := by
  obtain ⟨h16, -⟩ := clockConst_facts V c hc
  have hw : wordWidth c t = 2 ^ Nat.clog 2 (Nat.clog 2 t + c) := rfl
  have hlog : Nat.log 2 (wordWidth c t) = Nat.clog 2 (Nat.clog 2 t + c) := by
    rw [hw, Nat.log_pow (by norm_num)]
  have hτ := (instance_side_conditions c n t h16 hn hnt).1
  have hTw := (two_pow_wordWidth c t h16 (by omega)).2
  have hwT : wordWidth c t ≤ padTime c t := by
    have := padTime_ge c t
    have : wordWidth c t ≤ c * (t + wordWidth c t) := by nlinarith
    omega
  refine ⟨by rw [hlog]; rfl, hτ, ?_, ?_, (padInput_facts V c n t hc hn hnt x).2.1.le⟩
  · rw [hlog]
    have : 2 ^ Nat.clog 2 (Nat.clog 2 t + c) ≤ 2 ^ timeExp c t := by
      rw [← hw]; exact hwT
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  · unfold padTime at hTw
    have hle : 2 ^ timeExp c t < 2 ^ wordWidth c t := hTw
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hle

/-- **`cor:trace-verifier` (Step 1 of the short PCP, the machine side).** -/
theorem step_one_event_trace (F : Type) [CommRing F] [CharP F 2] (V : OrdinaryVerifier) (c : ℕ)
    (hc : clockConst V ≤ c) (r : Joins.ClockRequest) (hfit : codeLen V ≤ 2 ^ wordWidth c r.2)
    (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) (hrun : Joins.RunsWithin V r.1.2 r.2) :
    (∃ y : BitInput r.2, V.accepts (List.ofFn r.1.2) (List.ofFn y)) ↔
      Satisfiable F (mnRam V (wordWidth c r.2) r.1.1 r.2 (2 ^ timeExp c r.2) hfit) mnKind (timeExp c r.2)
        (padInput c r.2 r.1.2) := by
  obtain ⟨hw2, hτ, hωτ, hτw, hlen⟩ := mn_setting V c r.1.1 r.2 hc (by omega) hnt r.1.2
  rw [mn_bhram_clock V c r.1.1 r.2 hc (by omega) hnt r.1.2 hrun]
  exact (event_trace_iff (mnRam V (wordWidth c r.2) r.1.1 r.2 (2 ^ timeExp c r.2) hfit) mnKind (timeExp c r.2)
    (padInput c r.2 r.1.2) (mnAlu_kind _) hw2 hτ hωτ hτw hlen).symm

/-- **The join `RAMEventTrace` holds** (`thm:trace` and `cor:trace-verifier`). -/
theorem ramEventTrace : Joins.RAMEventTrace :=
  ⟨fun _ _ _ M kind τ xbar halu hw2 hτ hωτ hτw _ hlen => event_trace_iff M kind τ xbar halu hw2 hτ hωτ hτw hlen,
    fun F _ _ V c hc r hfit hn hnt hrun => step_one_event_trace F V c hc r hfit hn hnt hrun⟩

end NearCubicGates.Adapters.RAMTrace
