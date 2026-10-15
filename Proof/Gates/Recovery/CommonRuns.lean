import Proof.Gates.Recovery.CommonLayout

/-!
# The common SAT-oracle program of the recovery: its two paths

`inactive_ready`: after a prefix whose live flag reads `false`, the program prints `false`. `live_ready`: after a prefix
whose live flag reads `true`, with the refuter's source input `z` in the hierarchy slot (`RepairOrdinary.frame z ++ post`), the final
address on tape 0 and a run of zeros on the query tape, the after-prefix program runs on its banked ports — the zeros on
the query tape are its blank query tape padded (`OrdinaryOracleCompose.Ready.padding`) — and the program prints the gate
core's bit at the full final length.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.Common

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

noncomputable section

/-- The bank after the prefix. -/
def afterPrefix (p : Params s P g) (bits : List Bool) (out : Fin (pt p) → List Bool) : Fin (tapes p) → List Bool :=
  install (prefixSlot p) (input p bits) out

theorem prefixSlot_val (p : Params s P g) (i : Fin (pt p)) : (prefixSlot p i).val = i.val := rfl

/-- A tape at or past the prefix's bank is blank after the prefix. -/
theorem afterPrefix_blank (p : Params s P g) (bits : List Bool) (out : Fin (pt p) → List Bool) (i : Fin (tapes p))
    (hi : pt p ≤ i.val) : afterPrefix p bits out i = [] := by
  unfold afterPrefix
  rw [install_other _ _ _ _ (by
    intro j he
    have hv := congrArg Fin.val he
    rw [prefixSlot_val] at hv
    have := j.isLt
    omega)]
  have h2 := (prefixProgram p).base.twoTapes
  unfold input
  rw [if_neg (by unfold pt at hi; omega)]

theorem afterPrefix_at (p : Params s P g) (bits : List Bool) (out : Fin (pt p) → List Bool) (i : Fin (pt p)) :
    afterPrefix p bits out (prefixSlot p i) = out i :=
  install_slot _ (prefix_injective p) _ _ i

/-! ## The inactive path -/

theorem false_output (p : Params s P g) : falseSlot p 0 = (ports p).outputTape := by
  change falseSlot p (falseLocal 0) = _
  rw [falseSlot, CloseoutCommonPortBank.shared_slot _ _ (by decide : Function.Injective falseLocal)]
  rfl

theorem false_blank (p : Params s P g) (bits : List Bool) (out : Fin (pt p) → List Bool) (j : Fin 2) :
    afterPrefix p bits out (falseSlot p j) = [] := by
  apply afterPrefix_blank
  have h0 : (falseSlot p 0).val = pt p := by rw [false_output]; rfl
  have h1 : (falseSlot p 1).val = n0 p + ta p + 1 := by
    unfold falseSlot
    rw [CloseoutCommonPortBank.fresh_slot falseLocal (falseShared p) 1 (by intro j; fin_cases j; decide)]
    rfl
  obtain ⟨v, hv⟩ := j
  interval_cases v
  · show pt p ≤ (falseSlot p 0).val
    rw [h0]
  · show pt p ≤ (falseSlot p 1).val
    rw [h1]
    unfold n0
    omega

theorem inactive_ready (p : Params s P g) (bits : List Bool) (fuel : ℕ) (out : Fin (pt p) → List Bool)
    (actual : Ready RecoveryOracle.correctedSat (prefixProgram p) fuel
      (GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.input (work s g) p.refuter g.k bits) out)
    (flag : readTapeBit (out (flagP p)) 0 = false) :
    ∃ final, Ready RecoveryOracle.correctedSat (program p) (fuel + 6) (input p bits) final ∧
      final (ports p).outputTape = RepairOrdinary.frame false.toNat.bits := by
  let mid := afterPrefix p bits out
  have hp := actual.focus (ports p) (prefixSlot p) (prefix_injective p) rfl (input p bits) (fun _ => rfl)
  have hflag : readTapeBit (mid (liveFlag p)) 0 = false := by
    change readTapeBit (afterPrefix p bits out (prefixSlot p (flagP p))) 0 = false
    rw [afterPrefix_at]
    exact flag
  have hf : ReadyRun (RecoveryFocus.machine (falseSlot p) (HierarchyFixedWord.machine [false])) 4 mid
      (install (falseSlot p) mid ![[false], [false]]) :=
    (HierarchyFixedWord.word_ready [false]).focus (falseSlot p) (false_injective p) mid (false_blank p bits out)
  have ta := hp.call (ports p) (pieces p) 0 (next p) 0 2 (by
    intro q
    change some (if readTapeBit (mid (liveFlag p)) 0 then (1 : Fin 3) else 2) = some 2
    rw [hflag]
    rfl)
  have tb := (Ready.ordinary (o := RecoveryOracle.correctedSat) (ports p) hf).stop
    (ports p) (pieces p) 0 (next p) 2 (by intro q; rfl)
  have trace := trans ta tb
  have hc : (fuel + 1) + (4 + 1) = fuel + 6 := by omega
  rw [hc] at trace
  refine ⟨_, ⟨_, trace, ?_, fun _ => rfl, rfl⟩, ?_⟩
  · simp [program, Ports.program, graph, RecoveryCalls.machine, RecoveryCalls.stopped]
  · rw [← false_output]
    exact install_slot (falseSlot p) (false_injective p) mid ![[false], [false]] 0

/-! ## The live path -/

theorem after_query (p : Params s P g) : afterSlot p p.ar.prog.queryTape = (ports p).queryTape := by
  change afterSlot p (afterLocal p 2) = _
  unfold afterSlot
  rw [CloseoutCommonPortBank.shared_slot _ _ (afterLocal_injective p)]
  rfl

theorem after_shared (p : Params s P g) (j : Fin 4) : afterSlot p (afterLocal p j) = lift0 p (afterShared p j) := by
  unfold afterSlot
  rw [CloseoutCommonPortBank.shared_slot _ _ (afterLocal_injective p)]
  rfl

theorem after_output (p : Params s P g) : afterSlot p p.ar.prog.base.outputTape = (ports p).outputTape :=
  after_shared p 3

/-- The query capacities of the padded after-prefix run. -/
def caps (p : Params s P g) (qlen : ℕ) (i : Fin (ta p)) : ℕ := if i = p.ar.prog.queryTape then qlen else 0

theorem live_ready (p : Params s P g) (bits : List Bool) (fuel : ℕ) (out : Fin (pt p) → List Bool)
    (actual : Ready RecoveryOracle.correctedSat (prefixProgram p) fuel
      (GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.input (work s g) p.refuter g.k bits) out)
    (flag : readTapeBit (out (flagP p)) 0 = true)
    (zWord : List Bool) (hword : out (wordP p) = zWord) (haddress : out (addressP p) = RepairOrdinary.frame bits)
    (qlen : ℕ) (hquery : out (prefixProgram p).queryTape = List.replicate qlen false)
    (cost : ℕ) (outA : Fin (ta p) → List Bool)
    (hA : Ready RecoveryOracle.correctedSat p.ar.prog cost
      (afterBank p.ar.zPort p.ar.pointPort zWord (RepairOrdinary.frame bits)) outA) :
    ∃ final, Ready RecoveryOracle.correctedSat (program p) (fuel + 1 + (cost + 1)) (input p bits) final ∧
      final (ports p).outputTape = outA p.ar.prog.base.outputTape := by
  classical
  let mid := afterPrefix p bits out
  have hp := actual.focus (ports p) (prefixSlot p) (prefix_injective p) rfl (input p bits) (fun _ => rfl)
  have hflag : readTapeBit (mid (liveFlag p)) 0 = true := by
    change readTapeBit (afterPrefix p bits out (prefixSlot p (flagP p))) 0 = true
    rw [afterPrefix_at]
    exact flag
  have first := hp.call (ports p) (pieces p) 0 (next p) 0 1 (by
    intro q
    change some (if readTapeBit (mid (liveFlag p)) 0 then (1 : Fin 3) else 2) = some 1
    rw [hflag]
    rfl)
  have hpad := hA.padding (caps p qlen)
  have hin : ∀ j, mid (afterSlot p j) =
      ZeroPadding.pad (caps p qlen j) (afterBank p.ar.zPort p.ar.pointPort zWord (RepairOrdinary.frame bits) j) := by
    intro j
    by_cases hz : j = p.ar.zPort
    · subst hz
      rw [show afterSlot p p.ar.zPort = lift0 p (afterShared p 0) from after_shared p 0]
      have hc : caps p qlen p.ar.zPort = 0 := by unfold caps; rw [if_neg p.ar.zQuery]
      rw [hc, ZeroPadding.pad_zero]
      unfold afterBank
      rw [if_pos rfl]
      change afterPrefix p bits out (prefixSlot p (wordP p)) = zWord
      rw [afterPrefix_at]
      exact hword
    by_cases hpt : j = p.ar.pointPort
    · subst hpt
      rw [show afterSlot p p.ar.pointPort = lift0 p (afterShared p 1) from after_shared p 1]
      have hc : caps p qlen p.ar.pointPort = 0 := by unfold caps; rw [if_neg p.ar.pointQuery]
      rw [hc, ZeroPadding.pad_zero]
      unfold afterBank
      rw [if_neg (Ne.symm p.ar.zPoint), if_pos rfl]
      change afterPrefix p bits out (prefixSlot p (addressP p)) = RepairOrdinary.frame bits
      rw [afterPrefix_at]
      exact haddress
    have hbank : afterBank p.ar.zPort p.ar.pointPort zWord (RepairOrdinary.frame bits) j = [] := by
      unfold afterBank
      rw [if_neg hz, if_neg hpt]
    rw [hbank]
    by_cases hq : j = p.ar.prog.queryTape
    · subst hq
      rw [show afterSlot p p.ar.prog.queryTape = lift0 p (afterShared p 2) from after_shared p 2]
      have hc : caps p qlen p.ar.prog.queryTape = qlen := by unfold caps; rw [if_pos rfl]
      rw [hc]
      change afterPrefix p bits out (prefixSlot p (prefixProgram p).queryTape) = _
      rw [afterPrefix_at, hquery]
      simp [ZeroPadding.pad]
    have hc : caps p qlen j = 0 := by unfold caps; rw [if_neg hq]
    rw [hc, ZeroPadding.pad_zero]
    by_cases ho : j = p.ar.prog.base.outputTape
    · subst ho
      rw [after_output]
      apply afterPrefix_blank
      change pt p ≤ pt p + 0
      omega
    · have hfresh : ∀ i, afterLocal p i ≠ j := by
        intro i he
        fin_cases i
        · exact hz he.symm
        · exact hpt he.symm
        · exact hq he.symm
        · exact ho he.symm
      apply afterPrefix_blank
      unfold afterSlot
      rw [CloseoutCommonPortBank.fresh_slot _ _ _ hfresh]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      unfold n0
      omega
  have second := hpad.focus (ports p) (afterSlot p) (after_injective p) (after_query p) mid hin
  have tb := second.stop (ports p) (pieces p) 0 (next p) 1 (by intro q; rfl)
  have trace := trans first tb
  refine ⟨_, ⟨_, trace, ?_, fun _ => rfl, rfl⟩, ?_⟩
  · simp [program, Ports.program, graph, RecoveryCalls.machine, RecoveryCalls.stopped]
  · rw [← after_output]
    have hc : caps p qlen p.ar.prog.base.outputTape = 0 := by
      unfold caps; rw [if_neg (Ne.symm p.ar.queryOutput)]
    refine (install_slot (afterSlot p) (after_injective p) mid
      (fun i => ZeroPadding.pad (caps p qlen i) (outA i)) p.ar.prog.base.outputTape).trans ?_
    rw [hc, ZeroPadding.pad_zero]

end

end NearCubicGates.Close.Recovery.Common
