import Proof.Gates.CounterMachine.TabCallStageB
import Proof.Gates.Interfaces.WordFn

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter

variable {B1 B2 cT : ℕ}

/-- The hypotheses of `stA_spec`, bundled. -/
structure AHyp (x : TabCallReq B1 B2 cT) (Λ cap Cl El : ℕ) : Prop where
  b1 : ∀ v ∈ descN x.id, natBitLength v + 2 ≤ Λ ∧ 2 ^ (natBitLength v + 1) ≤ Λ
  bits : ∀ y ∈ descN x.id ++ cellN x.r.c x.r.p x.r.wt, natBitLength y + 2 ≤ Λ
  len : (descN x.id ++ cellN x.r.c x.r.p x.r.wt).length ≤ Λ
  rd1 : ∀ v ∈ [x.r.c.n, kindTag x.r.c.kind, x.r.c.first.gates.length, x.r.c.first.coeffs.length,
      x.r.c.first.table.length, x.r.c.second.gates.length, x.r.c.second.coeffs.length, x.r.c.second.table.length,
      x.r.c.parity.length], 2 ^ (natBitLength v + 1) ≤ Λ
  hn : 2 * x.r.c.n + 3 ≤ Λ
  rd2 : ∀ v ∈ [x.r.p.k, x.r.p.P, x.r.p.e, x.r.p.J, (x.r.p.primes.sort (· ≤ ·)).length, x.r.p.factors.length],
      2 ^ (natBitLength v + 1) ≤ Λ
  rd3 : 2 ^ (natBitLength (coordsOf x.r.wt.I).length + 1) ≤ Λ ∧ ∀ s < x.r.p.J,
      2 ^ (natBitLength (x.r.wt.coef s 0).length + 1) ≤ Λ ∧ 2 ^ (natBitLength (x.r.wt.coef s 1).length + 1) ≤ Λ
  hcap : 40 * (Λ + 1) ^ 2 + 20 * (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt)).length +
      4 * (tabCallInput x).length + Λ + (encN (dRho x.id)).length + 10 ≤ cap
  sm : dF1 x.id + kindTag x.r.c.kind + 3 ≤ cap
  c3a : 2 * (x.r.p.J + 1) + 2 * x.r.p.k + x.r.c.first.gates.length + dF2 x.id + 2 * (tabCallInput x).length + 10 ≤ cap
  c3c : 4 * (lcap Cl El x.r.c.n x.r.p.k * (x.r.c.n + 1)) + 2 * x.r.c.n + 10 ≤ cap
  kn : x.r.p.k ≤ x.r.c.n

section Prog
variable (PolyTab : TabMachine) (PM : PrefixMachine B1 B2 cT)

/-- The prefix machine's tape count. -/
abbrev tPof : ℕ := PM.wf.program.tapeCount

abbrev tKof : ℕ := PolyTab.wf.program.tapeCount

/-- **RK's program.** -/
noncomputable def tabCallProg (Cl El : ℕ) : WMX (NS (tPof PM) (tKof PolyTab)) NR :=
  .seq (.wm (stA (tPof PM) (tKof PolyTab) Cl El))
    (.seq (WMX.machZ PM.wf.program.machine (fun j => pmap (tPof PM) (tKof PolyTab) j) (sLOG (tPof PM) (tKof PolyTab)))
      (.seq (.wm (stB (tPof PM) (tKof PolyTab) PM.wf.program.outputTape))
        (WMX.machZ PolyTab.wf.program.machine (fun j => kmap (tPof PM) (tKof PolyTab) j) (sLOG (tPof PM) (tKof PolyTab)))))

def tabCallOut : Fin (NS (tPof PM) (tKof PolyTab) + 1) := kmap (tPof PM) (tKof PolyTab) PolyTab.wf.program.outputTape

theorem tabCallOut_ne : (tabCallOut PolyTab PM).val ≠ 0 := by simp [tabCallOut]

/-- RK's step count. -/
noncomputable def tabCallCost (x : TabCallReq B1 B2 cT) (Λ Cl El : ℕ) : ℕ :=
  costA x Λ Cl El + 1 + ((2 * PM.budget x.r + 2) + 1 +
    (costB x Λ (costA x Λ Cl El) + 1 + (2 * PolyTab.budget (tabCallTab x) + 2)))

theorem pmap_tape0 : pmap (tPof PM) (tKof PolyTab) (tape0 PM.wf.program) = sPIN (tPof PM) (tKof PolyTab) :=
  Fin.ext (by simp [tape0])

theorem kmap_tape0 : kmap (tPof PM) (tKof PolyTab) (tape0 PolyTab.wf.program) = sO (tPof PM) (tKof PolyTab) :=
  Fin.ext (by simp [tape0])

/-- **RK's run.** -/
theorem tabCall_run (x : TabCallReq B1 B2 cT) (Λ cap Cl El : ℕ) (hA : AHyp x Λ cap Cl El)
    (hB : BCond x Λ cap (costA x Λ Cl El)) (hP : PM.budget x.r ≤ lcap Cl El x.r.c.n x.r.p.k)
    (hK : PolyTab.budget (tabCallTab x) ≤ lcap Cl El x.r.c.n x.r.p.k)
    (hord : PolyTab.order (tabCallTab x) = printerOrder (tabCallTab x).s) :
    ∃ τ, WXExec cap (tabCallProg PolyTab PM Cl El) (startState (NS (tPof PM) (tKof PolyTab)) NR (tabCallInput x)) τ
      (tabCallCost PolyTab PM x Λ Cl El) ∧ τ.st (tabCallOut PolyTab PM) = tabCallOutput PolyTab x ∧ (∀ i, τ.sh i = 0) ∧ ∀ q, τ.val q = 0 := by
  set tP := tPof PM with htP
  set tK := tKof PolyTab with htK
  have htP1 : 1 ≤ tP := by have := PM.wf.program.twoTapes; show 1 ≤ PM.wf.program.tapeCount; omega
  -- stage A
  obtain ⟨σ2, σA, eA, hA2, hD3⟩ := stA_spec tP tK x Λ cap Cl El hA.b1 hA.bits hA.len hA.rd1 hA.hn hA.rd2 hA.rd3
    hA.hcap hA.sm hA.c3a hA.c3c hA.kn
  have hVA : ∀ r, σA.val r ≤ costA x Λ Cl El := fun r => by
    have := WExec.val_le cap eA r
    simpa [startState] using this

  have hstA : ∀ i, i ≠ sLOG tP tK → σA.st i = σ2.st i := fun i h => by rw [hD3.st, Function.update_of_ne h]
  have hpL : ∀ j, pmap tP tK j ≠ sLOG tP tK := fun j e => by
    have := congrArg Fin.val e; simp at this <;> omega
  have hpY : ∀ j, pmap tP tK j ∉ ysL tP tK := fun j hm => by
    simp only [ysL, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> (have := congrArg Fin.val h; simp at this <;> omega)
  have hpA2 : ∀ j : Fin tP, j.val ≠ 0 → pmap tP tK j ∉ [sIN tP tK, sGJ tP tK, Y tP tK 1, Y tP tK 2, Y tP tK 3,
      Y tP tK 4, sPR tP tK, sTMP tP tK, Y tP tK 5, Y tP tK 6, sPIN tP tK] := fun j hj hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h <;>
      (have := congrArg Fin.val h; simp at this <;> omega)
  have hLA2 : sLOG tP tK ∉ [sIN tP tK, sGJ tP tK, Y tP tK 1, Y tP tK 2, Y tP tK 3,
      Y tP tK 4, sPR tP tK, sTMP tP tK, Y tP tK 5, Y tP tK 6, sPIN tP tK] := by lnm
  obtain ⟨σP, eP, hPo, hPh, hPd, hPv⟩ := wfDock_exact PM.wf x.r cap (fun j => pmap tP tK j)
    (pmap tP tK).injective (sLOG tP tK) hpL σA
    (by rw [pmap_tape0 PolyTab PM, hstA _ (by lne)]; exact hA2.pin)
    (fun j hj => by
      rw [hstA _ (hpL j)]
      exact (hA2.other _ (hpA2 j (fun h0 => hj (Fin.ext (by simp [tape0, h0]))))).1)
    (fun j => by
      rw [hD3.sh _ (hpY j)]
      by_cases h0 : j.val = 0
      · have : j = tape0 PM.wf.program := Fin.ext (by simp [tape0, h0])
        rw [this, pmap_tape0 PolyTab PM]; exact hA2.pinh
      · exact (hA2.other _ (hpA2 j h0)).2)
    (lcap Cl El x.r.c.n x.r.p.k) (by rw [hD3.st, Function.update_self])
    (by rw [hD3.sh _ (by simp only [ysL]; lnm)]; exact (hA2.other _ hLA2).2) hP
  have hPB := preB_of tP tK x Cl El PM.wf.program.outputTape htP1 σ2 σA σP hA2 hD3 hPd hPv hPo hPh
  -- stage B
  obtain ⟨σB, eB, hBo, hBh, hBk, hBl, hBv⟩ := stB_spec tP tK x Λ cap (costA x Λ Cl El) Cl El
    PM.wf.program.outputTape σP hPB hB (fun r => by rw [hPv]; exact hVA r)

  have hkL : ∀ j, kmap tP tK j ≠ sLOG tP tK := fun j e => by
    have := congrArg Fin.val e; simp at this <;> omega
  obtain ⟨τ, eK, hKo, hKh, hKd, hKv⟩ := wfDock_exact PolyTab.wf (tabCallTab x) cap (fun j => kmap tP tK j)
    (kmap tP tK).injective (sLOG tP tK) hkL σB
    (by rw [kmap_tape0 PolyTab PM]; exact hBo)
    (fun j hj => by
      refine hBk _ ⟨by simp, by simp⟩ ?_
      intro e
      apply hj
      have := congrArg Fin.val e
      exact Fin.ext (by simp [tape0] at this ⊢; omega))
    (fun j => hBh _) (lcap Cl El x.r.c.n x.r.p.k) hBl (hBh _) hK
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · exact WXExec.seq (WXExec.wm eA) (WXExec.seq eP (WXExec.seq (WXExec.wm eB) eK))
  · show τ.st (kmap tP tK PolyTab.wf.program.outputTape) = _
    rw [hKo, tabCallOutput, hord]
  · intro i
    by_cases hi : ∃ j, kmap tP tK j = i
    · obtain ⟨j, rfl⟩ := hi; exact hKh j
    · push Not at hi
      rw [(hKd i hi).2]; exact hBh i
  · intro q; rw [hKv]; exact hBv q

end Prog

end NearCubicGates.Close.CounterMachine.TabCallProg
