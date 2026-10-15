import Proof.Gates.CounterMachine.TabCallMain

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter

variable (tP tK : ℕ) {B1 B2 cT : ℕ}

/-- The streams RK's teardown rewinds. -/
def tdS : List (Fin (NS tP tK + 1)) := [sIN tP tK, sGJ tP tK, sPR tP tK, sTMP tP tK]

def isK (i : Fin (NS tP tK + 1)) : Prop := 16 + tP ≤ i.val ∧ i.val < 16 + tP + tK

/-- The state at the start of stage B. -/
structure PB (x : TabCallReq B1 B2 cT) (Cl El : ℕ) (o : Fin tP) (σ : WState (NS tP tK) NR) : Prop where
  y0 : σ.st (Y tP tK 0) = []
  yc1 : σ.st (Y tP tK 1) = encN (W0 x.r.c x.r.wt x.r.p.J)
  yc2 : σ.st (Y tP tK 2) = encN (x.r.c.first.coeffs.flatMap intN)
  yc3 : σ.st (Y tP tK 3) = encN (W1 x.r.c x.r.wt x.r.p.J)
  yc4 : σ.st (Y tP tK 4) = encN (x.r.c.second.coeffs.flatMap intN)
  yc5 : σ.st (Y tP tK 5) = encN (x.r.p.factors ++ [x.r.p.M1, x.r.p.A])
  yc6 : σ.st (Y tP tK 6) = encN (dRho x.id)
  inh : σ.sh (sIN tP tK) = 2 * (tabCallInput x).length
  gjh : σ.sh (sGJ tP tK) ≤ 2 * (tabCallInput x).length
  prh : σ.sh (sPR tP tK) ≤ 2 * (tabCallInput x).length
  tmph : σ.sh (sTMP tP tK) ≤ 2 * (tabCallInput x).length
  pfx : σ.st (sPFX tP tK) = []
  oe : σ.st (sO tP tK) = []
  kother : ∀ i, isK tP tK i → i ≠ sO tP tK → σ.st i = []
  log : σ.st (sLOG tP tK) = List.replicate (lcap Cl El x.r.c.n x.r.p.k) false
  pout : σ.st (pmap tP tK o) = prefixesWord x.r
  hz : ∀ i, i ∉ tdS tP tK → σ.sh i = 0
  x0 : σ.val (X 0) = if x.r.c.kind = .pair then 1 else 0
  x1 : σ.val (X 1) = x.r.p.J
  x5 : σ.val (X 5) = qOf x.id - 1
  xb : ∀ d ∈ bndRegs, σ.val d = 2 * (tabCallInput x).length
  x8 : σ.val (X 8) = x.r.p.e
  x10 : dTag x.id ≠ 0 → σ.val (X 10) = dF2 x.id
  x11 : σ.val (X 11) = ((if x.r.c.kind = .pair then 1 else 0) + 1) * (x.r.p.J + 1)
  x14 : σ.val (X 14) = x.r.c.first.gates.length
  x18 : σ.val (X 18) = x.r.c.second.gates.length
  x19 : σ.val (X 19) = x.r.c.first.gates.length
  x22 : σ.val (X 22) = 2 * x.r.p.k
  t0 : σ.val (Td 0) = dTag x.id
  t1 : σ.val (Td 1) = dF1 x.id
  e19 : σ.val (E 19) = 2 * (tabCallInput x).length
  e21 : σ.val (E 21) = pidx (dTag x.id) (dF1 x.id) (kindTag x.r.c.kind)
  zero : ∀ r, r ∉ [X 0, X 1, X 5, X 6, X 7, X 8, X 10, X 11, X 14, X 16, X 17, X 18, X 19, X 20, X 21, X 22,
    E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1, Td 2, Q 15, Gl 4] → σ.val r = 0
  x10z : dTag x.id = 0 → σ.val (X 10) = 0

theorem kNotA2 (i : Fin (NS tP tK + 1)) (htP : 1 ≤ tP) (h1 : 16 + tP ≤ i.val) :
    i ∉ [sIN tP tK, sGJ tP tK, Y tP tK 1, Y tP tK 2, Y tP tK 3, Y tP tK 4, sPR tP tK, sTMP tP tK, Y tP tK 5,
      Y tP tK 6, sPIN tP tK] := by
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h <;>
    (have := congrArg Fin.val h; simp only [sIN_val, sGJ_val, Y_val, sPR_val, sTMP_val, sPIN_val] at this; omega)

theorem nP (i : Fin (NS tP tK + 1)) (hi : i.val < 16 ∨ 16 + tP ≤ i.val) : ∀ j, pmap tP tK j ≠ i := by
  intro j e; have := congrArg Fin.val e; simp at this; have := j.isLt; omega

theorem qjReg_cases (t : ℕ) : (t = 0 ∧ qjReg t = X 5) ∨ (t ≠ 0 ∧ qjReg t = X 10) := by
  unfold qjReg; by_cases h : t = 0 <;> simp [h]

theorem preB_of (x : TabCallReq B1 B2 cT) (Cl El : ℕ) (o : Fin tP) (htP : 1 ≤ tP) (σ2 σA σ : WState (NS tP tK) NR)
    (hA : A2 tP tK x σ2) (hD : D3 tP tK x Cl El σ2 σA)
    (hdock : ∀ i, (∀ j, pmap tP tK j ≠ i) → σ.st i = σA.st i ∧ σ.sh i = σA.sh i) (hdv : σ.val = σA.val)
    (hpo : σ.st (pmap tP tK o) = prefixesWord x.r) (hph : ∀ j, σ.sh (pmap tP tK j) = 0) :
    PB tP tK x Cl El o σ := by
  have hb := streams_le x
  simp only [allN] at hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hb
  have hle := len_eq x
  have hstA : ∀ i, i ≠ sLOG tP tK → σA.st i = σ2.st i := fun i h => by rw [hD.st, Function.update_of_ne h]
  have st : ∀ i, (i.val < 16 ∨ 16 + tP ≤ i.val) → i ≠ sLOG tP tK → σ.st i = σ2.st i := fun i h1 h2 => by
    rw [(hdock i (nP tP tK i h1)).1, hstA i h2]
  have sh : ∀ i, (i.val < 16 ∨ 16 + tP ≤ i.val) → i ∉ ysL tP tK → σ.sh i = σ2.sh i := fun i h1 h2 => by
    rw [(hdock i (nP tP tK i h1)).2, hD.sh i h2]
  have vA : ∀ r, r ∉ [X 11, X 19, X 22, qjReg (dTag x.id), X 6, X 7, X 16, X 17, X 20, X 21, Gl 4] →
      σ.val r = σ2.val r := fun r h => by rw [hdv, hD.vo r h]
  have hq := qjReg_cases (dTag x.id)
  have nqL : ∀ r, r ∉ [X 11, X 19, X 22, X 5, X 10, X 6, X 7, X 16, X 17, X 20, X 21, Gl 4] →
      r ∉ [X 11, X 19, X 22, qjReg (dTag x.id), X 6, X 7, X 16, X 17, X 20, X 21, Gl 4] := fun r h hm => by
    apply h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hq with ⟨_, hq'⟩ | ⟨_, hq'⟩ <;> rw [hq'] at hm <;> tauto
  have hPIN : sPIN tP tK = pmap tP tK ⟨0, htP⟩ := Fin.ext rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [st _ (by simp) (by lne)]; exact (hA.other _ (by lnm)).1
  · rw [st _ (by simp) (by lne)]; exact hA.y1
  · rw [st _ (by simp) (by lne)]; exact hA.y2
  · rw [st _ (by simp) (by lne)]; exact hA.y3
  · rw [st _ (by simp) (by lne)]; exact hA.y4
  · rw [st _ (by simp) (by lne)]; exact hA.y5
  · rw [st _ (by simp) (by lne)]; exact hA.y6
  · rw [sh _ (by simp) (by simp only [ysL]; lnm), hA.nat.2, List.take_of_length_le le_rfl, hle]
  · rw [sh _ (by simp) (by simp only [ysL]; lnm), hA.gjh, hA.gj, List.length_append]; omega
  · rw [sh _ (by simp) (by simp only [ysL]; lnm), hA.prh, hA.pr]
    have := primes_le_all x; simp only [allN] at this; omega
  · rw [sh _ (by simp) (by simp only [ysL]; lnm), hA.tmph]; have := M1_le_all x; simp only [allN] at this; omega
  · rw [st _ (by simp) (by lne)]; exact (hA.other _ (by lnm)).1
  · rw [st _ (by simp) (by lne)]; exact (hA.other _ (kNotA2 tP tK _ htP (by simp))).1
  · intro i hi hio
    obtain ⟨h1, h2⟩ := hi
    rw [st _ (by omega) (by intro e; have := congrArg Fin.val e; simp at this; omega)]
    exact (hA.other _ (kNotA2 tP tK i htP h1)).1
  · rw [(hdock _ (nP tP tK _ (by simp))).1, hD.st, Function.update_self]
  · exact hpo
  · intro i hi
    by_cases hp : ∃ j, pmap tP tK j = i
    · obtain ⟨j, rfl⟩ := hp; exact hph j
    · push Not at hp
      rw [(hdock i hp).2]
      by_cases hy : i ∈ ysL tP tK
      · exact hD.shY i hy
      · rw [hD.sh i hy]
        refine (hA.other i ?_).2
        simp only [tdS, List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp only [ysL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hi.1, hi.2.1, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hi.2.2.1, hi.2.2.2, hy.2.2.2.2.1, hy.2.2.2.2.2,
          by rw [hPIN]; exact (hp _).symm⟩
  · rw [vA _ (by lnm)]; exact hA.flag
  · rw [vA _ (by lnm)]; exact hA.vJ
  · rcases hq with ⟨h0, h5⟩ | ⟨h0, h10⟩
    · rw [hdv, ← h5, hD.vq]; simp [qjVal, qOf, h0]
    · rw [vA _ (by rw [h10]; lnm), hA.regs _ (by lnm)]; simp [qOf, h0]
  · intro d hd; rw [hdv]; exact hD.vb d hd
  · rw [vA _ (by lnm)]; exact hA.vE
  · intro h0
    rcases hq with ⟨h0', _⟩ | ⟨_, h10⟩
    · exact absurd h0' h0
    · rw [hdv, ← h10, hD.vq]; simp [qjVal, h0]
  · rw [hdv]; exact hD.v11
  · rw [vA _ (by lnm)]; exact hA.vG0
  · rw [vA _ (by lnm)]; exact hA.vG1
  · rw [hdv]; exact hD.v19
  · rw [hdv]; exact hD.v22
  · rw [vA _ (by lnm)]; exact hA.t0
  · rw [vA _ (by lnm)]; exact hA.t1
  · rw [vA _ (by lnm)]; exact hA.len
  · rw [vA _ (by lnm)]; exact hA.pix
  · intro r hr
    have hs1 : [X 11, X 19, X 22, X 5, X 10, X 6, X 7, X 16, X 17, X 20, X 21, Gl 4] ⊆ [X 0, X 1, X 5, X 6, X 7, X 8,
        X 10, X 11, X 14, X 16, X 17, X 18, X 19, X 20, X 21, X 22, E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1,
        Td 2, Q 15, Gl 4] := by decide
    have hs2 : [X 0, X 1, X 8, X 14, X 18, E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1, Td 2, Q 15] ⊆ [X 0, X 1,
        X 5, X 6, X 7, X 8, X 10, X 11, X 14, X 16, X 17, X 18, X 19, X 20, X 21, X 22, E 0, E 1, E 2, E 3, E 4, E 19,
        E 21, Td 0, Td 1, Td 2, Q 15, Gl 4] := by decide
    rw [vA r (nqL r (fun hm => hr (hs1 hm)))]
    exact hA.regs r (fun hm => hr (hs2 hm))
  · intro h0
    rcases hq with ⟨_, h5⟩ | ⟨h0', _⟩
    · rw [vA _ (by rw [h5]; lnm), hA.regs _ (by lnm)]
    · exact absurd h0 h0'

/-- Prefix selection's scratch registers `E 10 … E 13`. -/
def Usel : Fin 4 ↪ Fin NR := off 74 (by simp only [NR]; omega)

/-- Every register. -/
def allR : List (Fin NR) := List.finRange NR

/-- Stage B: select the prefix, print the formula and the request word, tear down. -/
def stB (o : Fin tP) : WM (NS tP tK) NR :=
  .seq (selPfx (pmap tP tK o) (sPFX tP tK) (E 21) Usel)
    (.seq (.seq (formulaTop tP tK) (formulaOut (Y tP tK 0) (sO tP tK) (sPFX tP tK) F))
      (.seq (rwL (E 19) (E 22) (E 20) (tdS tP tK)) (clrL allR)))

/-- Stage B's cost. -/
def costB (x : TabCallReq B1 B2 cT) (Λ V0 : ℕ) : ℕ :=
  100 * ((prefixesWord x.r).length + 1) + 1 +
    ((300000 * (Λ + 1) ^ 5 + 20 + 1 + 5000 * ((pfxOf x).length + ((formulaToks x).flatMap tokWord).length +
      (formulaToks x).length + 1) ^ 2) + 1 + (4 * (30 * (2 * (tabCallInput x).length) + 10) + 1 + 88 * (3 * V0 + 2)))

/-- The numeric side conditions of stage B. -/
structure BCond (x : TabCallReq B1 B2 cT) (Λ cap V0 : ℕ) : Prop where
  fb : FBound (fdataOf x) Λ
  len : 2 * (tabCallInput x).length ≤ Λ
  bin : ∀ j < x.r.p.e, binom x.r.p.e j * (x.r.p.e + j) ≤ Λ
  e2 : 2 * x.r.p.e ≤ Λ
  g2 : 2 * (x.r.c.first.gates.length + x.r.c.second.gates.length) ≤ Λ
  c1 : (prefixesWord x.r).length + 10 ≤ cap
  c2 : 2 * ((formulaToks x).flatMap tokWord).length + 8 * Λ + 100 ≤ cap
  c3 : (formulaToks x).length + 4 * Λ + 2 ≤ cap
  c4 : 20 * ((pfxOf x).length + ((formulaToks x).flatMap tokWord).length + (formulaToks x).length + 1) ≤ cap
  c5 : 2 * (tabCallInput x).length + V0 + 3 ≤ cap

theorem notTd (i : Fin (NS tP tK + 1)) (h : i.val ≠ 0 ∧ i.val ≠ 9 ∧ i.val ≠ 10 ∧ i.val ≠ 11) : i ∉ tdS tP tK := by
  intro hm; simp only [tdS, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> simp at h

theorem pmap_not_td (o : Fin tP) : pmap tP tK o ∉ tdS tP tK := by
  intro hm; simp only [tdS, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h <;> (have := congrArg Fin.val h; simp at this <;> omega)

/-- RG's preconditions at the start of stage B (after the prefix selection). -/
theorem formulaPre_of (x : TabCallReq B1 B2 cT) (Λ cap V0 Cl El : ℕ) (o : Fin tP) (σ σ1 : WState (NS tP tK) NR)
    (hPB : PB tP tK x Cl El o σ) (hC : BCond x Λ cap V0) (hst : ∀ i, i ≠ sPFX tP tK → σ1.st i = σ.st i)
    (hsh : σ1.sh = σ.sh) (hv : ∀ r, r ≠ E 21 → σ1.val r = σ.val r) : FormulaPre tP tK x Λ cap σ1 := by
  have z : ∀ r, r ∉ [X 0, X 1, X 5, X 6, X 7, X 8, X 10, X 11, X 14, X 16, X 17, X 18, X 19, X 20, X 21, X 22,
      E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1, Td 2, Q 15, Gl 4] → σ1.val r = 0 := fun r h => by
    rw [hv r (fun e => h (by rw [e]; simp))]; exact hPB.zero r h
  have hF : ∀ i, σ1.val (F i) = 0 := fun i => z _ (by apply fin_nmem; simp; omega)
  have hb' : ∀ d ∈ bndRegs, σ1.val d = 2 * (tabCallInput x).length := fun d hd => by
    rw [hv d (by simp only [bndRegs, List.mem_cons, List.not_mem_nil, or_false] at hd
                 rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> lne)]
    exact hPB.xb d hd
  have hs := fstate_of tP tK x σ1 (by rw [hst _ (by lne)]; exact hPB.y0)
    (by rw [hsh]; exact hPB.hz _ (by simp only [tdS]; lnm)) hF
    (by rw [hst _ (by lne)]; exact hPB.yc1) (by rw [hst _ (by lne)]; exact hPB.yc2)
    (by rw [hst _ (by lne)]; exact hPB.yc3) (by rw [hst _ (by lne)]; exact hPB.yc4)
    (by rw [hst _ (by lne)]; exact hPB.yc5) (by rw [hst _ (by lne)]; exact hPB.yc6)
    (fun i hi => by
      rw [hsh]; exact hPB.hz _ (by
        intro hm; simp only [tdS, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h | h | h <;> (have := congrArg Fin.val h; simp at this <;> omega)))
    (by rw [hv _ (by lne)]; exact hPB.x0) (by rw [hv _ (by lne)]; exact hPB.x1) (by rw [hv _ (by lne)]; exact hPB.x5)
    hb' (by rw [hv _ (by lne)]; exact hPB.x8) (by rw [hv _ (by lne)]; exact hPB.x11)
    (by rw [hv _ (by lne)]; exact hPB.x14) (z _ (by lnm)) (by rw [hv _ (by lne)]; exact hPB.x18)
    (by rw [hv _ (by lne)]; exact hPB.x19) (by rw [hv _ (by lne)]; exact hPB.x22)
    (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact z _ (by lnm))
  have h7 : σ1.val (F 7) = 0 := hF 7
  have h16 : σ1.val (F 16) = 0 := hF 16
  refine ⟨hs, hC.fb, ?_, ?_, hC.bin, hC.e2, hC.g2, by rw [hv _ (by lne)]; exact hPB.t0,
    by rw [hv _ (by lne)]; exact hPB.t1, fun h1 => by rw [hv _ (by lne)]; exact hPB.x10 (by omega),
    by have := hC.c5; omega, ⟨by rw [h7]; have := hC.c2; omega, by rw [h16]; have := hC.c3; omega⟩⟩
  · intro i hi
    have hbi : X i ∈ bndRegs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bndRegs]
    rw [hb' _ hbi]; exact hC.len
  · intro h0 i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact z _ (by lnm)
    · rw [hv _ (by lne)]; exact hPB.x10z h0
    · exact z _ (by lnm)
    · exact z _ (by lnm)
    · exact z _ (by lnm)

/-- **Stage B.** -/
theorem stB_spec (x : TabCallReq B1 B2 cT) (Λ cap V0 Cl El : ℕ) (o : Fin tP) (σ : WState (NS tP tK) NR)
    (hPB : PB tP tK x Cl El o σ) (hC : BCond x Λ cap V0) (hV : ∀ r, σ.val r ≤ V0) :
    ∃ τ, WExec cap (stB tP tK o) σ τ (costB x Λ V0) ∧ τ.st (sO tP tK) = RepairOrdinary.frame (tabWord (tabCallTab x)) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ i, isK tP tK i → i ≠ sO tP tK → τ.st i = []) ∧
      τ.st (sLOG tP tK) = List.replicate (lcap Cl El x.r.c.n x.r.p.k) false ∧ (∀ r, τ.val r = 0) := by
  obtain ⟨hlt, hws⟩ := prefix_sel x
  have hU : ∀ j, Usel j ≠ E 21 := fun j => by intro e; have := congrArg Fin.val e; simp [Usel] at this; omega
  have hU0 : ∀ j, σ.val (Usel j) = 0 := fun j => hPB.zero _ (by
    apply fin_nmem; simp [Usel]; refine ⟨?_, ?_⟩ <;> omega)
  have e1 := selPfx_spec cap (pmap tP tK o) (sPFX tP tK) (E 21) Usel σ (wsOf x.r) [] _ (by lne) hU
    (by rw [hPB.pout, prefixesWord_eq, List.append_nil]) (hPB.hz _ (pmap_not_td tP tK o)) hlt hPB.pfx
    (hPB.hz _ (by simp only [tdS]; lnm)) hPB.e21 hU0 (by rw [← prefixesWord_eq]; exact hC.c1)
  rw [hws] at e1
  set σ1 := (σ.sets (sPFX tP tK) (RepairOrdinary.frame (pfxOf x))).setv (E 21) 0 with hσ1
  have st1 : ∀ i, i ≠ sPFX tP tK → σ1.st i = σ.st i := fun i h => by simp [hσ1, Function.update_of_ne h]
  have sh1 : σ1.sh = σ.sh := by simp [hσ1]
  have v1 : ∀ r, r ≠ E 21 → σ1.val r = σ.val r := fun r h => by simp [hσ1, Function.update_of_ne h]
  have hpre := formulaPre_of tP tK x Λ cap V0 Cl El o σ σ1 hPB hC st1 sh1 v1
  have eP := formulaTop_spec tP tK x Λ cap σ1 hpre
  obtain ⟨τ3, e3, o3, oh3, _, sh3, pfh3, os3, ov3, _⟩ := formulaReq_spec cap (Y tP tK 0) (sO tP tK) (sPFX tP tK) F
    (by lne) (by lne) (by lne) (formulaTop tP tK) (formulaToks x) _ σ1 hpre.hs.rest eP (by rw [st1 _ (by lne)]; exact hPB.y0)
    (by rw [sh1]; exact hPB.hz _ (notTd tP tK _ (by simp))) (by rw [v1 _ (by lne)]; exact hPB.zero _ (by lnm))
    (by rw [v1 _ (by lne)]; exact hPB.zero _ (by lnm))
    (pfxOf x) [] (by simp [hσ1]) (by rw [sh1]; exact hPB.hz _ (notTd tP tK _ (by simp)))
    (by rw [st1 _ (by lne)]; exact hPB.oe) (by rw [sh1]; exact hPB.hz _ (notTd tP tK _ (by simp; omega))) hC.c4
  have hz1 : ∀ i, i ∉ tdS tP tK → σ1.sh i = 0 := fun i h => by rw [sh1]; exact hPB.hz i h
  have v3 : ∀ r, τ3.val r = σ1.val r := ov3
  have hE22 : τ3.val (E 22) = 0 := by rw [v3, v1 _ (by lne)]; exact hPB.zero _ (by lnm)
  have hE20 : τ3.val (E 20) = 0 := by rw [v3, v1 _ (by lne)]; exact hPB.zero _ (by lnm)
  have hE19 : τ3.val (E 19) = 2 * (tabCallInput x).length := by rw [v3, v1 _ (by lne)]; exact hPB.e19
  have sh3' : ∀ X, X ≠ sO tP tK → X ≠ Y tP tK 0 → X ≠ sPFX tP tK → τ3.st X = σ.st X ∧ τ3.sh X = σ.sh X :=
    fun X a b c => by rw [(os3 X a b).1, (os3 X a b).2, st1 X c, sh1]; exact ⟨rfl, rfl⟩
  obtain ⟨τ4, e4, h4a, h4b, h4c, h4d⟩ := rwL_spec cap (E 19) (E 22) (E 20) (by lne) (by lne) (by lne) (tdS tP tK) τ3
    hE22 hE20 (fun y hy => by
      rw [hE19]
      simp only [tdS, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · rw [(sh3' _ (by lne) (by lne) (by lne)).2, hPB.inh]
      · rw [(sh3' _ (by lne) (by lne) (by lne)).2]; exact hPB.gjh
      · rw [(sh3' _ (by lne) (by lne) (by lne)).2]; exact hPB.prh
      · rw [(sh3' _ (by lne) (by lne) (by lne)).2]; exact hPB.tmph) (by rw [hE19]; have := hC.c5; omega)
  rw [hE19] at e4
  have hV4 : ∀ r ∈ allR, τ4.val r ≤ V0 := fun r _ => by
    rw [h4d, v3]
    by_cases hr : r = E 21
    · subst hr; simp [hσ1]
    · rw [v1 r hr]; exact hV r
  obtain ⟨τ5, e5, h5a, h5b, h5c, h5d⟩ := clrL_spec cap V0 (by have := hC.c5; omega) allR τ4 hV4
  refine ⟨τ5, WExec.mono (WExec.seq e1 (WExec.seq e3 (WExec.seq e4 e5))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold costB; simp only [tdS, allR, List.length_cons, List.length_nil, List.length_finRange]
    rw [← prefixesWord_eq]
    try omega
  · rw [h5a, h4c, o3, tabWord_tabCallTab]
    try simp [List.append_assoc]
  · intro i
    rw [h5b]
    by_cases ht : i ∈ tdS tP tK
    · exact h4a i ht
    · rw [h4b i ht]
      by_cases hO : i = sO tP tK
      · rw [hO]; exact oh3
      · by_cases hS : i = Y tP tK 0
        · rw [hS]; exact sh3
        · by_cases hP : i = sPFX tP tK
          · rw [hP]; exact pfh3
          · rw [(sh3' i hO hS hP).2]; exact hPB.hz i ht
  · intro i hi hio
    rw [h5a, h4c, (sh3' i hio (by intro e; rw [e] at hi; simp [isK] at hi; omega)
      (by intro e; rw [e] at hi; simp [isK] at hi; omega)).1]
    exact hPB.kother i hi hio
  · rw [h5a, h4c, (sh3' _ (by lne) (by lne) (by lne)).1]; exact hPB.log
  · intro r; exact h5c r (by simp [allR])

end NearCubicGates.Close.CounterMachine.TabCallProg
