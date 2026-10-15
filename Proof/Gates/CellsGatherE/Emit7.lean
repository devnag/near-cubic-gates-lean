import Proof.Gates.CellsGatherE.Emit6

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

theorem emitP_spec_of (qP : St VV MM) (qCost : Ctx → Call → Params → ℕ → ℕ) (hq : QryGoal qP qCost) :
    GatherPhase.EmitGoal (emitP qP) (emitCost qCost) := by
  intro C cT c p wt i a Big hs hw0 hadm0 hi hct G hb hWd
  obtain ⟨w, hw⟩ := hw0
  obtain ⟨B1, B2, hadm⟩ := hadm0
  obtain ⟨hA, hW1, hW2, hR, hNW, hJn, hEn⟩ := emit_widths C c p wt Big w hs hw hadm hWd
  have hE1 : 1 ≤ p.hE := hE_pos c p hs
  -- 1. the constants
  obtain ⟨a1, n1, x1, hn1, cv1, sm1, fr1, cs1⟩ :=
    cstE_spec C c p a G.cst hE1 G.VW G.KW G.J G.rc G.hE G.kind hW1 hW2
  -- 2. `|reqIds|`
  have a1N : a1.ram sN = CounterMachine.cellN c p wt := by rw [sm1.ram]; exact G.cellN
  have a1NP : a1.env vNP = (p.primes.sort (· ≤ ·)).length := by rw [fr1 vNP (by decide)]; exact G.NP
  have a1IPr : (CounterMachine.cellN c p wt).drop (a1.env vIPr) = p.primes.sort (· ≤ ·) ++
      (CounterMachine.cellN c p wt).drop (a1.env vIPr + (p.primes.sort (· ≤ ·)).length) := by
    rw [fr1 vIPr (by decide)]; exact G.IPr
  have a1J : a1.env gJ = p.J := by rw [fr1 gJ (by decide)]; exact G.J
  have a1rc : a1.env gRC = roleCount c.kind := by rw [fr1 gRC (by decide)]; exact G.rc
  have a1cur : ∀ m, a1.rc m ≤ (a1.ram m).length := by intro m; rw [sm1.rc, sm1.ram]; exact G.rcur m
  have hq2 : ∀ q ∈ p.primes, 2 ≤ q := fun q hq => (primes_prime hs q hq).two_le
  obtain ⟨a2, n2, x2, hn2, r2, kp2, fr2, cs2, rc2⟩ :=
    cnt_spec C c p wt a1 cs1 cv1 a1N a1NP a1IPr a1J a1rc a1cur hq2 hR hNW
  have ram2 : a2.ram = a.ram := kp2.ram.trans sm1.ram
  -- 3. rewind `sG`
  obtain ⟨a3, n3, x3, hn3, ha3⟩ := hs_rwM C sG a2
  subst ha3
  -- 4. the table records
  have g3 : GW (a2.rew sG) (a.ram sG) [] := ⟨by simp [ram2], by simp [DS.rew]⟩
  have hB3 : (a2.rew sG).ram sCT = blk c p wt i := by simp [ram2, G.blk]
  have hR3 : (a2.rew sG).env eR = (blk c p wt i).length := by simp [r2, blk_length]
  have e2 : ∀ x, x ∉ cntT → x ∉ cstT → (a2.rew sG).env x = a.env x := by
    intro x h1 h2; simp only [rew_env]; rw [fr2 x h1, fr1 x h2]
  have hG23 : (a2.rew sG).env eG2 = 2 ^ valueWidth c p * 2 ^ keyW c p := by
    simp only [rew_env]; rw [fr2 eG2 (by decide)]; exact cv1.g2
  have hVW3 : (a2.rew sG).env p2VW = 2 ^ valueWidth c p := by rw [e2 p2VW (by decide) (by decide)]; exact G.VW
  have hKW3 : (a2.rew sG).env p2K = 2 ^ keyW c p := by rw [e2 p2K (by decide) (by decide)]; exact G.KW
  have hrc3 : ∀ m, (a2.rew sG).rc m ≤ ((a2.rew sG).ram m).length := by
    intro m
    by_cases hm : m = sG
    · subst hm; simp [DS.rew]
    · have := rc2 m; simpa [DS.rew, Function.update_of_ne hm] using this
  have hBW : (blk c p wt i).length < 2 ^ C.Wd := by rw [blk_length]; exact hR
  obtain ⟨a4, n4, x4, hn4, g4, ke4, rc4, rcCT4, fr4, cs4⟩ :=
    tab_spec C c p (a2.rew sG) (a.ram sG) [] (blk c p wt i) ⟨cs2.z, cs2.one, cs2.two⟩ g3 hB3 hR3 hG23 hVW3 hKW3 hrc3
      hBW hA

  have envA : ∀ x, ¬ gScratch x → a4.env x = a.env x := by
    intro x hx
    rw [fr4 x (not_mem_of_gs gs_tabT hx)]
    exact e2 x (not_mem_of_gs gs_cntT hx) (not_mem_of_gs gs_cstT hx)
  have ramA : ∀ m, m ≠ sG → a4.ram m = a.ram m := fun m hm => by rw [ke4.ram m hm]; simp [ram2]
  have rcA : ∀ m, a4.rc m ≤ (a4.ram m).length := by
    intro m
    by_cases hm : m = sG
    · subst hm; exact g4.len_le
    by_cases hm2 : m = sCT
    · subst hm2; rw [ramA sCT (by decide), ← G.blk] at *; exact rcCT4
    · rw [rc4 m hm hm2, ke4.ram m hm]; exact hrc3 m
  have qpre : QPre c p wt i a a4 :=
    ⟨G, envA, ramA, rcA, ke4.ip.trans (kp2.ip.trans sm1.ip), ke4.out.trans (kp2.out.trans sm1.out),
      ke4.kin.trans (kp2.kin.trans sm1.kin), ke4.kout.trans (kp2.kout.trans sm1.kout),
      ke4.kc.trans (kp2.kc.trans sm1.kc), by rw [fr4 eG2 (by decide)]; exact hG23⟩
  obtain ⟨a5, n5, x5, hn5, g5, ram5, rc5, ip5, out5, kin5, kout5, kc5, env5⟩ :=
    hq C c p wt i a a4 Big (a.ram sG) ((blk c p wt i).map (GatherPhase.tabRec c p)) hs ⟨w, hw⟩ ⟨B1, B2, hadm⟩ hi hct hb hWd
      qpre (by simpa using g4)
  -- 6. the padding records
  have nq : ∀ x, ¬ gScratch x → ¬ qScratch x := fun x hx h => hx (qScratch_gScratch x h)
  have hc5 : Cst a5 := ⟨by rw [env5 vZ (by unfold qScratch; decide)]; exact cs4.z,
    by rw [env5 v1 (by unfold qScratch; decide)]; exact cs4.one, by rw [env5 v2 (by unfold qScratch; decide)]; exact cs4.two⟩
  have hL5 : a5.env vNL = (CounterMachine.cellN c p wt).length := by
    rw [env5 vNL (by unfold qScratch; decide), envA vNL (by unfold gScratch; decide)]; exact G.NL
  have hG25 : a5.env eG2 = 2 ^ valueWidth c p * 2 ^ keyW c p := by
    rw [env5 eG2 (not_qScratch_W eG2 (by decide))]; exact qpre.g2
  have hKW5 : a5.env p2K = 2 ^ keyW c p := by
    rw [env5 p2K (by unfold qScratch; decide), envA p2K (by unfold gScratch; decide)]; exact G.KW
  obtain ⟨a6, n6, x6, hn6, g6, ke6, rc6, fr6, cs6⟩ :=
    pad_spec C c p a5 (a.ram sG) ((blk c p wt i).map (GatherPhase.tabRec c p) ++ qRecs c p wt i)
      (CounterMachine.cellN c p wt).length hc5 g5 hL5 hG25 hKW5 hNW hA
  -- 7. the conclusion
  have ramF : ∀ m, m ≠ sG → a6.ram m = a.ram m := fun m hm => by rw [ke6.ram m hm, ram5 m hm, ramA m hm]
  have hgw : (a.ram sG).length ≤ gWork c p wt (cellOf wt.I i) := G.gLen
  refine ⟨a6, n1 + (n2 + (n3 + (n4 + (n5 + n6 + 1) + 1) + 1) + 1) + 1,
    Ex.seq x1 (Ex.seq x2 (Ex.seq x3 (Ex.seq x4 (Ex.seq x5 x6)))) |> fun h => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simpa [emitP] using h
  · -- the cost
    have hP : (p.primes.sort (· ≤ ·)).length ≤ (CounterMachine.cellN c p wt).length := by
      have h := congrArg List.length G.IPr
      simp only [List.length_drop, List.length_append] at h
      omega
    have hN := cellN_len c p wt hadm hs w hw
    have hd : CounterMachine.CellTablesProg.dOf c p ≤ 2 * c.n + 4 := by
      rw [dOf_eq]
      have hrc : roleCount c.kind ≤ 2 := by cases c.kind <;> decide
      have : roleCount c.kind * p.J ≤ 2 * (c.n + 1) := Nat.mul_le_mul hrc hJn
      omega
    have hRv : (rowVals c p wt (cellOf wt.I i)).length ≤ 2 * (wWin p ^ nDig c p * c.n ^ 3) :=
      SystemsPhase.rowVals_len c p wt (cellOf wt.I i) hs
    have hS : a2.rc sG ≤ (reqIds c p).length + (rowVals c p wt (cellOf wt.I i)).length +
        (CounterMachine.cellN c p wt).length := by
      have := rc2 sG; rw [ram2] at this; unfold gWork at hgw; omega
    have hc := cost_arith (reqIds c p).length (CounterMachine.cellN c p wt).length (p.primes.sort (· ≤ ·)).length
      (wWin p ^ nDig c p) (rowVals c p wt (cellOf wt.I i)).length c.n (CounterMachine.CellTablesProg.dOf c p) (qCost C c p Big)
      (a2.rc sG) hP hN hd hRv hS
    rw [blk_length] at hn4
    unfold emitCost
    refine le_trans ?_ hc
    omega
  · -- `sG = emitL`
    have hl : (a.ram sG).length ≤ ((blk c p wt i).map (GatherPhase.tabRec c p) ++ qRecs c p wt i ++
        List.replicate (CounterMachine.cellN c p wt).length (GatherPhase.padRec c p)).length := by
      simp only [qRecs, List.length_append, List.length_map, List.length_zipIdx, List.length_replicate, blk_length,
        rowKeys_len]
      unfold gWork at hgw; omega
    rw [GW.final g6 hl]
    rfl
  · rw [ramF sB (by decide)]; exact G.bLen
  · intro m hm _; exact ramF m hm
  · intro m
    by_cases hm : m = sG
    · subst hm; exact g6.len_le
    · rw [rc6 m hm, ke6.ram m hm]; exact rc5 m
  · exact ke6.ip.trans (ip5.trans qpre.ip)
  · exact ke6.out.trans (out5.trans qpre.out)
  · exact ke6.kin.trans (kin5.trans qpre.kin)
  · exact ke6.kout.trans (kout5.trans qpre.kout)
  · exact ke6.kc.trans (kc5.trans qpre.kc)
  · intro x hx
    rw [fr6 x (not_mem_of_gs gs_padT hx), env5 x (nq x hx), envA x hx]

end NearCubicGates.Close.Cells.RecordEmission
