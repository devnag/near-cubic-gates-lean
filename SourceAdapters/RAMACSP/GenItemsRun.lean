import SourceAdapters.RAMACSP.GenItemsGlue

/-!
# The machine-items printer as one cell program with one callee

Paper: `lem:generator`. The program emits the machine items in catalog
order, each normalized guard followed by the corresponding equation tokens.

The program `itemsMainP V body` of L's cell language:
`preP; stageRI; callIrr; lenP; callCoord; readVar 38 vD; setupP; comp body; emit 0`.
Its callee is `sumWF` of Shoup's machine (tag `1`) and of the pair (coordinate machine, tag `0 1`; an empty request
type, tag `0 0`). `items_run`: under the size conditions `IFits`, if the printing program `body` prints the numbers
`machineNums V irrPoly r` from every state of the item printer (`Base`, `CoordV`) within the room `Room`, the run
prints exactly `frame (machineItemsWord V irrPoly r)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMACSP.Gen
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicGates.Adapters.Machine.ComposeCarry
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

/-! ## The callee -/

section Callee

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)

/-- The coordinate request word. -/
abbrev coordIn (r : ClockRequest) : List Bool := Joins.coordInput (coordRequest V irrPoly r)

/-- The coordinate word. -/
abbrev coordOut (r : ClockRequest) : List Bool := Joins.coordWord (coordRequest V irrPoly r) (coordRequest_ok V irrPoly hI r)

/-- The coordinate machine on clock requests (`GenCoordDock.coordWF`). -/
def CoordRWF (K e : ℕ) : Type :=
  WordFunction ClockRequest (coordIn V irrPoly) (coordOut V irrPoly hI) (fun r => K * ((coordIn V irrPoly r).length + 1) ^ e)

/-- A word function on the empty request type. -/
def emptyWF {R : Type} {i o : R → List Bool} {b : R → ℕ} (W : WordFunction R i o b) :
    WordFunction Empty (fun e => e.elim) (fun e => e.elim) (fun _ => 0) := ⟨W.program, fun e => e.elim⟩

/-- The callee's input words. -/
abbrev iIn : {f : ℕ // 1 ≤ f} ⊕ (ClockRequest ⊕ Empty) → List Bool :=
  sumInput (fun f => List.replicate f.val true) (sumInput (coordIn V irrPoly) (fun e : Empty => e.elim))

/-- The callee's budget. -/
abbrev iBud (Ks es Kc ec : ℕ) : {f : ℕ // 1 ≤ f} ⊕ (ClockRequest ⊕ Empty) → ℕ :=
  sumBudget (fun f : {f : ℕ // 1 ≤ f} => List.replicate f.val true) (fun f => Ks * (f.val + 1) ^ es)
    (sumInput (coordIn V irrPoly) (fun e : Empty => e.elim))
    (sumBudget (coordIn V irrPoly) (fun r => Kc * ((coordIn V irrPoly r).length + 1) ^ ec) (fun e : Empty => e.elim)
      (fun _ => 0))

/-- **The callee**: Shoup's machine (tag `1`), the coordinate machine (tags `0 1`). -/
def itemsCallee {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordRWF V irrPoly hI Kc ec) : Callee :=
  ⟨{f : ℕ // 1 ≤ f} ⊕ (ClockRequest ⊕ Empty), iIn V irrPoly,
    sumOutput (fun f => Published.Shoup.coeffWord f.val (irrPoly f.val))
      (sumOutput (coordOut V irrPoly hI) (fun e : Empty => e.elim)),
    iBud V irrPoly Ks es Kc ec, sumWF WS (sumWF WC (emptyWF WC))⟩

end Callee

/-! ## The program -/

/-- **The machine-items printer** for the printing program `body`. -/
def itemsMainP (V : Verifier) (body : P) : St VV MM :=
  .seq FL.preP (.seq (compS (stageRI V) 0) (.seq callIrr (.seq (compS lenP 0) (.seq callCoord (.seq (readVar 38 vD)
    (.seq (compS setupP 0) (.seq (compS (comp body) 0) (compS (.emit (.k 0)) 0))))))))

/-! ## The run -/

section Run

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)
  {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordRWF V irrPoly hI Kc ec)

/-- The modulus mask. -/
abbrev irrI (r : ClockRequest) : ℕ := modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2)

/-- The size of the coordinate array, `mH·mH·f`. -/
abbrev cwN (r : ClockRequest) : ℕ := domExp V r.2 * domExp V r.2 * fieldExp V r.2

/-- The size conditions of the run. -/
structure IFits (r : ClockRequest) (C : Ctx) (G : Glob) : Prop where
  pFit : ParamFit V r G
  room : Room V r G
  lkI : fieldExp V r.2 + 1 < C.Lk
  lkCo : 2 * natBitLength (fieldExp V r.2) + 2 * natBitLength (irrI V irrPoly r) + 2 * natBitLength (domExp V r.2) + 6 <
    C.Lk
  bkI : ∀ h : 1 ≤ fieldExp V r.2, iBud V irrPoly Ks es Kc ec (.inl ⟨fieldExp V r.2, h⟩) ≤ C.Bk
  bkCo : iBud V irrPoly Ks es Kc ec (.inr (.inl r)) ≤ C.Bk
  wI : 2 ^ (fieldExp V r.2 + 3) < 2 ^ C.Wd
  wCo : natBitLength (fieldExp V r.2) + natBitLength (irrI V irrPoly r) + natBitLength (domExp V r.2) + 4 < 2 ^ C.Wd
  wD : 2 ^ (cwN V r - 1 + 3) < 2 ^ C.Wd

/-- The cost bound of the run. -/
def iCost (body : P) (C : Ctx) (G : Glob) (inp : List Bool) (r : ClockRequest) : ℕ :=
  preCost inp + costS G (stageRI V) + callIrrCost C (fieldExp V r.2) + costS G lenP +
    callCoordCost C (fieldExp V r.2) (irrI V irrPoly r) (domExp V r.2) + (10 * (cwN V r - 1) + 40) +
    costS G setupP + costS G (comp body) + costS G (.emit (.k 0)) + 8

theorem iCallee_outw_inl (g : {f : ℕ // 1 ≤ f}) :
    (itemsCallee V irrPoly hI WS WC).outw (.inl g) = Published.Shoup.coeffWord g.val (irrPoly g.val) := rfl

theorem iCallee_outw_co (r : ClockRequest) :
    (itemsCallee V irrPoly hI WS WC).outw (.inr (.inl r)) = coordOut V irrPoly hI r := by
  simp only [itemsCallee, sumOutput]

theorem iCallee_inw_co (r : ClockRequest) :
    (itemsCallee V irrPoly hI WS WC).inw (.inr (.inl r)) =
      false :: true :: (natWord (fieldExp V r.2) ++ natWord (irrI V irrPoly r) ++ natWord (domExp V r.2)) := by
  simp only [itemsCallee, iIn, sumInput, coordIn, Joins.coordInput, coordRequest]

theorem fixedWidthNatBits_length' (w v : ℕ) : (WilliamsLoaderForms.fixedWidthNatBits w v).length = w := by
  simp [WilliamsLoaderForms.fixedWidthNatBits]

theorem coordWord_length (p : Joins.CoordReq) (h : Joins.CoordOk p) :
    (Joins.coordWord p h).length = p.m * p.m * p.f := by
  simp only [Joins.coordWord, List.length_flatMap, fixedWidthNatBits_length', List.map_const', List.sum_replicate,
    List.length_finRange, smul_eq_mul]
  ring

theorem coordOut_length (r : ClockRequest) : (coordOut V irrPoly hI r).length = cwN V r :=
  coordWord_length _ _

theorem one_le_cwN (r : ClockRequest) : 1 ≤ cwN V r := by
  have h1 : 1 ≤ domExp V r.2 := by unfold domExp laneExp; omega
  have h2 := one_le_fieldExp V r.2
  have : 1 ≤ domExp V r.2 * domExp V r.2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact le_trans this (Nat.le_mul_of_pos_right _ (by omega))

set_option maxHeartbeats 400000 in
/-- **The printer's run**: on `1^L 0 ++ ClockRequest.word r` (`L ≥ 1`), `itemsMainP V body` prints
`frame (machineItemsWord V irrPoly r)`. -/
theorem items_run (body : P) (hwf : WF baseA body) (hok : Ok 0 body)
    (hden : ∀ (G : Glob) (r : ClockRequest) (s : FS), Room V r G → Base V r s → CoordV V irrPoly hI r s →
      den G s body = machineNums V irrPoly r)
    (hbound : ∀ r x, x ∈ machineNums V irrPoly r → x < 2 ^ (fieldExp V r.2 + 1))
    (a2 c2 a3 c3 : ℕ) (r : ClockRequest) (L : ℕ) (hL : 1 ≤ L)
    (fits : IFits V irrPoly (Ks := Ks) (es := es) (Kc := Kc) (ec := ec) r
      (ctxOf (itemsCallee V irrPoly hI WS WC) (zM a2 c2 a3 c3) (List.replicate L true ++ false :: ClockRequest.word r))
      (globOf (List.replicate L true ++ false :: ClockRequest.word r))) :
    ∃ b n, Ex (ctxOf (itemsCallee V irrPoly hI WS WC) (zM a2 c2 a3 c3)
        (List.replicate L true ++ false :: ClockRequest.word r)) (itemsMainP V body) a0 b n ∧
      b.out = RepairSource.frame (machineItemsWord V irrPoly r) ∧
      n ≤ iCost V irrPoly body
        (ctxOf (itemsCallee V irrPoly hI WS WC) (zM a2 c2 a3 c3) (List.replicate L true ++ false :: ClockRequest.word r))
        (globOf (List.replicate L true ++ false :: ClockRequest.word r))
        (List.replicate L true ++ false :: ClockRequest.word r) r := by
  set inp := List.replicate L true ++ false :: ClockRequest.word r with hinp
  set C := ctxOf (itemsCallee V irrPoly hI WS WC) (zM a2 c2 a3 c3) inp with hC
  set G := globOf inp with hG
  have hlead : leadOnes inp = L := NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_rep _ _
  have h1 : 1 ≤ leadOnes inp := by omega
  have hlt : leadOnes inp < inp.length := by rw [hlead]; simp [hinp]
  have hg : GOk C G := gokM _ a2 c2 a3 c3 inp h1
  have hCinp : C.inp = G.inp := rfl
  have SO := compS_ok hg hCinp
  have hR := fits.room
  have hf1 := one_le_fieldExp V r.2
  have hcapK := cap_add G
  set f := fieldExp V r.2 with hf
  set cw := coordOut V irrPoly hI r with hcw
  set irr := irrI V irrPoly r with hirr
  set nD := cwN V r with hnD
  have hnD1 : 1 ≤ nD := one_le_cwN V r
  have hnDe : nD = domExp V r.2 * domExp V r.2 * fieldExp V r.2 := rfl
  suffices H : Hs C (itemsMainP V body) a0 (iCost V irrPoly body C G inp r)
      (fun b => b.out = RepairSource.frame (machineItemsWord V irrPoly r)) by
    obtain ⟨b, n, hx, hn, hb⟩ := H
    exact ⟨b, n, hx, hb, hn⟩
  unfold itemsMainP
  refine Hs.mono (Hs.seq (t2 := costS G (stageRI V) + (callIrrCost C f + (costS G lenP + (callCoordCost C f irr
      (domExp V r.2) + ((10 * (nD - 1) + 40) + (costS G setupP + (costS G (comp body) + costS G (.emit (.k 0)) + 1) + 1)
      + 1) + 1) + 1) + 1) + 1)
      (preM_ok _ a2 c2 a3 c3 inp hlt) (fun b0 hb0 => ?_)) (by unfold iCost; rw [← hf, ← hirr, ← hnD]; omega)
    (fun _ h => h)
  obtain ⟨hb0, hk0⟩ := hb0
  have r0 : Rel G (FL.s0 inp) b0 := rel_s0 inp h1 b0 hb0
  -- read + params
  have hinA : G.inp.drop (FL.s0 inp).ip = ClockRequest.word r ++ [] := by
    show inp.drop (leadOnes inp + 1) = _
    rw [hlead, hinp, drop_prefix_word, List.append_nil]
  obtain ⟨pvA, outA, badA, flA, fpA⟩ := stageRI_spec V (G := G) (FL.s0 inp) r [] hinA fits.pFit
  generalize hsA : evalS G (stageRI V) (FL.s0 inp) = sA at pvA outA badA flA fpA
  have SA := SO (stageRI V) 0 (FL.s0 inp) b0 (by norm_num) (wf_stageRI V) (by rw [hsA, badA]; rfl) r0
  rw [hsA] at SA
  refine Hs.seq SA (fun b1 sp1 => ?_)
  have hk1 : b1.kin = [] := sp1.fix.2.2.1.trans hk0
  -- the Shoup call
  have hcapf : 2 ^ (f + 1) ≤ G.cap + 1 := by
    rw [hcapK]; exact Nat.pow_le_pow_right (by norm_num) (by have := hR.fK; omega)
  have houtI : C.K.outw (.inl ⟨f, hf1⟩) = Published.Shoup.coeffWord f (irrPoly f) :=
    iCallee_outw_inl V irrPoly hI WS WC ⟨f, hf1⟩
  refine Hs.seq (callIrr_spec C G sA b1 sp1.rel hk1 f pvA.f (.inl ⟨f, hf1⟩) rfl (C.K.outw (.inl ⟨f, hf1⟩)) rfl
    (by rw [houtI, coeffWord_length]) (fits.bkI hf1) fits.lkI fits.wI hcapf) (fun b2 hb2 => ?_)
  obtain ⟨r2, k2⟩ := hb2
  rw [houtI, bitsValue_coeffWord] at r2
  set sA' := sA.setv 37 (modMask (irrPoly f) f) with hsA'
  have pvA' : PV V r sA' := pvA.keep V (fun i h1 h2 => by
    simp only [hsA', FS.setv_env, Function.update_apply]; rw [if_neg (by intro e; subst e; exact absurd h2 (by decide))])
  -- the lengths
  have hirrlt : modMask (irrPoly f) f < 2 ^ (f + 1) := WireExponent3_5.GF.ofPoly_lt _ _
  have hDcap : nD ≤ G.cap := by
    have := hR.dK
    have h2 : nD < 2 ^ nD := Nat.lt_two_pow_self
    have h3 : 2 ^ nD ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨pvH, h37, h41, h42, h43, h38, EH⟩ := lenP_spec V (G := G) sA' r pvA' (modMask (irrPoly f) f)
    (by simp [hsA']) hirrlt hR.fK hR.kn hDcap
  generalize hsH : evalS G lenP sA' = sH at pvH h37 h41 h42 h43 h38 EH
  have hbH : sH.bad = false := by rw [EH.bad]; simp [hsA', badA]; rfl
  have SH := SO lenP 0 sA' b2 (by norm_num) wf_lenP (by rw [hsH]; exact hbH) r2
  rw [hsH] at SH
  refine Hs.seq SH (fun b3 sp3 => ?_)
  have hk3 : b3.kin = [] := sp3.fix.2.2.1.trans k2
  -- the coordinate call
  refine Hs.seq (Hs.mono (callCoord_spec C G sH b3 sp3.rel hk3 f irr (domExp V r.2) pvH.f h37 pvH.mH h41 h42 h43
    (.inr (.inl r)) (iCallee_inw_co V irrPoly hI WS WC r) fits.bkCo fits.lkCo fits.wCo) le_rfl (fun _ h => h))
    (fun b4 hb4 => ?_)
  obtain ⟨r4, e4, o4, c4⟩ := hb4
  have hk4 : b4.kin = [] := by rw [e4]
  have houtC : C.K.outw (.inr (.inl r)) = cw := iCallee_outw_co V irrPoly hI WS WC r
  -- the coordinate array
  have hcwl : cw.length = nD - 1 + 1 := by rw [hcw, coordOut_length]; omega
  have hcapD : 2 ^ (nD - 1 + 1) ≤ G.cap + 1 := by
    rw [hcapK]; exact Nat.pow_le_pow_right (by norm_num) (by have := hR.dK; omega)
  refine Hs.seq (readVar_spec 38 vD C G sH b4 r4 (nD - 1) h38 cw (o4.trans houtC) c4 hcwl fits.wD hcapD)
    (fun b5 hb5 => ?_)
  obtain ⟨r5, k5⟩ := hb5
  set sD := sH.setv vD (CanonicalBinary.bitsValue cw) with hsD
  have pvD : PV V r sD := pvH.keep V (fun i h1 h2 => by
    simp only [hsD, FS.setv_env, Function.update_apply]
    rw [if_neg (by intro e; subst e; exact absurd h2 (by decide))])
  -- the layout masks
  have hcapM : 2 ^ (domExp V r.2 + 8) ≤ G.cap := by have := hR.cap; omega
  obtain ⟨v44, v45, v48, v49, ES⟩ := setupP_spec V (G := G) sD r pvD hcapM
  generalize hsS : evalS G setupP sD = sS at v44 v45 v48 v49 ES
  have hbS : sS.bad = false := by rw [ES.bad]; exact hbH
  have SS := SO setupP 0 sD b5 (by norm_num) wf_setupP (by rw [hsS]; exact hbS) r5
  rw [hsS] at SS
  refine Hs.seq SS (fun b6 sp6 => ?_)
  have hbase : Base V r sS := ⟨pvD.keep V (fun i h1 h2 => ES.env i (by
      simp only [SHW, List.mem_cons, List.not_mem_nil, or_false]
      intro h; rcases h with h | h | h | h <;> (subst h; exact absurd h2 (by decide)))),
    v44, v45, v48, v49⟩
  have hcoord : CoordV V irrPoly hI r sS := by
    show sS.env vD = _
    rw [ES.env vD (by decide)]
    simp only [hsD, FS.setv_env, Function.update_self]
    rfl
  -- the catalog
  have hden' := hden G r sS hR hbase hcoord
  have hbits : ∀ x ∈ den G sS body, natBitLength x + 2 ≤ G.K := by
    intro x hx
    rw [hden'] at hx
    have := natBitLength_le_of_lt (v := x) (L := f + 1) (by omega) (hbound r x hx)
    have := hR.fK; omega
  have O := comp_spec hR.kn body baseA sS baseA_ge hwf hbits
  rw [hden'] at O
  have SB := SO (comp body) 0 sS b6 (by norm_num) (wfS_comp 0 body hok) (by rw [O.bad]; exact hbS) sp6.rel
  refine Hs.seq SB (fun b7 sp7 => ?_)
  generalize hsB : evalS G (comp body) sS = sB at O sp7
  have SE := SO (.emit (.k 0)) 0 sB b7 (by norm_num) (by decide) (by show sB.bad = false; rw [O.bad]; exact hbS)
    sp7.rel
  refine Hs.mono SE le_rfl (fun b8 sp8 => ?_)
  refine sp8.rel.out.trans ?_
  have e1 : (evalS G (.emit (.k 0)) sB).out = sB.out ++ [false] := by
    show sB.out ++ [evalE G sB (.k 0) != 0] = _
    simp only [show evalE G sB (.k 0) = 0 from Nat.zero_min _]; rfl
  have e3 : sD.out = sH.out := rfl
  have e4 : sA'.out = sA.out := rfl
  have e5 : (FL.s0 inp).out = [] := rfl
  rw [e1, O.out, ES.out, e3, EH.out, e4, outA, e5, machineItemsWord_eq V irrPoly r]
  simp only [frame_dbl, dbl, List.flatMap_nil, List.nil_append, List.append_nil]

end Run

end NearCubicGates.Adapters.RAMACSP.Gen.Items
