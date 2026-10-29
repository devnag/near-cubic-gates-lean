import SourceAdapters.RAMACSP.GenStageB
import SourceAdapters.Machine.ComposeCarry
import NineInputs
import SourceAdapters.RAMACSP.ConstraintEmit
import SourceAdapters.RAMACSP.CheckFrame

/-!
# The generator as one cell program, with the constraint circuit's printer as a callee

Paper: `lem:generator` ("There is an algorithm that, given `x ∈ {0,1}^n` … and an integer `t ≥ n` in binary,
outputs `x̄` and the instance `I_x` … in `poly(n, log t)` steps"; "It obtains `irr` from Shoup's deterministic
algorithm"), the description of `def:acsp` (`Instance.word`) and `cor:short-pcp-clock` ("The construction does not
test the promise").

The program `mainP` (`L`'s cell language, one callee):
`preP; stageA; callIrr; stageB1; callCons; copyOut; stageB2; emit 0`.
The callee is `sumWF` (`ComposeCarry`) of Shoup's machine (`PolyTimeIrrChoice`, tag `1`) and the constraint circuit's
printer `ConsWF` (an ordinary word function printing `frame (listWord gateWord (ownCons V irrPoly r))` on
`ClockRequest.word r` within a polynomial budget; tag `0`).

`main_run`: under the size conditions `MainFits`, the run prints exactly
`frame (frame x̄ ++ (ownInst V irrPoly (ownCons V irrPoly) r).word)`, the description of `def:acsp` field by field:
`f`, `irr`, the basis and offset of `H`, the neighbor pairs, the circuit, the basis and offset of `I`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicGates.Adapters.Machine.ComposeCarry
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])

/-! ## The modulus mask -/

theorem bitsValue_coeffWord (f : ℕ) (a : (ZMod 2)[X]) :
    CanonicalBinary.bitsValue (Published.Shoup.coeffWord f a) = modMask a f := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : (CanonicalBinary.bitsValue (Published.Shoup.coeffWord f a)).testBit i =
      ((Published.Shoup.coeffWord f a).getD i false) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, testBit_bitsValue]
    cases (Published.Shoup.coeffWord f a).getD i false <;> simp
  rw [h1, modMask, WireExponent3_5.GF.ofPoly, WireExponent3_5.GF.testBit_equivBitIndices_symm]
  simp only [Published.Shoup.coeffWord, Finset.mem_filter, Finset.mem_range]
  by_cases hi : i < f + 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    simp only [hi, true_and]
    by_cases hc : a.coeff i = 0
    · simp [hc]
    · simp [hc, WireExponent3_5.GF.zmod2_ne_zero _ hc]
  · rw [List.getD_eq_default _ _ (by simpa using hi)]; simp [hi]

theorem coeffWord_length (f : ℕ) (a : (ZMod 2)[X]) : (Published.Shoup.coeffWord f a).length = f + 1 := by
  simp [Published.Shoup.coeffWord]

/-! ## The constraint circuit's printer and the callee -/

/-- The serialization of the constraint circuit (the `cons` field of `Instance.word`). -/
def consWord (r : ClockRequest) : List Bool := listWord gateWord (ownCons V irrPoly r)

/-- **The constraint circuit's printer**: an ordinary machine printing the circuit's serialization (framed) on the
request word, within a polynomial budget. -/
def ConsWF (K e : ℕ) : Type :=
  WordFunction ClockRequest ClockRequest.word (fun r => RepairSource.frame (consWord V irrPoly r))
    (fun r => K * (r.1.1 + natBitLength r.2 + 1) ^ e)

/-- Shoup's machine (the leaf's `PolyTimeIrrChoice`). -/
def ShoupWF (K e : ℕ) : Type :=
  WordFunction {f : ℕ // 1 ≤ f} (fun f => List.replicate f.val true)
    (fun f => Published.Shoup.coeffWord f.val (irrPoly f.val)) (fun f => K * (f.val + 1) ^ e)

/-- **The callee**: Shoup's machine (tag `1`) and the cons printer (tag `0`). -/
def genCallee {Ks es Kc ec : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : ConsWF V irrPoly Kc ec) : Callee :=
  ⟨{f : ℕ // 1 ≤ f} ⊕ ClockRequest, sumInput (fun f => List.replicate f.val true) ClockRequest.word,
    sumOutput (fun f => Published.Shoup.coeffWord f.val (irrPoly f.val)) (fun r => RepairSource.frame (consWord V irrPoly r)),
    sumBudget (fun f => List.replicate f.val true) (fun f => Ks * (f.val + 1) ^ es) ClockRequest.word
      (fun r => Kc * (r.1.1 + natBitLength r.2 + 1) ^ ec), sumWF WS WC⟩

/-! ## The program -/

/-- **The generator program.** -/
def mainP : St VV MM :=
  .seq FL.preP (.seq (compS (stageA V) 0) (.seq callIrr (.seq (compS stageB1 0) (.seq callCons (.seq copyOut
    (.seq (compS stageB2 0) (compS (.emit (.k 0)) 0)))))))

end NearCubicGates.Adapters.RAMACSP.Gen

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicGates.Adapters.Machine.ComposeCarry
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

theorem wf_stageA (V : Verifier) : wfS (stageA V) 0 = true := rfl
theorem wf_stageB1 : wfS stageB1 0 = true := by decide
theorem wf_stageB2 : wfS stageB2 0 = true := by decide
theorem wf_emit0 : wfS (.emit (.k 0)) 0 = true := by decide


/-! ## The instance word, field by field -/

theorem ownInst_word (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate)
    (r : ClockRequest) : (ownInst V irrPoly cons r).word =
      natWord (fieldExp V r.2) ++ natWord (modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2)) ++
        listWord natWord ((List.range (domExp V r.2)).map (2 ^ ·)) ++ natWord 0 ++
        listWord ACSP.Affine.Instance.pairWord ((Routing.globalBank (ownLayout V r.2)).map (fun b => (1, b))) ++
        listWord gateWord (cons r) ++
        listWord natWord (inBasis V r) ++ natWord (2 ^ tau V r.2) := rfl

/-! ## The run -/

section Run

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) {Ks es Kc ec : ℕ}
variable (WS : ShoupWF irrPoly Ks es) (WC : ConsWF V irrPoly Kc ec)

/-- The size conditions of the run at request `r` in the context `C` (run constants `G`). -/
structure MainFits (r : ClockRequest) (C : Ctx) (G : Glob) : Prop where
  aFit : AFit V r G
  bFit : BFit V r.2 G
  lkI : fieldExp V r.2 + 1 < C.Lk
  lkC : 2 * r.1.1 + 2 * r.2.bits.length + 3 < C.Lk
  bkI : ∀ h : 1 ≤ fieldExp V r.2, sumBudget (fun f : {f : ℕ // 1 ≤ f} => List.replicate f.val true)
    (fun f => Ks * (f.val + 1) ^ es) ClockRequest.word (fun r => Kc * (r.1.1 + natBitLength r.2 + 1) ^ ec)
    (.inl ⟨fieldExp V r.2, h⟩) ≤ C.Bk
  bkC : sumBudget (fun f : {f : ℕ // 1 ≤ f} => List.replicate f.val true)
    (fun f => Ks * (f.val + 1) ^ es) ClockRequest.word (fun r => Kc * (r.1.1 + natBitLength r.2 + 1) ^ ec)
    (.inr r) ≤ C.Bk
  wI : 2 ^ (fieldExp V r.2 + 3) < 2 ^ C.Wd
  wC : r.1.1 + r.2.bits.length + 4 < 2 ^ C.Wd

theorem ctx_K (K : Callee) (z : Sz) (inp : List Bool) : (ctxOf K z inp).K = K := rfl

theorem genCallee_outw_inl (g : {f : ℕ // 1 ≤ f}) :
    (genCallee V irrPoly WS WC).outw (.inl g) = Published.Shoup.coeffWord g.val (irrPoly g.val) := rfl

theorem genCallee_outw_inr (r : ClockRequest) :
    (genCallee V irrPoly WS WC).outw (.inr r) = RepairSource.frame (consWord V irrPoly r) := rfl

/-- The cost bound of the run. -/
def mainCost (C : Ctx) (G : Glob) (inp : List Bool) (r : ClockRequest) : ℕ :=
  preCost inp + costS G (stageA V) + callIrrCost C (fieldExp V r.2) + costS G stageB1 +
    callConsCost C r.1.1 r.2.bits.length + (10 * (consWord V irrPoly r).length + 4) + costS G stageB2 +
    costS G (.emit (.k 0)) + 7

theorem one_le_fieldExp (t : ℕ) : 1 ≤ fieldExp V t := by have := domExp_add_two_le_fieldExp V t; omega

/-- **The generator's run** (`lem:generator`, correctness): on `1^L 0 ++ ClockRequest.word r` (`L ≥ 1`), `mainP`
prints `frame (frame x̄ ++ word)` for the instance with the constraint circuit `ownCons`, on every request. -/
theorem main_run (a2 c2 a3 c3 : ℕ) (r : ClockRequest) (L : ℕ) (hL : 1 ≤ L)
    (fits : MainFits V (Ks := Ks) (es := es) (Kc := Kc) (ec := ec) r
      (ctxOf (genCallee V irrPoly WS WC) (zM a2 c2 a3 c3) (List.replicate L true ++ false :: ClockRequest.word r))
      (globOf (List.replicate L true ++ false :: ClockRequest.word r))) :
    ∃ b n, Ex (ctxOf (genCallee V irrPoly WS WC) (zM a2 c2 a3 c3) (List.replicate L true ++ false :: ClockRequest.word r))
      (mainP V) a0 b n ∧
      b.out = RepairSource.frame (RepairSource.frame (ownXbar V r) ++ (ownInst V irrPoly (ownCons V irrPoly) r).word) ∧
      n ≤ mainCost V irrPoly
        (ctxOf (genCallee V irrPoly WS WC) (zM a2 c2 a3 c3) (List.replicate L true ++ false :: ClockRequest.word r))
        (globOf (List.replicate L true ++ false :: ClockRequest.word r))
        (List.replicate L true ++ false :: ClockRequest.word r) r := by
  set inp := List.replicate L true ++ false :: ClockRequest.word r with hinp
  set C := ctxOf (genCallee V irrPoly WS WC) (zM a2 c2 a3 c3) inp with hC
  set G := globOf inp with hG
  have hlead : leadOnes inp = L := NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_rep _ _
  have h1 : 1 ≤ leadOnes inp := by omega
  have hlt : leadOnes inp < inp.length := by rw [hlead]; simp [hinp]
  have hg : GOk C G := gokM _ a2 c2 a3 c3 inp h1
  have hCinp : C.inp = G.inp := rfl
  have SO := compS_ok hg hCinp
  have hAF := fits.aFit
  obtain ⟨⟨hPK, hPN⟩, hPP⟩ := fits.aFit
  have hBF := fits.bFit
  have hf1 := one_le_fieldExp V r.2
  have hcapK := cap_add G
  have hKlt : G.K < 2 ^ G.K := Nat.lt_two_pow_self
  set f := fieldExp V r.2 with hf
  set cw := consWord V irrPoly r with hcw
  suffices H : Hs C (mainP V) a0 (mainCost V irrPoly C G inp r)
      (fun b => b.out = RepairSource.frame (RepairSource.frame (ownXbar V r) ++
        (ownInst V irrPoly (ownCons V irrPoly) r).word)) by
    obtain ⟨b, n, hx, hn, hb⟩ := H
    exact ⟨b, n, hx, hb, hn⟩
  unfold mainP
  refine Hs.mono (Hs.seq (t2 := costS G (stageA V) + (callIrrCost C f + (costS G stageB1 + (callConsCost C r.1.1
      r.2.bits.length + ((10 * cw.length + 4) + (costS G stageB2 + costS G (.emit (.k 0)) + 1) + 1) + 1) + 1) + 1) + 1)
    (preM_ok _ a2 c2 a3 c3 inp hlt) (fun b0 hb0 => ?_)) (by unfold mainCost; rw [← hf, ← hcw]; omega) (fun _ h => h)
  obtain ⟨hb0, hk0⟩ := hb0
  have r0 : Rel G (FL.s0 inp) b0 := rel_s0 inp h1 b0 hb0
  -- stage A
  have hinA : G.inp.drop (FL.s0 inp).ip = ClockRequest.word r ++ [] := by
    show inp.drop (leadOnes inp + 1) = _
    rw [hlead, hinp, drop_prefix_word, List.append_nil]
  obtain ⟨pvA, outA, badA, flA, fpA⟩ := stageA_spec V (G := G) (FL.s0 inp) r [] hinA hAF
  generalize hsA : evalS G (stageA V) (FL.s0 inp) = sA at pvA outA badA flA fpA
  have SA := SO (stageA V) 0 (FL.s0 inp) b0 (by norm_num) (wf_stageA V) (by rw [hsA, badA]; rfl) r0
  rw [hsA] at SA
  refine Hs.seq SA (fun b1 sp1 => ?_)
  have hk1 : b1.kin = [] := sp1.fix.2.2.1.trans hk0
  -- the Shoup call
  have hcapf : 2 ^ (f + 1) ≤ G.cap + 1 := by
    rw [hcapK]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have houtI : C.K.outw (.inl ⟨f, hf1⟩) = Published.Shoup.coeffWord f (irrPoly f) :=
    genCallee_outw_inl V irrPoly WS WC ⟨f, hf1⟩
  refine Hs.seq (callIrr_spec C G sA b1 sp1.rel hk1 f pvA.f (.inl ⟨f, hf1⟩) rfl (C.K.outw (.inl ⟨f, hf1⟩)) rfl
    (by rw [houtI, coeffWord_length]) (fits.bkI hf1) fits.lkI fits.wI hcapf) (fun b2 hb2 => ?_)
  obtain ⟨r2, k2⟩ := hb2
  rw [houtI, bitsValue_coeffWord] at r2
  set sA' := sA.setv 37 (modMask (irrPoly f) f) with hsA'
  have pvA' : PV V r sA' := pvA.keep V (fun i h1 h2 => by
    simp only [hsA', FS.setv_env, Function.update_apply]; rw [if_neg (by intro e; subst e; exact absurd h2 (by decide))])
  -- stage B1
  have hirr : modMask (irrPoly f) f < 2 ^ (f + 1) := WireExponent3_5.GF.ofPoly_lt _ _
  have EB1 := stageB1_spec V (G := G) r sA' pvA' (modMask (irrPoly f) f) (by simp [hsA']) hirr hBF
  have SB1 := SO stageB1 0 sA' b2 (by norm_num) wf_stageB1 (by rw [EB1.bad]; simp [hsA', badA]; rfl) r2
  refine Hs.seq SB1 (fun b3 sp3 => ?_)
  generalize hsB : evalS G stageB1 sA' = sB at EB1 sp3
  have pvB : PV V r sB := pvA'.keep V (fun i h1 h2 => EB1.env i (fun hm => by
    rcases mem_LW.mp hm with h | h <;> omega))
  have hk3 : b3.kin = [] := sp3.fix.2.2.1.trans k2
  -- the constraint circuit's printer
  have hx1 : sB.env 20 = CanonicalBinary.bitsValue (List.ofFn r.1.2) := pvB.x
  have hx2 : sB.env 21 = (List.ofFn r.1.2).length := by rw [pvB.n, List.length_ofFn]
  have hy1 : sB.env 22 = CanonicalBinary.bitsValue r.2.bits := by rw [pvB.t, CanonicalBinary.bitsValue_natBits]
  have hy2 : sB.env 23 = r.2.bits.length := pvB.tb
  refine Hs.seq (Hs.mono (callCons_spec C G sB b3 sp3.rel hk3 (List.ofFn r.1.2) r.2.bits hx1 hx2 hy1 hy2 (.inr r) rfl
    fits.bkC (by rw [List.length_ofFn]; exact fits.lkC) (by rw [List.length_ofFn]; exact fits.wC))
    (by rw [List.length_ofFn]) (fun _ h => h)) (fun b4 hb4 => ?_)
  obtain ⟨r4, -, o4, c4⟩ := hb4
  have houtC : C.K.outw (.inr r) = RepairSource.frame cw := genCallee_outw_inr V irrPoly WS WC r
  refine Hs.seq (copyOut_spec C G sB b4 r4 cw (o4.trans houtC) c4) (fun b5 hb5 => ?_)
  obtain ⟨r5, k5⟩ := hb5
  set sC : FS := { sB with out := sB.out ++ dbl cw } with hsC
  have pvC : PV V r sC := pvB.keep V (fun _ _ _ => rfl)
  -- stage B2
  have EB2 := stageB2_spec V (G := G) r sC pvC hBF hAF
  have hbB : sB.bad = false := by rw [EB1.bad]; simp [hsA', badA]; rfl
  have SB2 := SO stageB2 0 sC b5 (by norm_num) wf_stageB2 (by rw [EB2.bad]; exact hbB) r5
  refine Hs.seq SB2 (fun b6 sp6 => ?_)
  generalize hsD : evalS G stageB2 sC = sD at EB2 sp6
  have SE := SO (.emit (.k 0)) 0 sD b6 (by norm_num) wf_emit0 (by
    show sD.bad = false; rw [EB2.bad]; exact hbB) sp6.rel
  refine Hs.mono SE le_rfl (fun b7 sp7 => ?_)
  rw [sp7.rel.out]
  show sD.out ++ [evalE G sD (.k 0) != 0] = _
  rw [show evalE G sD (.k 0) = 0 from Nat.zero_min _, EB2.out]
  show sB.out ++ dbl cw ++ _ ++ _ = _
  rw [EB1.out, show sA'.out = sA.out from rfl, outA, ownInst_word,
    show (FL.s0 inp).out = ([] : List Bool) from rfl]
  simp only [frame_dbl, dbl_append, List.nil_append, List.append_assoc, hcw, consWord]
  rfl

end Run
end NearCubicGates.Adapters.RAMACSP.Gen
