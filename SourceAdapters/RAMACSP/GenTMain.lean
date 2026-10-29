import SourceAdapters.RAMACSP.GenTRoute
import SourceAdapters.RAMACSP.GenTGlue
import SourceAdapters.RAMACSP.GenTCoord
import SourceAdapters.RAMACSP.GenItemsSeam
import SourceAdapters.RAMACSP.GenCoordDock
import SourceAdapters.RAMACSP.GenMain
import SourceAdapters.RAMACSP.CheckDegree

/-!
# The input printer of `Joins/TermsCircuit`

Paper: `lem:generator` ("It emits the neighbor offsets …; the guard patterns …; and, for each equation family and bit
index, the selector times the equation"), with the circuit's input word
`Joins.termsInput` of the join `TermsCircuit`: `natWord f ++ natWord mH ++` the coordinate masks `++
listWord natWord (globalBank l) ++` the item words of `routingPairs l ++ machineItems … ++ natWord 0`.

The cell program `termsP` (callee `sumWF Shoup (sumWF coordinates items)`, `termsCallee`):
`preP`; `stageR` (read the request, compute the numbers); `callIrr` (Shoup: the modulus mask in `37`); `headP` (`natWord f ++
natWord mH`, and the lengths of `f, irr, mH` in `41, 42, 43`); `callCoord` + `copyOut` (the coordinate word, from
`Joins.CoordArrayWF`); `bodyP` (the bank list and the routing items); `callItems` + `copyOut` (the machine items, from
`MachineItemsWF`); `natWord 0`; the end bit. `terms_run`: the output is `frame (termsInput (termsRequest r))` on every
request.
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

/-! ## The callee -/

section Callee

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)

/-- The coordinate word at the clock request `r`. -/
def cwOf (r : ClockRequest) : List Bool := Joins.coordWord (coordRequest V irrPoly r) (coordRequest_ok V irrPoly hI r)

/-- The coordinate machine on the generator's requests, framed. -/
def CoordFWF (K e : ℕ) : Type :=
  WordFunction ClockRequest (fun r => Joins.coordInput (coordRequest V irrPoly r))
    (fun r => RepairSource.frame (cwOf V irrPoly hI r))
    (fun r => K * ((Joins.coordInput (coordRequest V irrPoly r)).length + 1) ^ e)

/-- The machine-items printer (`MachineItemsWF`). -/
def ItemsWF (K e : ℕ) : Type :=
  WordFunction ClockRequest ClockRequest.word (fun r => RepairSource.frame (machineItemsWord V irrPoly r))
    (fun r => K * (r.1.1 + natBitLength r.2 + 1) ^ e)

/-- The input word of the inner pair. -/
abbrev tIn : ClockRequest ⊕ ClockRequest → List Bool :=
  sumInput (fun r => Joins.coordInput (coordRequest V irrPoly r)) ClockRequest.word

/-- The budget of the inner pair. -/
abbrev tBud (Kc ec Ki ei : ℕ) : ClockRequest ⊕ ClockRequest → ℕ :=
  sumBudget (fun r => Joins.coordInput (coordRequest V irrPoly r))
    (fun r => Kc * ((Joins.coordInput (coordRequest V irrPoly r)).length + 1) ^ ec) ClockRequest.word
    (fun r => Ki * (r.1.1 + natBitLength r.2 + 1) ^ ei)

/-- The whole callee's budget. -/
abbrev tBudAll (Ks es Kc ec Ki ei : ℕ) : {f : ℕ // 1 ≤ f} ⊕ (ClockRequest ⊕ ClockRequest) → ℕ :=
  sumBudget (fun f : {f : ℕ // 1 ≤ f} => List.replicate f.val true) (fun f => Ks * (f.val + 1) ^ es)
    (tIn V irrPoly) (tBud V irrPoly Kc ec Ki ei)

/-- **The callee**: Shoup (tag `1`), then the coordinate machine (tags `0 1`) and the machine items (tags `0 0`). -/
def termsCallee {Ks es Kc ec Ki ei : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordFWF V irrPoly hI Kc ec)
    (WI : ItemsWF V irrPoly Ki ei) : Callee :=
  ⟨{f : ℕ // 1 ≤ f} ⊕ (ClockRequest ⊕ ClockRequest),
    sumInput (fun f => List.replicate f.val true) (tIn V irrPoly),
    sumOutput (fun f => Published.Shoup.coeffWord f.val (irrPoly f.val))
      (sumOutput (fun r => RepairSource.frame (cwOf V irrPoly hI r)) (fun r => RepairSource.frame (machineItemsWord V irrPoly r))),
    tBudAll V irrPoly Ks es Kc ec Ki ei, sumWF WS (sumWF WC WI)⟩

end Callee

/-! ## The program -/

section Program

variable (V : Verifier)

/-- Read the request and compute the G2 numbers. -/
def stageR : S := .seq readP (paramsP V)

/-- `natWord f ++ natWord mH`; the lengths of `f`, `irr`, `mH` into `41, 42, 43`. -/
def headP : S :=
  .seq (natLenP 36) (.seq (.set 41 (.v 6)) (.seq (natLenP 37) (.seq (.set 42 (.v 6)) (.seq (natLenP 35)
    (.seq (.set 43 (.v 6)) (.seq (emitNatV 36) (emitNatV 35)))))))

/-- The bank list and the routing items. -/
def bodyP : S := .seq bankNatP routeP

/-- **The term printer.** -/
def termsP : St VV MM :=
  .seq FL.preP (.seq (compS (stageR V) 0) (.seq callIrr (.seq (compS headP 0) (.seq callCoord (.seq copyOut
    (.seq (compS bodyP 0) (.seq callItems (.seq copyOut (.seq (compS (emitNatE (.k 0)) 0) (compS (.emit (.k 0)) 0))))))))))

theorem wf_stageR : wfS (stageR V) 0 = true := rfl
theorem wf_headP : wfS headP 0 = true := by decide
theorem wf_bodyP : wfS bodyP 0 = true := by decide
theorem wf_emitNat0 : wfS (emitNatE (.k 0)) 0 = true := by decide

end Program

/-! ## The FL stages -/

section Stages

variable (V : Verifier) {G : Glob}

theorem stageR_spec (s : FS) (r : ClockRequest) (rest : List Bool)
    (hin : G.inp.drop s.ip = ClockRequest.word r ++ rest) (hfit : ParamFit V r G) :
    let u := evalS G (stageR V) s
    PV V r u ∧ u.out = s.out ∧ u.bad = s.bad ∧ u.fl = s.fl ∧ u.fp = s.fp := by
  intro u
  obtain ⟨hK, hKN⟩ := hfit
  obtain ⟨a20, a21, a22, a23, aW⟩ := readP_spec (G := G) s r rest hin (pow_le_cap' (by omega))
    (pow_le_cap' (by omega)) (by omega) (by omega)
  generalize hs1 : evalS G readP s = s1 at a20 a21 a22 a23 aW
  obtain ⟨pv2, w2⟩ := paramsP_spec V (G := G) r s1 a20 a21 a22 a23 ⟨hK, hKN⟩
  have hu : u = evalS G (paramsP V) s1 := by show evalS G (stageR V) s = _; rw [← hs1]; rfl
  rw [hu]
  exact ⟨pv2, by rw [w2.out, aW.out], by rw [w2.bad, aW.bad], by rw [w2.fl, aW.fl], by rw [w2.fp, aW.fp]⟩

/-- The scratch of `headP`. -/
def HW : List Var := [5, 6, 41, 42, 43]

theorem headP_spec (s : FS) (r : ClockRequest) (h : PV V r s) (irr : ℕ) (h37 : s.env 37 = irr)
    (hirr : irr < 2 ^ (fieldExp V r.2 + 1)) (hK : fieldExp V r.2 + 8 ≤ G.K) (hKN : G.K ≤ G.N) :
    let u := evalS G headP s
    PV V r u ∧ u.env 37 = irr ∧ u.env 41 = natBitLength (fieldExp V r.2) ∧ u.env 42 = natBitLength irr ∧
      u.env 43 = natBitLength (domExp V r.2) ∧
      Em HW s u (natWord (fieldExp V r.2) ++ natWord (domExp V r.2)) := by
  intro u
  have hf := fieldExp V r.2
  have hmf := domExp_add_two_le_fieldExp V r.2
  have nf : natBitLength (fieldExp V r.2) + 2 ≤ G.K := by have := natBitLength_le (fieldExp V r.2); omega
  have nm : natBitLength (domExp V r.2) + 2 ≤ G.K := by have := natBitLength_le (domExp V r.2); omega
  have ni : natBitLength irr + 2 ≤ G.K := by
    have := natBitLength_le_of_lt (v := irr) (L := fieldExp V r.2 + 1) (by omega) hirr; omega
  have m6 : ∀ x ∈ ([6] : List Var), x ∈ HW := by decide
  have m56 : ∀ x ∈ ([5, 6] : List Var), x ∈ HW := by decide
  -- natLenP 36
  obtain ⟨l1, e1⟩ := natLenP_spec (G := G) s 36 (by decide) (by rw [h.f]; exact nf) hKN
  generalize hs1 : evalS G (natLenP 36) s = s1 at l1 e1
  have s1e : ∀ i : Var, i ∉ HW → s1.env i = s.env i := fun i hi => e1.env i (fun h' => hi (m6 i h'))
  -- 41 := 6
  set s2 := s1.setv 41 (evalE G s1 (.v 6)) with hs2
  have e2 : Em HW s1 s2 [] := Em.setv s1 (by decide) _
  -- natLenP 37
  have s2_37 : s2.env 37 = irr := by simp [hs2, s1e 37 (by decide), h37]
  obtain ⟨l3, e3⟩ := natLenP_spec (G := G) s2 37 (by decide) (by rw [s2_37]; exact ni) hKN
  generalize hs3 : evalS G (natLenP 37) s2 = s3 at l3 e3
  set s4 := s3.setv 42 (evalE G s3 (.v 6)) with hs4
  have e4 : Em HW s3 s4 [] := Em.setv s3 (by decide) _
  have s4e : ∀ i : Var, i ∉ HW → s4.env i = s.env i := fun i hi =>
    (e4.env i hi).trans ((e3.env i (fun h' => hi (m6 i h'))).trans ((e2.env i hi).trans (s1e i hi)))
  obtain ⟨l5, e5⟩ := natLenP_spec (G := G) s4 35 (by decide) (by rw [s4e 35 (by decide), h.mH]; exact nm) hKN
  generalize hs5 : evalS G (natLenP 35) s4 = s5 at l5 e5
  set s6 := s5.setv 43 (evalE G s5 (.v 6)) with hs6
  have e6 : Em HW s5 s6 [] := Em.setv s5 (by decide) _
  have s6e : ∀ i : Var, i ∉ HW → s6.env i = s.env i := fun i hi =>
    (e6.env i hi).trans ((e5.env i (fun h' => hi (m6 i h'))).trans (s4e i hi))
  have e7 := emitNatV_spec (G := G) s6 36 (by decide) (by decide) (by rw [s6e 36 (by decide), h.f]; exact nf) hKN
  generalize hs7 : evalS G (emitNatV 36) s6 = s7 at e7
  have s7e : ∀ i : Var, i ∉ HW → s7.env i = s.env i := fun i hi => (e7.env i (fun h' => hi (m56 i h'))).trans (s6e i hi)
  have e8 := emitNatV_spec (G := G) s7 35 (by decide) (by decide) (by rw [s7e 35 (by decide), h.mH]; exact nm) hKN
  generalize hs8 : evalS G (emitNatV 35) s7 = s8 at e8
  have hu : u = s8 := by
    show evalS G headP s = s8
    rw [← hs8, ← hs7, hs6, ← hs5, hs4, ← hs3, hs2, ← hs1]; rfl
  rw [hu]
  have s8e : ∀ i : Var, i ∉ HW → s8.env i = s.env i := fun i hi => (e8.env i (fun h' => hi (m56 i h'))).trans (s7e i hi)
  have s8_41 : s8.env 41 = natBitLength (fieldExp V r.2) := by
    rw [e8.env 41 (by decide), e7.env 41 (by decide), hs6, FS.setv_env, Function.update_of_ne (by decide),
      e5.env 41 (by decide), hs4, FS.setv_env, Function.update_of_ne (by decide), e3.env 41 (by decide), hs2]
    simp [eE_v, l1, h.f]
  have s8_42 : s8.env 42 = natBitLength irr := by
    rw [e8.env 42 (by decide), e7.env 42 (by decide), hs6, FS.setv_env, Function.update_of_ne (by decide),
      e5.env 42 (by decide), hs4]
    simp [eE_v, l3, s2_37]
  have s8_43 : s8.env 43 = natBitLength (domExp V r.2) := by
    rw [e8.env 43 (by decide), e7.env 43 (by decide), hs6]
    simp [eE_v, l5, s4e 35 (by decide), h.mH]
  refine ⟨h.keep V (fun i h1 h2 => s8e i (notmem_hi (by decide) h1 h2)),
    by rw [s8e 37 (by decide), h37], s8_41, s8_42, s8_43, ?_⟩
  have E := ((e1.mono m6).trans (e2.trans ((e3.mono m6).trans (e4.trans ((e5.mono m6).trans (e6.trans
    ((e7.mono m56).trans (e8.mono m56))))))))
  rw [s6e 36 (by decide), h.f, s7e 35 (by decide), h.mH] at E
  simpa using E

theorem bodyP_spec {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (s : FS) (r : ClockRequest) (h : PV V r s)
    (hfit : BFit V r.2 G) :
    Em LW s (evalS G bodyP s) (listWord natWord (Routing.globalBank (ownLayout V r.2)) ++
      (routingPairs (F := F) (ownLayout V r.2)).flatMap (itemWord mk)) := by
  obtain ⟨hK, hN, hKN⟩ := hfit
  have hmf := domExp_add_two_le_fieldExp V r.2
  have hm : (ownLayout V r.2).m = domExp V r.2 := ownLayout_m V r.2
  have hl := lv_own V h
  have hK' : (ownLayout V r.2).m + 8 ≤ G.K := by rw [hm]; omega
  have hk : (ownLayout V r.2).k = laneExp V r.2 := rfl
  have hq : (ownLayout V r.2).q = colExp V r.2 := rfl
  have hq2 : colExp V r.2 < 2 ^ colExp V r.2 := Nat.lt_two_pow_self
  refine Em_acc (bankNatP_spec (ownLayout V r.2) s hl hK' hKN (by rw [hk, hq]; omega)) (fun t1 a1 => ?_)
  exact routeP_spec mk (ownLayout V r.2) t1 (lv_of hl a1.env) hK' hKN (by rw [hk]; omega) (by rw [hq]; omega)
    (by rw [hm]; omega)

end Stages

/-! ## The printed word is the join's input word -/

section Word

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)

/-- The generator's request of the join (with Shoup's modulus). -/
abbrev tReq (r : ClockRequest) : Joins.TermsReq := termsRequest V irrPoly r (modulusGood V irrPoly hI r)

theorem tReq_ok (r : ClockRequest) : Joins.TermsOk (tReq V irrPoly hI r) :=
  termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)

attribute [local irreducible] ownLayout baseIrr in
/-- The bank list and the routing items' words. -/
def bodyWord (r : ClockRequest) : List Bool :=
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨(modulusGood V irrPoly hI r).1⟩
  listWord natWord (Routing.globalBank (ownLayout V r.2)) ++
    (routingPairs (F := ACSP.Field2 (baseIrr V irrPoly r)) (ownLayout V r.2)).flatMap
      (itemWord (Joins.termsMask (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)))

theorem termsInput_gen (p : Joins.TermsReq) (h : Joins.TermsOk p) :
    Joins.termsInput p h = natWord p.f ++ natWord p.l.m ++ Joins.termsCoordWord p h ++
      listWord natWord (Routing.globalBank p.l) ++
        (p.items.flatMap (itemWord (Joins.termsMask p h)) ++ natWord 0) := rfl

attribute [local irreducible] ownLayout baseIrr in
theorem termsInput_eq (r : ClockRequest) :
    Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r) =
      natWord (fieldExp V r.2) ++ natWord (domExp V r.2) ++ cwOf V irrPoly hI r ++ bodyWord V irrPoly hI r ++
        machineItemsWord V irrPoly r ++ natWord 0 := by
  have hf1 : 1 ≤ fieldExp V r.2 := by have := domExp_add_two_le_fieldExp V r.2; omega
  have hd := (hI _ hf1).2
  have hl : (tReq V irrPoly hI r).l = ownLayout V r.2 := rfl
  have hf : (tReq V irrPoly hI r).f = fieldExp V r.2 := rfl
  have hcw : cwOf V irrPoly hI r = Joins.termsCoordWord (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r) := by
    refine coordWord_terms _ _ _ _ rfl ?_ ?_
    · show domExp V r.2 = (ownLayout V r.2).m
      rw [ownLayout_m]
    · rw [coordRequest_toPoly V irrPoly r hd]
      show _ = baseIrr V irrPoly r
      rw [baseIrr_eq V irrPoly r hd]
  have hmi : machineItemsWord V irrPoly r =
      haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨(modulusGood V irrPoly hI r).1⟩
      (machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V)
      (ownRam V r) RAMTrace.mnKind (tau V r.2) (inRecExp V r) (termsLam V irrPoly r (modulusGood V irrPoly hI r))).flatMap
      (Joins.itemWord (Joins.termsMask (termsRequest V irrPoly r (modulusGood V irrPoly hI r))
        (termsRequest_ok V irrPoly r (modulusGood V irrPoly hI r)))) :=
    dif_pos (modulusGood V irrPoly hI r)
  refine (termsInput_gen _ _).trans ?_
  have h1 : natWord (tReq V irrPoly hI r).f = natWord (fieldExp V r.2) := rfl
  have h2 : natWord (tReq V irrPoly hI r).l.m = natWord (domExp V r.2) := by rw [hl, ownLayout_m]
  have h4 : listWord natWord (Routing.globalBank (tReq V irrPoly hI r).l) =
      listWord natWord (Routing.globalBank (ownLayout V r.2)) := rfl
  have h5 : (tReq V irrPoly hI r).items.flatMap (itemWord (Joins.termsMask (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r))) =
      haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨(modulusGood V irrPoly hI r).1⟩
      (routingPairs (F := ACSP.Field2 (baseIrr V irrPoly r)) (ownLayout V r.2)).flatMap
        (itemWord (Joins.termsMask (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r))) ++ machineItemsWord V irrPoly r := by
    have hit : (tReq V irrPoly hI r).items =
        haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨(modulusGood V irrPoly hI r).1⟩
        ownItems V r (termsLam V irrPoly r (modulusGood V irrPoly hI r)) := rfl
    simp only [hit, ownItems, hmi]
    exact List.flatMap_append
  simp only [h1, h2, h4, h5, hcw.symm, bodyWord, List.append_assoc]

end Word

/-! ## The run -/

section Run

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (hI : Published.Shoup.IrreducibleChoice irrPoly)
  {Ks es Kc ec Ki ei : ℕ} (WS : ShoupWF irrPoly Ks es) (WC : CoordFWF V irrPoly hI Kc ec) (WI : ItemsWF V irrPoly Ki ei)

/-- The modulus mask. -/
abbrev irrM (r : ClockRequest) : ℕ := modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2)

/-- The size conditions of the run. -/
structure TFits (r : ClockRequest) (C : Ctx) (G : Glob) : Prop where
  pFit : ParamFit V r G
  bFit : BFit V r.2 G
  lkI : fieldExp V r.2 + 1 < C.Lk
  lkCo : 2 * natBitLength (fieldExp V r.2) + 2 * natBitLength (irrM V irrPoly r) + 2 * natBitLength (domExp V r.2) + 6 <
    C.Lk
  lkC : 2 * r.1.1 + 2 * r.2.bits.length + 4 < C.Lk
  bkI : ∀ h : 1 ≤ fieldExp V r.2, tBudAll V irrPoly Ks es Kc ec Ki ei (.inl ⟨fieldExp V r.2, h⟩) ≤ C.Bk
  bkCo : tBudAll V irrPoly Ks es Kc ec Ki ei (.inr (.inl r)) ≤ C.Bk
  bkC : tBudAll V irrPoly Ks es Kc ec Ki ei (.inr (.inr r)) ≤ C.Bk
  wI : 2 ^ (fieldExp V r.2 + 3) < 2 ^ C.Wd
  wCo : natBitLength (fieldExp V r.2) + natBitLength (irrM V irrPoly r) + natBitLength (domExp V r.2) + 4 < 2 ^ C.Wd
  wC : r.1.1 + r.2.bits.length + 4 < 2 ^ C.Wd

/-- The cost bound of the run. -/
def tCost (C : Ctx) (G : Glob) (inp : List Bool) (r : ClockRequest) : ℕ :=
  preCost inp + costS G (stageR V) + callIrrCost C (fieldExp V r.2) + costS G headP +
    callCoordCost C (fieldExp V r.2) (irrM V irrPoly r) (domExp V r.2) + (10 * (cwOf V irrPoly hI r).length + 4) +
    costS G bodyP + callItemsCost C r.1.1 r.2.bits.length + (10 * (machineItemsWord V irrPoly r).length + 4) +
    costS G (emitNatE (.k 0)) + costS G (.emit (.k 0)) + 11

theorem tCallee_outw_inl (g : {f : ℕ // 1 ≤ f}) :
    (termsCallee V irrPoly hI WS WC WI).outw (.inl g) = Published.Shoup.coeffWord g.val (irrPoly g.val) := rfl

theorem tCallee_outw_co (r : ClockRequest) :
    (termsCallee V irrPoly hI WS WC WI).outw (.inr (.inl r)) = RepairSource.frame (cwOf V irrPoly hI r) := by
  simp only [termsCallee, sumOutput]

theorem tCallee_outw_it (r : ClockRequest) :
    (termsCallee V irrPoly hI WS WC WI).outw (.inr (.inr r)) = RepairSource.frame (machineItemsWord V irrPoly r) := by
  simp only [termsCallee, sumOutput]

theorem tCallee_inw_co (r : ClockRequest) :
    (termsCallee V irrPoly hI WS WC WI).inw (.inr (.inl r)) =
      false :: true :: (natWord (fieldExp V r.2) ++ natWord (irrM V irrPoly r) ++ natWord (domExp V r.2)) := by
  simp only [termsCallee, tIn, sumInput, Joins.coordInput, coordRequest]

theorem tCallee_inw_it (r : ClockRequest) :
    (termsCallee V irrPoly hI WS WC WI).inw (.inr (.inr r)) = false :: false :: (frame (List.ofFn r.1.2) ++ frame r.2.bits) := by
  simp only [termsCallee, tIn, sumInput, ClockRequest.word]

set_option maxHeartbeats 400000 in
attribute [local irreducible] baseIrr in
/-- **The term printer's run**: on `1^L 0 ++ ClockRequest.word r` (`L ≥ 1`), `termsP` prints
`frame (termsInput (termsRequest r))`. -/
theorem terms_run (a2 c2 a3 c3 : ℕ) (r : ClockRequest) (L : ℕ) (hL : 1 ≤ L)
    (fits : TFits V irrPoly (Ks := Ks) (es := es) (Kc := Kc) (ec := ec) (Ki := Ki) (ei := ei) r
      (ctxOf (termsCallee V irrPoly hI WS WC WI) (zM a2 c2 a3 c3) (List.replicate L true ++ false :: ClockRequest.word r))
      (globOf (List.replicate L true ++ false :: ClockRequest.word r))) :
    ∃ b n, Ex (ctxOf (termsCallee V irrPoly hI WS WC WI) (zM a2 c2 a3 c3)
        (List.replicate L true ++ false :: ClockRequest.word r)) (termsP V) a0 b n ∧
      b.out = RepairSource.frame (Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)) ∧
      n ≤ tCost V irrPoly hI
        (ctxOf (termsCallee V irrPoly hI WS WC WI) (zM a2 c2 a3 c3) (List.replicate L true ++ false :: ClockRequest.word r))
        (globOf (List.replicate L true ++ false :: ClockRequest.word r))
        (List.replicate L true ++ false :: ClockRequest.word r) r := by
  set inp := List.replicate L true ++ false :: ClockRequest.word r with hinp
  set C := ctxOf (termsCallee V irrPoly hI WS WC WI) (zM a2 c2 a3 c3) inp with hC
  set G := globOf inp with hG
  have hlead : leadOnes inp = L := NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_rep _ _
  have h1 : 1 ≤ leadOnes inp := by omega
  have hlt : leadOnes inp < inp.length := by rw [hlead]; simp [hinp]
  have hg : GOk C G := gokM _ a2 c2 a3 c3 inp h1
  have hCinp : C.inp = G.inp := rfl
  have SO := compS_ok hg hCinp
  have hBF := fits.bFit
  have hf1 := one_le_fieldExp V r.2
  have hcapK := cap_add G
  set f := fieldExp V r.2 with hf
  set cw := cwOf V irrPoly hI r with hcw
  set iw := machineItemsWord V irrPoly r with hiw
  set irr := irrM V irrPoly r with hirr
  suffices H : Hs C (termsP V) a0 (tCost V irrPoly hI C G inp r)
      (fun b => b.out = RepairSource.frame (Joins.termsInput (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r))) by
    obtain ⟨b, n, hx, hn, hb⟩ := H
    exact ⟨b, n, hx, hb, hn⟩
  unfold termsP
  refine Hs.mono (Hs.seq (t2 := costS G (stageR V) + (callIrrCost C f + (costS G headP + (callCoordCost C f irr
      (domExp V r.2) + ((10 * cw.length + 4) + (costS G bodyP + (callItemsCost C r.1.1 r.2.bits.length +
      ((10 * iw.length + 4) + (costS G (emitNatE (.k 0)) + costS G (.emit (.k 0)) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
      + 1) (preM_ok _ a2 c2 a3 c3 inp hlt) (fun b0 hb0 => ?_)) (by unfold tCost; rw [← hf, ← hcw, ← hiw, ← hirr]; omega)
    (fun _ h => h)
  obtain ⟨hb0, hk0⟩ := hb0
  have r0 : Rel G (FL.s0 inp) b0 := rel_s0 inp h1 b0 hb0
  -- read + params
  have hinA : G.inp.drop (FL.s0 inp).ip = ClockRequest.word r ++ [] := by
    show inp.drop (leadOnes inp + 1) = _
    rw [hlead, hinp, drop_prefix_word, List.append_nil]
  obtain ⟨pvA, outA, badA, flA, fpA⟩ := stageR_spec V (G := G) (FL.s0 inp) r [] hinA fits.pFit
  generalize hsA : evalS G (stageR V) (FL.s0 inp) = sA at pvA outA badA flA fpA
  have SA := SO (stageR V) 0 (FL.s0 inp) b0 (by norm_num) (wf_stageR V) (by rw [hsA, badA]; rfl) r0
  rw [hsA] at SA
  refine Hs.seq SA (fun b1 sp1 => ?_)
  have hk1 : b1.kin = [] := sp1.fix.2.2.1.trans hk0
  -- the Shoup call
  have hcapf : 2 ^ (f + 1) ≤ G.cap + 1 := by
    rw [hcapK]; exact Nat.pow_le_pow_right (by norm_num) (by obtain ⟨⟨hK, _⟩⟩ := fits; omega)
  have houtI : C.K.outw (.inl ⟨f, hf1⟩) = Published.Shoup.coeffWord f (irrPoly f) :=
    tCallee_outw_inl V irrPoly hI WS WC WI ⟨f, hf1⟩
  refine Hs.seq (callIrr_spec C G sA b1 sp1.rel hk1 f pvA.f (.inl ⟨f, hf1⟩) rfl (C.K.outw (.inl ⟨f, hf1⟩)) rfl
    (by rw [houtI, coeffWord_length]) (fits.bkI hf1) fits.lkI fits.wI hcapf) (fun b2 hb2 => ?_)
  obtain ⟨r2, k2⟩ := hb2
  rw [houtI, bitsValue_coeffWord] at r2
  set sA' := sA.setv 37 (modMask (irrPoly f) f) with hsA'
  have pvA' : PV V r sA' := pvA.keep V (fun i h1 h2 => by
    simp only [hsA', FS.setv_env, Function.update_apply]; rw [if_neg (by intro e; subst e; exact absurd h2 (by decide))])
  -- the header
  have hirrlt : modMask (irrPoly f) f < 2 ^ (f + 1) := WireExponent3_5.GF.ofPoly_lt _ _
  obtain ⟨pvH, h37, h41, h42, h43, EH⟩ := headP_spec V (G := G) sA' r pvA' (modMask (irrPoly f) f) (by simp [hsA'])
    hirrlt hBF.1 hBF.2.2
  generalize hsH : evalS G headP sA' = sH at pvH h37 h41 h42 h43 EH
  have SH := SO headP 0 sA' b2 (by norm_num) wf_headP (by rw [hsH, EH.bad]; simp [hsA', badA]; rfl) r2
  rw [hsH] at SH
  refine Hs.seq SH (fun b3 sp3 => ?_)
  have hk3 : b3.kin = [] := sp3.fix.2.2.1.trans k2
  -- the coordinate call
  refine Hs.seq (Hs.mono (callCoord_spec C G sH b3 sp3.rel hk3 f irr (domExp V r.2) pvH.f h37 pvH.mH h41 h42 h43
    (.inr (.inl r)) (tCallee_inw_co V irrPoly hI WS WC WI r) fits.bkCo fits.lkCo fits.wCo) le_rfl (fun _ h => h))
    (fun b4 hb4 => ?_)
  obtain ⟨r4, e4, o4, c4⟩ := hb4
  have hk4 : b4.kin = [] := by rw [e4]
  have houtC : C.K.outw (.inr (.inl r)) = RepairSource.frame cw := tCallee_outw_co V irrPoly hI WS WC WI r
  refine Hs.seq (copyOut_spec C G sH b4 r4 cw (o4.trans houtC) c4) (fun b5 hb5 => ?_)
  obtain ⟨r5, k5⟩ := hb5
  set sC : FS := { sH with out := sH.out ++ dbl cw } with hsC
  have pvC : PV V r sC := pvH.keep V (fun _ _ _ => rfl)
  -- the bank and the routing items
  have EB : Em LW sC (evalS G bodyP sC) (bodyWord V irrPoly hI r) := by
    haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨(modulusGood V irrPoly hI r).1⟩
    exact bodyP_spec V (G := G) (F := ACSP.Field2 (baseIrr V irrPoly r))
      (Joins.termsMask (tReq V irrPoly hI r) (tReq_ok V irrPoly hI r)) sC r pvC hBF
  have hbB : sH.bad = false := by rw [EH.bad]; simp [hsA', badA]; rfl
  have SB := SO bodyP 0 sC b5 (by norm_num) wf_bodyP (EB.bad.trans hbB) r5
  refine Hs.seq SB (fun b6 sp6 => ?_)
  generalize hsD : evalS G bodyP sC = sD at EB sp6
  have pvD : PV V r sD := pvC.of_wr V (W := LW) (fun i h1 h2 hi => by
    have := mem_LW.mp hi; omega) EB.env
  have hk6 : b6.kin = [] := sp6.fix.2.2.1.trans (k5.trans hk4)
  -- the items call
  have hx1 : sD.env 20 = CanonicalBinary.bitsValue (List.ofFn r.1.2) := pvD.x
  have hx2 : sD.env 21 = (List.ofFn r.1.2).length := by rw [pvD.n, List.length_ofFn]
  have hy1 : sD.env 22 = CanonicalBinary.bitsValue r.2.bits := by rw [pvD.t, CanonicalBinary.bitsValue_natBits]
  have hy2 : sD.env 23 = r.2.bits.length := pvD.tb
  refine Hs.seq (Hs.mono (callItems_spec C G sD b6 sp6.rel hk6 (List.ofFn r.1.2) r.2.bits hx1 hx2 hy1 hy2 (.inr (.inr r))
    (tCallee_inw_it V irrPoly hI WS WC WI r) fits.bkC (by rw [List.length_ofFn]; exact fits.lkC)
    (by rw [List.length_ofFn]; exact fits.wC)) (by rw [List.length_ofFn]) (fun _ h => h)) (fun b7 hb7 => ?_)
  obtain ⟨r7, -, o7, c7⟩ := hb7
  have houtT : C.K.outw (.inr (.inr r)) = RepairSource.frame iw := tCallee_outw_it V irrPoly hI WS WC WI r
  refine Hs.seq (copyOut_spec C G sD b7 r7 iw (o7.trans houtT) c7) (fun b8 hb8 => ?_)
  obtain ⟨r8, k8⟩ := hb8
  set sE : FS := { sD with out := sD.out ++ dbl iw } with hsE
  -- natWord 0
  have hK8 : 8 ≤ G.K := by have := hBF.1; omega
  obtain ⟨hc0, hl0⟩ := small_ok (G := G) hK8 (show 0 ≤ 5 by norm_num)
  have EZ := emitNatK_spec (G := G) sE 0 hc0 hl0 hBF.2.2
  have hbD : sD.bad = false := EB.bad.trans hbB
  have hbE : sE.bad = false := hbD
  have SZ := SO (emitNatE (.k 0)) 0 sE b8 (by norm_num) wf_emitNat0 (EZ.bad.trans hbE) r8
  refine Hs.seq SZ (fun b9 sp9 => ?_)
  generalize hsF : evalS G (emitNatE (.k 0)) sE = sF at EZ sp9
  have SE := SO (.emit (.k 0)) 0 sF b9 (by norm_num) (by decide) (EZ.bad.trans hbE) sp9.rel
  refine Hs.mono SE le_rfl (fun b10 sp10 => ?_)
  refine sp10.rel.out.trans ?_
  have e1 : (evalS G (.emit (.k 0)) sF).out = sF.out ++ [false] := by
    show sF.out ++ [evalE G sF (.k 0) != 0] = _
    simp only [show evalE G sF (.k 0) = 0 from Nat.zero_min _]; rfl
  have e2 : sE.out = sD.out ++ dbl iw := rfl
  have e3 : sC.out = sH.out ++ dbl cw := rfl
  have e4 : sA'.out = sA.out := rfl
  have e5 : (FL.s0 inp).out = [] := rfl
  refine e1.trans ?_
  rw [EZ.out, e2, EB.out, e3, EH.out, e4, outA, e5, termsInput_eq V irrPoly hI r]
  simp only [frame_dbl, dbl_append, List.nil_append, List.append_assoc, hcw, hiw]

end Run

end NearCubicGates.Adapters.RAMACSP.Gen
