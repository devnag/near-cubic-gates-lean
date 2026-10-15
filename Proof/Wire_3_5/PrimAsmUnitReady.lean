import Proof.Wire_3_5.PrimAsmFiltPipe

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierWalk Theorem25Completion
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe NearCubicWires.WireExponent3_5.PrimT.WalkBank

section Pop
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.PrimAsm.PopCellW
open NearCubicWires.WireExponent3_5.PrimAsm.PopRecW NearCubicWires.WireExponent3_5.PrimAsm.PopLink
open NearCubicWires.WireExponent3_5.PrimAsm.PopCellNum NearCubicWires.WireExponent3_5.PrimAsm.PopBlockW
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.PrimAsm.PopParams
open NearCubicWires.WireExponent3_5.PrimAsm.LevelW NearCubicWires.WireExponent3_5.PrimAsm.Arith

/-- **A POP-ready cell state**: the hypotheses of `PopPipe.popPipe` on one state (the walk-bank producer's inputs, C5's builder state, the POP cell's numbers, the empty record stream, the output `out ++ [false]` at `|out|`). -/
structure PopReady (cap : ℕ) (W : WalkBankProducer) (σ : WState (LNS W.x) LNR) (out : List Bool) (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off Mlab lw CAP LL R cp RW LW : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1)) (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length) : Prop where
  hlen : (sliceLabs r4 G off L).length = 4 * L
  hnest : ∀ h j i, Pl.base.inLevel h (j + 1) i = true → Pl.base.inLevel h j i = true
  hlw : lw = lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J L + Pl.M + 2
  hCAP : CAP = labSum (sliceLabs r4 G off L)
  hLL : LL = ((sliceLabs r4 G off L).flatMap labE).length
  hR : R = PopCap.popKc L (3 * lbP Pl) (capP Pl L) CAP (PopNums.blF L (3 * lbP Pl) (capP Pl L) CAP LL lw Pl.M) + 1
  hcp : cp = PopCap.popCapB Pl.walkLen R (PopCap.popPW L (3 * lbP Pl) Mlab)
  hok : ∀ st ∈ popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s, StateOk Pl.walkLen R cp st
  hRW : 2 * sideB Pl.base.rank + 1 ≤ RW
  hLW : 2 * sideB Pl.base.rank + 1 ≤ LW
  hpad : padB Pl.base.rank ≤ 1
  hps : padB Pl.base.rank ≤ sideB Pl.base.rank
  hsd : 2 * Pl.base.rank - 1 + Pl.base.rank ≤ 2 * sideB Pl.base.rank - padB Pl.base.rank
  hlb : 1 ≤ Pl.base.rank
  hnJ : Pl.base.J + 1 ≤ Pl.base.rank + 1
  hcapC : 8 * sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ cap
  hO : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < cap
  hout : σ.st (sk W.x 1) = out ++ [false]
  houth : σ.sh (sk W.x 1) = out.length
  hrec : σ.st (sk W.x 3) = []
  hrec0 : σ.sh (sk W.x 3) = 0
  hD : σ.sh (sk W.x 4) = (σ.st (sk W.x 4)).length
  hin : ∀ j : Fin 14, σ.st (sk W.x (portT j)) = inPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW (seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e) j
  hh : ∀ j : Fin 14, σ.sh (sk W.x (portT j)) = 0
  hsc : ∀ k : Fin W.x, σ.st (sT W.x k) = []
  hsh : ∀ k : Fin W.x, σ.sh (sT W.x k) = 0
  hC5 : ∀ i : Fin 12, i.val ≠ 0 → i.val ≠ 2 → σ.st (fsC W.x i) = (yC Pl e L RW LW).st i ∧ σ.sh (fsC W.x i) = 0
  hC5r : ∀ r, σ.val (frC r) = (yC Pl e L RW LW).val r
  hcell : σ.cell = (yC Pl e L RW LW).cell
  hscr : ∀ j : Fin (IPL (negFam F35).t + 1), j.val ≠ 0 → j.val ≠ 45 → σ.st (tmapQ W.x j) = [] ∧ σ.sh (tmapQ W.x j) = 0
  h0 : σ.val (Xe Pe 0) = 0
  h1 : σ.val (Xe Pe 1) = r4
  h2 : σ.val (Xe Pe 2) = G
  h3 : σ.val (Xe Pe 3) = off
  h4 : σ.val (Xe Pe 4) = L
  h20 : σ.val (Xe Pe 20) = CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)
  h21 : σ.val (Xe Pe 21) = Pl.base.J
  h44 : σ.val (Xe Pe 44) = Pl.M
  h45 : σ.val (Xe Pe 45) = L
  h50 : σ.val (Xe Pe 50) = if sgn then 1 else 0
  h52 : σ.val (Xe Pe 52) = Pl.walkLen
  h53 : σ.val (Xe Pe 53) = SupplierWalk.majorityThreshold Pl.walkLen
  h63 : σ.val (Xe Pe 63) = s.val
  hzA : ∀ k : Fin 64, (5 ≤ k.val ∧ k.val ≤ 19) ∨ (22 ≤ k.val ∧ k.val ≤ 43) ∨ (46 ≤ k.val ∧ k.val ≤ 49) ∨ k.val = 51 ∨ (54 ≤ k.val ∧ k.val ≤ 62) → σ.val (Xe Pe k) = 0
  hz : ∀ j : Fin 200, 64 ≤ j.val → j.val ≤ 170 → σ.val (Pe j) = 0
  h180 : σ.val (Pe 180) = Mlab
  hM : off + L + (r4 + 4) * G ≤ Mlab
  hcap : lvCap (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J Pl.base.J ≤ cap
  hdc : 3 * lbP Pl ≤ cap
  hJc : Pl.base.J + 1 ≤ cap
  hSc : CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) ≤ cap
  hlwc : lw ≤ cap
  hMc : Pl.M ≤ cap
  hcL : 4 * L ≤ cap
  hcap3 : L * (4 * (4 * Mlab + 4)) + 5 + L * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) + 4 * (2 * Mlab + 10) + 7 * Mlab + r4 + G + off + L + 20 ≤ cap
  hac3 : CAP + LL ≤ cap
  hQc : (8 * L + 2) ^ (3 * lbP Pl) * (8 * L + 2) + 2 ≤ cap
  hc4 : capP Pl L + 8 ≤ cap
  hin2 : L + capP Pl L + Pl.M + Mlab + Pl.walkLen ≤ cap
  hnum : ∀ i, evalL (vIn L (3 * lbP Pl) (capP Pl L) CAP LL Pl.M Mlab Pl.walkLen lw ((8 * L + 2) ^ (3 * lbP Pl))) PopNums.numOps i ≤ cap
  h2c : 2 ≤ cap
  hcV : (Pl.base.J + 1) * (2 * L + 1) + 1 ≤ cap
  hcT : Pl.walkLen * ((Pl.base.J + 1) * (2 * L + 1) + 1) ≤ cap
  hθc : SupplierWalk.majorityThreshold Pl.walkLen ≤ cap
  hRc1 : R + 1 ≤ cap
  hcpc : cp ≤ cap
  hbig : (frame (popRowRec Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) R (R + 1) cp (oneWC Pl s) (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s))).length + 2 + labCapA (4 * L) (3 * lbP Pl) + (pieceA (4 * L) (3 * lbP Pl)).length + labCapB r4 G off L Mlab ≤ cap

theorem popPipe_ready (cap : ℕ) (W : WalkBankProducer) (σ : WState (LNS W.x) LNR) (out : List Bool) (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off Mlab lw CAP LL R cp RW LW : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1)) (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length) (h : PopReady cap W σ out Pl e L r4 G off Mlab lw CAP LL R cp RW LW sgn s hlabs) :
    ∃ σF m, Step (popPipeM W) m (wenc cap σ).H (wenc cap σ).A (wenc cap σF).H (wenc cap σF).A ∧ σF.st (sk W.x 1) = out ++ (popRefC Pl e L sgn (sliceLabs r4 G off L) s).flatMap (fun t => true :: ListMachine.Rec.termWord t) ++ [false] ∧ σF.sh (sk W.x 1) = (out ++ (popRefC Pl e L sgn (sliceLabs r4 G off L) s).flatMap (fun t => true :: ListMachine.Rec.termWord t)).length ∧ (∀ k : Fin 161, (k.val = 0 ∨ k.val = 2) → σF.st (sk W.x k) = σ.st (sk W.x k) ∧ σF.sh (sk W.x k) = σ.sh (sk W.x k)) ∧ m ≤ popPipeBound cap Pl e L r4 G off Mlab lw R cp RW LW sgn s hlabs :=
  popPipe cap W σ out Pl e L r4 G off Mlab lw CAP LL R cp RW LW sgn s hlabs h.hlen h.hnest h.hlw h.hCAP h.hLL h.hR h.hcp h.hok h.hRW h.hLW h.hpad h.hps h.hsd h.hlb h.hnJ h.hcapC h.hO h.hout h.houth h.hrec h.hrec0 h.hD h.hin h.hh h.hsc h.hsh h.hC5 h.hC5r h.hcell h.hscr h.h0 h.h1 h.h2 h.h3 h.h4 h.h20 h.h21 h.h44 h.h45 h.h50 h.h52 h.h53 h.h63 h.hzA h.hz h.h180 h.hM h.hcap h.hdc h.hJc h.hSc h.hlwc h.hMc h.hcL h.hcap3 h.hac3 h.hQc h.hc4 h.hin2 h.hnum h.h2c h.hcV h.hcT h.hθc h.hRc1 h.hcpc h.hbig

end Pop

section Filt
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **A FILTER-ready cell state**: the hypotheses of `FiltPipe.filtPipe` on one state (the unary field degree, the trace mask's zero words, the walk-bank producer's inputs, C5's stage-6 builder words and registers, the FILTER numbers, the empty record stream, the output `out ++ [false]` at `|out|`). -/
structure FiltReady (cap : ℕ) (W : WalkBankProducer) (σ : WState (LNS W.x) LNR) (out : List Bool) (P : GapParams) (e : GapSeed P) (L r4 G off Mlab RW LW : ℕ) (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)) : Prop where
  hvert : ∀ i, (sample.vertex i).1.val = (e.vertex i).1.val
  hU : 1 ≤ P.cap
  hlen : (sliceLabs r4 G off L).length = 4 * L
  hlabs : 4 * L ≤ (sliceLabs r4 G off L).length
  hRW : 2 * (wOf P.fieldBits P.labelBits * 128) + 1 ≤ RW
  hLW : 2 * (wOf P.fieldBits P.labelBits * 128) + 1 ≤ LW
  hcap6 : 2 * (wOf P.fieldBits P.labelBits * 128) + 4 * P.labelBits + 2 * P.fieldBits + L + 10 ≤ cap
  hO6 : (2 * (P.errExp / 4) + 1) * (128 * (2 * L + 2) + 2) + 12 < cap
  hcapT : 2 * P.fieldBits + 2 ≤ cap
  hout : σ.st (sk W.x 1) = out ++ [false]
  houth : σ.sh (sk W.x 1) = out.length
  hrec : σ.st (sk W.x 3) = []
  hrec0 : σ.sh (sk W.x 3) = 0
  hmod : σ.st (sk W.x 91) = List.replicate P.fieldBits true
  hmsc : ∀ j : Fin 17, j.val ≠ 0 → σ.st (tmapM W.x j) = []
  hmh : ∀ j : Fin 17, σ.sh (tmapM W.x j) = 0
  htau : ∀ j : Fin 7, 1 ≤ j.val → σ.st (SmT W.x j) = frame (SignedSortKey.binary P.fieldBits 0) ∧ σ.sh (SmT W.x j) = 0
  htauR : ∀ j : Fin 9, j ≠ 4 → σ.val (RgT j) = 0
  htauR4 : σ.val (RgT 4) = P.fieldBits
  hin : ∀ j : Fin 14, σ.st (sk W.x (portT j)) = inPorts (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW (seedIndexWord (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) sample) j
  hh : ∀ j : Fin 14, σ.sh (sk W.x (portT j)) = 0
  hsc : ∀ k : Fin W.x, σ.st (sT W.x k) = []
  hsh : ∀ k : Fin W.x, σ.sh (sT W.x k) = 0
  hC5 : ∀ i : Fin 12, 4 ≤ i.val → σ.st (fsF W.x i) = (yFC P L RW LW sample).st i ∧ σ.sh (fsF W.x i) = 0
  hC51 : σ.st (sk W.x 80) = [] ∧ σ.sh (sk W.x 80) = 0
  hC5r : ∀ r, σ.val (frC r) = (yFC P L RW LW sample).val r
  hcell : σ.cell = false
  hF0 : σ.val (FR 0) = 0
  hF1 : σ.val (FR 1) = r4
  hF2 : σ.val (FR 2) = G
  hF3 : σ.val (FR 3) = off
  hF4 : σ.val (FR 4) = L
  hFz : ∀ i : Fin 20, 5 ≤ i.val → i.val ≤ 12 → σ.val (FR i) = 0
  hF13 : σ.val (FR 13) = 4 * L
  hF14 : σ.val (FR 14) = filtDeg (filterTable P e L)
  hF15 : σ.val (FR 15) = majorityThreshold P.walkLen
  hF16 : σ.val (FR 16) = cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 1
  hF17 : σ.val (FR 17) = (tableWord (filterTable P e L)).length
  hF18 : σ.val (FR 18) = 0
  hF19 : σ.val (FR 19) = 0
  hM : off + L + (r4 + 4) * G ≤ Mlab
  cA : 4 * (8 * (4 * L) + 6) + 30 + 4 * filtDeg (filterTable P e L) + 6 + 4 * L + filtDeg (filterTable P e L) + 10 ≤ cap
  cB : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6)) + ((sliceLabs r4 G off L).flatMap labE).length + 4 * labSum (sliceLabs r4 G off L) + 10 + L * (4 * (4 * Mlab + 4)) + L * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) + 4 * (2 * Mlab + 10) + 7 * Mlab + r4 + G + off + L + labSum (sliceLabs r4 G off L) + 40 ≤ cap
  cC : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6) + (((sliceLabs r4 G off L).flatMap labE).length + 6 + 4 * labSum (sliceLabs r4 G off L) + 4)) + 4 * (tableWord (filterTable P e L)).length + 2 + (tableWord (filterTable P e L)).length + 5 ≤ cap
  cD : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6) + (((sliceLabs r4 G off L).flatMap labE).length + 6 + 4 * labSum (sliceLabs r4 G off L) + 4) + (4 * (tableWord (filterTable P e L)).length + 2)) + 4 * majorityThreshold P.walkLen + 6 + 8 * (4 * (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 1) + 2) + 7 + majorityThreshold P.walkLen + cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 10 ≤ cap
  crw : (frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L))).length ≤ cap
  hscr : ∀ j : Fin (1 + (1 + (14 + F37.t) + 1)), j.val ≠ 0 → j.val ≠ 12 → σ.st (tmapR W.x j) = [] ∧ σ.sh (tmapR W.x j) = 0

theorem filtPipe_ready (cap : ℕ) (W : WalkBankProducer) (σ : WState (LNS W.x) LNR) (out : List Bool) (P : GapParams) (e : GapSeed P) (L r4 G off Mlab RW LW : ℕ) (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)) (h : FiltReady cap W σ out P e L r4 G off Mlab RW LW sample) :
    ∃ σF m, Step (filtPipeM W) m (wenc cap σ).H (wenc cap σ).A (wenc cap σF).H (wenc cap σF).A ∧ σF.st (sk W.x 1) = out ++ (filtRefC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L)).flatMap (fun t => true :: ListMachine.Rec.termWord t) ++ [false] ∧ σF.sh (sk W.x 1) = (out ++ (filtRefC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L)).flatMap (fun t => true :: ListMachine.Rec.termWord t)).length ∧ (∀ k : Fin 161, (k.val = 0 ∨ k.val = 2) → σF.st (sk W.x k) = σ.st (sk W.x k) ∧ σF.sh (sk W.x k) = σ.sh (sk W.x k)) ∧ m ≤ filtPipeBound P e L r4 G off RW LW :=
  filtPipe cap W σ out P e L r4 G off Mlab RW LW sample h.hvert h.hU h.hlen h.hlabs h.hRW h.hLW h.hcap6 h.hO6 h.hcapT h.hout h.houth h.hrec h.hrec0 h.hmod h.hmsc h.hmh h.htau h.htauR h.htauR4 h.hin h.hh h.hsc h.hsh h.hC5 h.hC51 h.hC5r h.hcell h.hF0 h.hF1 h.hF2 h.hF3 h.hF4 h.hFz h.hF13 h.hF14 h.hF15 h.hF16 h.hF17 h.hF18 h.hF19 h.hM h.cA h.cB h.cC h.cD h.crw h.hscr

end Filt

end NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
