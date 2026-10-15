import Proof.Wire_3_5.SeedFixJStages

/-! # C4.Sb, machine part 18: one enumeration cell

The cell of counter `j`: split the counter, write the cell words, test the labels; if every label is below `Q`, write
the constraint records and eliminate; if the system is consistent, write the coefficient, multiply in the eight
entries and append the group to the output. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)
open NearCubicWires.WireExponent3_5.JoinElimination NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)
open Split Cells Valid Cons FetchAll FetchCells Emit JBank JStages

namespace JBody

/-! ## The coefficient, the eight fetches, the emission -/

noncomputable def cfeM := Composition.machine (Composition.machine (RecoveryFocus.machine slCoef coefM)
  (RecoveryFocus.machine slFetch fetchCellsM)) (RecoveryFocus.machine slEmit emitM)

def coefT (bs : List Bool) (R2 e : ℕ) : SExpr := [((if parity bs then -1 else 1) * 2 ^ (R2 * cnt bs bs.length + e), [])]

/-- The accumulator's state after the coefficient. -/
def fs0 (bs : List Bool) (R2 e : ℕ) (T : JT) : FoldSt := ⟨coefT bs R2 e, T.ACC, T.Y, T.ROW, T.AT⟩

theorem overlay_exprWord (G : SExpr) (B : List Bool) :
    overlay (exprWord G) B = exprWord G ++ B.drop (exprWord G).length := rfl

theorem cfe_run (T : JT) (bs : List Bool) (R2 : ℕ) (sg0 : Bool) (rus xs : List Bool) (e : ℕ)
    (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool)) (tailB tailC tw r8s : List Bool)
    (c0 c1 c2 c3 c4 c5 c6 c7 W e0 : ℕ) (f0 : Bool) (V : SExpr) (OB : List Bool)
    (hBT : T.BT = frame bs) (hONES : T.ONES8 = frame (List.replicate bs.length true)) (hSG : T.SG = [sg0])
    (hRK2 : T.RK2 = List.replicate R2 true ++ false :: rus) (hXE : T.XE = List.replicate e true ++ false :: xs)
    (hL0 : T.L0 = List.replicate c0 false) (hL1 : T.L1 = List.replicate c1 false) (hL2 : T.L2 = List.replicate c2 false)
    (hL3 : T.L3 = List.replicate c3 false) (hL4 : T.L4 = List.replicate c4 false) (hL5 : T.L5 = List.replicate c5 false)
    (hL6 : T.L6 = List.replicate c6 false) (hL7 : T.L7 = List.replicate c7 false)
    (hBAT : T.BAT = blockWord ents ++ tailB) (hCNT : T.CNT = frame (binary W 0)) (hTGT : T.TGT = frame (binary W e0))
    (hFLAG : T.FLAG = [f0]) (hONE : T.ONE = [true]) (hTW : T.TW = frame tw)
    (hR8 : T.R8 = List.replicate es.length true ++ false :: r8s) (hCL : T.CL = cs.flatMap frame ++ tailC)
    (hOUT : T.OUT = overlay (exprWord V) OB)
    (hcL : R2 * (2 + 2) + 1 ≤ c0) (hcF : 2 * bs.length + 1 ≤ c1) (hcM : coefCost bs R2 e ≤ 2 * c2 + 2)
    (ok : FcOk (fs0 bs R2 e T) ents es c0 c1 c2 c3 W c4 c5)
    (hlc : cs.length = es.length)
    (hcs : ∀ k (hk : k < es.length) (hk' : k < cs.length), binary W es[k] = cs[k] ++ tw)
    (hw : ∀ c ∈ cs, c.length + tw.length = W) (hcG : ∀ c ∈ cs, tgtInnerCost c.length tw.length ≤ c6)
    (hcH : ((List.range (es.length - 0)).map
      (fun i => fcCost (fs0 bs R2 e T) ents es cs tw W (0 + i) + 2)).sum + 1 ≤ c7)
    (hcE : emitInnerCost (exprWord V).length
      (exprWord (fcSt (fs0 bs R2 e T) ents es es.length).A).length ≤ c0) :
    Step cfeM (coefCost bs R2 e + 1 + fetchCellsCost (fs0 bs R2 e T) ents es cs tw W + 1 +
        (2 * emitInnerCost (exprWord V).length
          (exprWord (fcSt (fs0 bs R2 e T) ents es es.length).A).length + 2))
      (fun _ => 0) T.vec (fun _ => 0)
      { T with SG := [parity bs],
               ACC := (fcSt (fs0 bs R2 e T) ents es es.length).X,
               Y := (fcSt (fs0 bs R2 e T) ents es es.length).Y,
               ROW := (fcSt (fs0 bs R2 e T) ents es es.length).ROW,
               AT := (fcSt (fs0 bs R2 e T) ents es es.length).AT,
               TGT := frame (binary W (tgAt e0 es es.length)), FLAG := [flAt f0 ents.length es es.length],
               OUT := overlay (exprWord (V ++ (fcSt (fs0 bs R2 e T) ents es es.length).A))
                 OB }.vec := by
  set s0 : FoldSt := fs0 bs R2 e T
  have h1 := stage_coef T bs R2 sg0 rus xs e c0 c1 c2 hBT hONES hSG hRK2 hXE hL0 hL1 hL2 hcL hcF hcM
  set T1 := { T with SG := [parity bs],
                     ACC := overlay (exprWord [((if parity bs then -1 else 1) * 2 ^ (R2 * cnt bs bs.length + e), [])]) T.ACC }
  have h2 := stage_fetch T1 s0 ents es cs tailB tailC tw r8s c0 c1 c2 c3 W e0 c4 c5 c6 c7 f0 hBAT rfl rfl rfl rfl hL0 hL1
    hL2 hL3 hCNT hTGT hFLAG hONE hL4 hL5 hTW hR8 hL6 hL7 ok hCL hlc hcs hw hcG hcH
  set sf := fcSt s0 ents es es.length
  set T2 := { T1 with ACC := sf.X, Y := sf.Y, ROW := sf.ROW, AT := sf.AT,
                      TGT := frame (binary W (tgAt e0 es es.length)), FLAG := [flAt f0 ents.length es es.length] }
  have h3 := stage_emit T2 V sf.A (sf.Xb.drop (exprWord sf.A).length) OB c0 (overlay_exprWord sf.A sf.Xb) hOUT hL0 hcE
  exact (h1.seq h2).seq h3

/-! ## Every cost and capacity of the fetches depends on the accumulator only through its product -/

theorem foldl_step_A : ∀ (L : List SExpr) (s s' : FoldSt), s.A = s'.A →
    (L.foldl FoldSt.step s).A = (L.foldl FoldSt.step s').A
  | [], _, _, h => h
  | V :: L, s, s', h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_step_A L _ _ (by simp only [FoldSt.step]; rw [h])

theorem foldAt_A_eq (s s' : FoldSt) (h : s.A = s'.A) (rs : List SExpr) (r : ℕ) :
    (foldAt s rs r).A = (foldAt s' rs r).A := foldl_step_A _ s s' h

theorem rowCaps_eq (s s' : FoldSt) (h : s.A = s'.A) (V : SExpr) (cI cT cA cC : ℕ) :
    RowCaps s V cI cT cA cC = RowCaps s' V cI cT cA cC := by
  unfold RowCaps; rw [h]

theorem rowsMulCost_eq (s s' : FoldSt) (h : s.A = s'.A) (rs : List SExpr) : rowsMulCost s rs = rowsMulCost s' rs := by
  unfold rowsMulCost fRowCost
  have e : ∀ i, (foldAt s rs i).A = (foldAt s' rs i).A := fun i => foldAt_A_eq s s' h rs i
  simp only [e]

theorem fetchCost_eq (s s' : FoldSt) (h : s.A = s'.A) (ents : List (List SExpr)) (W e : ℕ) :
    fetchCost s ents W e = fetchCost s' ents W e := by
  unfold fetchCost entCost
  have e : ∀ rs, rowsMulCost s rs = rowsMulCost s' rs := fun rs => rowsMulCost_eq s s' h rs
  simp only [e]

theorem fcSt_A_eq (s s' : FoldSt) (h : s.A = s'.A) (ents : List (List SExpr)) (es : List ℕ) (k : ℕ) :
    (fcSt s ents es k).A = (fcSt s' ents es k).A := by
  unfold fcSt
  generalize es.take k = L
  induction L generalizing s s' with
  | nil => exact h
  | cons e L ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (foldAt_A_eq s s' h _ _)

theorem fcCost_eq (s s' : FoldSt) (h : s.A = s'.A) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool))
    (tw : List Bool) (W k : ℕ) : fcCost s ents es cs tw W k = fcCost s' ents es cs tw W k := by
  unfold fcCost fetchAllCost
  rw [fetchCost_eq _ _ (fcSt_A_eq s s' h ents es k)]

theorem fetchCellsCost_eq (s s' : FoldSt) (h : s.A = s'.A) (ents : List (List SExpr)) (es : List ℕ)
    (cs : List (List Bool)) (tw : List Bool) (W : ℕ) :
    fetchCellsCost s ents es cs tw W = fetchCellsCost s' ents es cs tw W := by
  unfold fetchCellsCost
  have e : ∀ i, fcCost s ents es cs tw W i = fcCost s' ents es cs tw W i := fun i => fcCost_eq s s' h ents es cs tw W i
  simp only [e]

theorem fcOk_of (s s' : FoldSt) (h : s.A = s'.A) (ents : List (List SExpr)) (es : List ℕ) (cI cT cA cC W cE cF : ℕ)
    (ok : FcOk s ents es cI cT cA cC W cE cF) : FcOk s' ents es cI cT cA cC W cE cF where
  hN := ok.hN
  he := ok.he
  hcE := ok.hcE
  h0 := fun k hk => by rw [← fcSt_A_eq s s' h]; exact ok.h0 k hk
  hrs := ok.hrs
  hc := fun k hk r hr => by
    rw [← rowCaps_eq _ _ (foldAt_A_eq _ _ (fcSt_A_eq s s' h ents es k) _ r)]
    exact ok.hc k hk r hr
  hcF := fun k hk => by rw [← fetchCost_eq _ _ (fcSt_A_eq s s' h ents es k)]; exact ok.hcF k hk

/-- The accumulator's state with only its product (the canonical instance of the capacity hypotheses). -/
def aOnly (A : SExpr) : FoldSt := ⟨A, [], [], [], []⟩

/-! ## The run's parameters, the cell's state, the bank at a counter value -/

open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Sampler

/-- A run's parameters: the seed parameters, the prefix, the elimination's widths, the logs' capacities, the batch, the
state word's width and the state, the output's backing. -/
structure JCtx where
  P : SeedParams
  plen : ℕ
  pfx : ℕ
  m : ℕ
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
  c6 : ℕ
  c7 : ℕ
  cK : ℕ
  cC : ℕ
  TWd : ℕ
  t : ℕ
  ents : List (List SExpr)
  tailB : List Bool
  OB : List Bool

/-- The cell's state carried between counter values: the scratch the blocks leave behind. -/
structure JState where
  CT : List Bool
  R : Regs
  O : List Bool
  W : List Bool
  P : List Bool
  g : Bool
  XE : List Bool
  sg : Bool
  ACC : List Bool
  Y : List Bool
  ROW : List Bool
  AT : List Bool
  tg : ℕ
  fl : Bool

namespace JCtx
variable (X : JCtx)

/-- The target width: the cell word, then the state word. -/
def Wt : ℕ := 2 * X.P.kh + X.TWd
/-- The counter width. -/
def w : ℕ := 8 + 8 * X.P.ell + 8 * X.P.kh
/-- The bound `Q − 1`. -/
def q : List Bool := binary X.P.ell (X.P.Q - 1)

def asJ (j : ℕ) : List (List Bool) := alphasOf X.P.ell j
def csJ (j : ℕ) : List (List Bool) := (List.finRange 8).map (cellW X.P j)
def validJ (j : ℕ) : Bool := (X.asJ j).all (cmpQ X.q)
def consJ (j : ℕ) : List (ℕ × ℕ) := consL X.P.N (aOf X.P j) (fun k => cellOf (by norm_num) (wOf X.P j) k) (bOf j)
def ggJ (j : ℕ) : Bool × ℕ :=
  gauss (8 * X.P.ell - X.plen) (system X.P.modulus X.P.ell 8 (2 * X.P.kh) X.plen X.pfx (X.consJ j))
def eJ (j : ℕ) : ℕ := 8 * X.P.ell - X.plen - (X.ggJ j).2
def esJ (j : ℕ) : List ℕ :=
  (List.finRange 8).map fun k => cellNumC (cellOf (by norm_num) (wOf X.P j) k) + X.P.N ^ 2 * X.t
def cfJ (j : ℕ) : SExpr := coefT (binary 8 j) (2 * X.P.kh) (X.eJ j)
def rowsJ (j : ℕ) : List SExpr := (X.esJ j).flatMap fun e => X.ents.getD e []

/-- The group the cell emits: empty unless the labels are valid and the system consistent. -/
def emitJ (j : ℕ) : SExpr := if X.validJ j = true ∧ (X.ggJ j).1 = true then sfold (X.cfJ j) (X.rowsJ j) else []

/-- The output after the counter values below `j`. -/
def Vacc (j : ℕ) : SExpr := (List.range j).flatMap X.emitJ

def alW (j : ℕ) : List Bool := (X.asJ j).flatMap frame ++ [false]
def dgW (j : ℕ) : List Bool := (digsOf X.P.ell X.P.kh j).flatMap frame ++ [false]
def dnW (j : ℕ) : List Bool :=
  ((digsOf X.P.ell X.P.kh j).tail ++ [(digsOf X.P.ell X.P.kh j).headD []]).flatMap frame ++ [false]
def clW (j : ℕ) : List Bool := (X.csJ j).flatMap frame ++ [false]

/-- The bank after counter value `j`'s fields, with state `S`, output `V` and counter `cnt`. -/
def jt (j : ℕ) (S : JState) (V : SExpr) (cnt : ℕ) : JT where
  BT := frame (binary 8 j)
  AL := X.alW j
  DG := X.dgW j
  DN := X.dnW j
  CL := X.clW j
  LAB := frame ((X.asJ j).getD 7 [])
  QM := frame X.q
  CC := [cmpQ X.q ((X.asJ j).getD 7 [])]
  V := [X.validJ j]
  ONE := [true]
  CT := S.CT
  ONES8 := frame (List.replicate 8 true)
  SG := [S.sg]
  ACC := S.ACC
  Y := S.Y
  ROW := S.ROW
  AT := S.AT
  BAT := blockWord X.ents ++ X.tailB
  CNT := frame (binary X.Wt 0)
  TGT := frame (binary X.Wt S.tg)
  FLAG := [S.fl]
  TW := frame (binary X.TWd X.t)
  OUT := overlay (exprWord V) X.OB
  R8 := List.replicate 8 true ++ [false]
  RL := List.replicate X.P.ell true ++ [false]
  RK := List.replicate X.P.kh true ++ [false]
  R1 := List.replicate 1 true ++ [false]
  R7 := List.replicate 7 true ++ [false]
  RK2 := List.replicate (2 * X.P.kh) true ++ [false]
  RA := frame (binary X.P.ell S.R.a)
  RC := frame (binary X.P.ell S.R.c)
  RT := S.R.T ++ List.replicate X.m false
  PW := frame (binary X.P.ell X.P.modulus)
  FL := S.R.fl
  RX := frame (binary X.P.ell S.R.x)
  RZ := frame (binary X.P.ell S.R.z)
  Z9 := [false]
  PFX := frame (binary X.plen X.pfx)
  MC := frame (binary X.P.ell S.R.mc)
  RR := S.R.r
  RB := [S.R.b]
  Z18 := [false]
  O := S.O
  ONEW := frame (binary X.P.ell 1)
  W := S.W
  P := S.P
  K := pad X.cK []
  CC2 := pad X.cC (List.replicate (8 * X.P.ell - X.plen) true)
  G := [S.g]
  XE := S.XE
  L0 := List.replicate X.c0 false
  L1 := List.replicate X.c1 false
  L2 := List.replicate X.c2 false
  L3 := List.replicate X.c3 false
  L4 := List.replicate X.c4 false
  L5 := List.replicate X.c5 false
  L6 := List.replicate X.c6 false
  L7 := List.replicate X.c7 false
  C := binary (X.w + 1) cnt
  CW := List.replicate (X.w + 1) false

/-- The state after the elimination of counter value `j`. -/
def elimSt (j : ℕ) (S : JState) : JState :=
  { S with CT := overlay (consOut (binary 8 j) (X.asJ j) (X.csJ j) (binary 8 j).length ++ [false]) S.CT,
           R := regsAt X.P.modulus X.P.ell 8 (2 * X.P.kh) X.plen S.R (X.consJ j) (X.consJ j).length,
           O := ElimX.elimO X.P.modulus X.P.ell 8 (2 * X.P.kh) X.plen X.pfx (X.consJ j) S.O S.W S.P,
           W := ElimX.elimW X.P.modulus X.P.ell 8 (2 * X.P.kh) X.plen X.pfx (X.consJ j) S.O S.W S.P,
           P := ElimX.elimP X.P.modulus X.P.ell 8 (2 * X.P.kh) X.plen X.pfx (X.consJ j) S.O S.W S.P,
           g := (X.ggJ j).1,
           XE := overlay (List.replicate (X.eJ j) true ++ [false]) S.XE }

/-- The accumulator's final state of counter value `j`. -/
def sfJ (j : ℕ) (S : JState) : FoldSt := fcSt ⟨X.cfJ j, S.ACC, S.Y, S.ROW, S.AT⟩ X.ents (X.esJ j) (X.esJ j).length

/-- The state after the group of counter value `j`. -/
def grpSt (j : ℕ) (S : JState) : JState :=
  { X.elimSt j S with sg := parity (binary 8 j), ACC := (X.sfJ j S).X, Y := (X.sfJ j S).Y, ROW := (X.sfJ j S).ROW,
                      AT := (X.sfJ j S).AT, tg := tgAt S.tg (X.esJ j) (X.esJ j).length,
                      fl := flAt S.fl X.ents.length (X.esJ j) (X.esJ j).length }

/-- The cell's state after counter value `j`. -/
def jNext (j : ℕ) (S : JState) : JState :=
  if X.validJ j = true then (if (X.ggJ j).1 = true then X.grpSt j S else X.elimSt j S) else S

end JCtx

/-! ## The group of a valid counter value -/

noncomputable def groupM := Composition.machine (Composition.machine (RecoveryFocus.machine slCons consM)
  (RecoveryFocus.machine slElim elimM)) (branchM (48 : Fin 60) cfeM (idle 60))

theorem overlay_term (x B : List Bool) : overlay (x ++ [false]) B = x ++ false :: B.drop (x.length + 1) := by
  simp [overlay]

theorem esJ_length (X : JCtx) (j : ℕ) : (X.esJ j).length = 8 := by simp [JCtx.esJ]
theorem csJ_length (X : JCtx) (j : ℕ) : (X.csJ j).length = 8 := by simp [JCtx.csJ]

theorem asJ_width (X : JCtx) (j : ℕ) : ∀ a ∈ X.asJ j, a.length = X.P.ell := fields8_width _ _
theorem csJ_width (X : JCtx) (j : ℕ) : ∀ c ∈ X.csJ j, c.length = 2 * X.P.kh := by
  intro c hc
  simp only [JCtx.csJ, List.mem_map] at hc
  obtain ⟨k, _, rfl⟩ := hc
  exact binary_length _ _

theorem cons_tape (X : JCtx) (j : ℕ) (B : List Bool) :
    overlay (consOut (binary 8 j) (X.asJ j) (X.csJ j) (binary 8 j).length ++ [false]) B =
      consTape X.P.ell (2 * X.P.kh) (X.consJ j)
        (B.drop ((consOut (binary 8 j) (X.asJ j) (X.csJ j) (binary 8 j).length).length + 1)) := by
  rw [overlay_term, consTape]
  congr 1
  rw [binary_length]
  exact cons_eq X.P j

/-- The group's cost: records, elimination, then the coefficient, the fetches and the emission if consistent. -/
noncomputable def groupCost (X : JCtx) (j : ℕ) (V : SExpr) : ℕ :=
  (2 * consInnerCost 8 X.P.ell (2 * X.P.kh) + 2) + 1 + elimCost X.P.ell 8 (2 * X.P.kh) X.plen (X.consJ j).length + 1 +
    ((if (X.ggJ j).1 = true then
      coefCost (binary 8 j) (2 * X.P.kh) (X.eJ j) + 1 +
        fetchCellsCost (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.csJ j) (binary X.TWd X.t) X.Wt + 1 +
        (2 * emitInnerCost (exprWord V).length (exprWord (fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length + 2)
      else 0) + 2)

theorem sfJ_A (X : JCtx) (j : ℕ) (S : JState) (hv : X.validJ j = true) (hg : (X.ggJ j).1 = true) :
    (X.sfJ j S).A = X.emitJ j := by
  unfold JCtx.sfJ JCtx.emitJ
  rw [fcSt_A, if_pos ⟨hv, hg⟩]
  rfl

theorem group_run (X : JCtx) (j : ℕ) (S : JState) (V : SExpr) (cnt : ℕ) (hv : X.validJ j = true)
    (hp : GF.ModulusOk X.P.modulus X.P.ell) (hR : S.R.Ok X.P.ell 8) (hm : 1 ≤ X.m) (hplen : X.plen ≤ 8 * X.P.ell)
    (hcons : ∀ con ∈ X.consJ j, con.1 < 2 ^ X.P.ell)
    (hkc : consInnerCost 8 X.P.ell (2 * X.P.kh) ≤ X.c0)
    (hcap : 2 * X.P.ell + 2 ≤ X.c0) (hcap2 : X.P.ell * (innerCost X.P.ell + 2) + 1 ≤ X.c1)
    (hcap2' : X.P.ell * (mulIterCost X.P.ell + 2) + 1 ≤ X.c1) (hcap2'' : X.plen * (phACost X.P.ell + 2) + 1 ≤ X.c1)
    (hcap3 : tableCost X.P.ell 8 ≤ X.c2) (hcap3' : passesCost X.P.ell X.plen (8 * X.P.ell) ≤ X.c2)
    (hcap4 : 2 * X.P.kh * (rowCost X.P.ell X.plen (8 * X.P.ell) + 2) + 1 ≤ X.c4)
    (hRV : 2 * X.P.ell + 1 ≤ X.c3) (hcL : 2 * X.P.ell + 1 ≤ X.c5)
    (hcapG : 2 * (8 * X.P.ell - X.plen) + 13 ≤ X.c0)
    (hcapG' : (X.consJ j).length * (2 * X.P.kh) * (Gauss.rowCost (8 * X.P.ell - X.plen) + 2) + 3 ≤ X.c1)
    (hcapG'' : (X.consJ j).length * (2 * X.P.kh) * (2 * (8 * X.P.ell - X.plen) + 1) + 1 ≤ X.c1)
    (hcK : 8 * X.P.ell - X.plen ≤ X.cK)
    (hcE1 : loopCost X.P.ell 8 (2 * X.P.kh) X.plen (X.consJ j).length + 1 + 1 ≤ X.c6)
    (hcE2 : Gauss.gaussCost ((X.consJ j).length * (2 * X.P.kh)) (8 * X.P.ell - X.plen) ≤ X.c6)
    (hcE3 : Deficit.cost (8 * X.P.ell - X.plen) ≤ X.c6)
    (hcf0 : 2 * X.P.kh * (2 + 2) + 1 ≤ X.c0) (hcf1 : 2 * 8 + 1 ≤ X.c1)
    (hcf2 : coefCost (binary 8 j) (2 * X.P.kh) (X.eJ j) ≤ 2 * X.c2 + 2)
    (ok : FcOk (aOnly (X.cfJ j)) X.ents (X.esJ j) X.c0 X.c1 X.c2 X.c3 X.Wt X.c4 X.c5)
    (hcs : ∀ k (_hk : k < (X.esJ j).length) (hk' : k < (X.csJ j).length),
      binary X.Wt (X.esJ j)[k] = (X.csJ j)[k] ++ binary X.TWd X.t)
    (hw : ∀ c ∈ X.csJ j, c.length + (binary X.TWd X.t).length = X.Wt)
    (hcG : ∀ c ∈ X.csJ j, tgtInnerCost c.length (binary X.TWd X.t).length ≤ X.c6)
    (hcH : ((List.range ((X.esJ j).length - 0)).map (fun i => fcCost (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.csJ j)
      (binary X.TWd X.t) X.Wt (0 + i) + 2)).sum + 1 ≤ X.c7)
    (hcE : emitInnerCost (exprWord V).length (exprWord (fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length ≤ X.c0) :
    Step groupM (groupCost X j V) (fun _ => 0) (X.jt j S V cnt).vec (fun _ => 0)
      (X.jt j (X.jNext j S) (V ++ X.emitJ j) cnt).vec := by
  set T0 := X.jt j S V cnt
  -- 1: the constraint records
  have h1 := stage_cons T0 X.P.ell (2 * X.P.kh) X.c0 (binary 8 j) [] [false] [false] (X.asJ j) (X.csJ j)
    (List.append_nil _).symm rfl rfl rfl (asJ_width X j) (csJ_width X j)
    (by rw [binary_length]; exact alphasOf_length _ _) (by rw [csJ_length, binary_length])
    (by rw [binary_length]; exact hkc)
  rw [show 2 * consInnerCost (binary 8 j).length X.P.ell (2 * X.P.kh) + 2 =
    2 * consInnerCost 8 X.P.ell (2 * X.P.kh) + 2 by rw [binary_length]] at h1
  set T1 := { T0 with CT := overlay (consOut (binary 8 j) (X.asJ j) (X.csJ j) (binary 8 j).length ++ [false]) T0.CT }
  -- 2: the elimination
  have h2 := stage_elim T1 X.P.modulus X.P.ell (2 * X.P.kh) X.plen X.pfx X.m X.c0 X.c1 X.c2 X.c4 X.c3 X.c5 X.c6 X.cK
    X.cC S.R (X.consJ j) _ S.g rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (cons_tape X j S.CT) rfl rfl rfl rfl rfl hp X.P.one_le_ell X.P.k_le hR hcons hcap hcap2 hcap2' hcap2'' hcap3 hcap3'
    hcap4 hplen hm hRV hcL hcapG hcapG' hcapG'' hcK hcE1 hcE2 hcE3
  have h2' : Step (RecoveryFocus.machine slElim elimM) (elimCost X.P.ell 8 (2 * X.P.kh) X.plen (X.consJ j).length)
      (fun _ => 0) T1.vec (fun _ => 0) (X.jt j (X.elimSt j S) V cnt).vec := h2
  -- 3: the branch on consistency
  set T2 := X.jt j (X.elimSt j S) V cnt
  have h3 : Step (branchM (48 : Fin 60) cfeM (idle 60))
      ((if (X.ggJ j).1 = true then
        coefCost (binary 8 j) (2 * X.P.kh) (X.eJ j) + 1 +
          fetchCellsCost (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.csJ j) (binary X.TWd X.t) X.Wt + 1 +
          (2 * emitInnerCost (exprWord V).length (exprWord (fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length + 2)
        else 0) + 2)
      (fun _ => 0) T2.vec (fun _ => 0) (X.jt j (X.jNext j S) (V ++ X.emitJ j) cnt).vec := by
    by_cases hg : (X.ggJ j).1 = true
    · have hA : (fs0 (binary 8 j) (2 * X.P.kh) (X.eJ j) T2).A = (aOnly (X.cfJ j)).A := rfl
      have hc := cfe_run T2 (binary 8 j) (2 * X.P.kh) S.sg [] ((S.XE).drop (X.eJ j + 1)) (X.eJ j) X.ents (X.esJ j)
        (X.csJ j) X.tailB [false] (binary X.TWd X.t) [] X.c0 X.c1 X.c2 X.c3 X.c4 X.c5 X.c6 X.c7 X.Wt S.tg S.fl V X.OB
        rfl (by rw [binary_length]; rfl) rfl rfl
        (by show overlay (List.replicate (X.eJ j) true ++ [false]) S.XE = _; rw [overlay_term, List.length_replicate])
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [esJ_length]; rfl) rfl rfl hcf0
        (by rw [binary_length]; exact hcf1) hcf2 (fcOk_of _ _ hA.symm _ _ _ _ _ _ _ _ _ ok)
        (by rw [csJ_length, esJ_length]) hcs hw hcG
        (by simp only [fcCost_eq _ _ hA]; exact hcH)
        (by rw [fcSt_A_eq _ _ hA]; exact hcE)
      have ecost : coefCost (binary 8 j) (2 * X.P.kh) (X.eJ j) + 1 +
          fetchCellsCost (fs0 (binary 8 j) (2 * X.P.kh) (X.eJ j) T2) X.ents (X.esJ j) (X.csJ j) (binary X.TWd X.t) X.Wt +
          1 + (2 * emitInnerCost (exprWord V).length
            (exprWord (fcSt (fs0 (binary 8 j) (2 * X.P.kh) (X.eJ j) T2) X.ents (X.esJ j) (X.esJ j).length).A).length + 2) =
          coefCost (binary 8 j) (2 * X.P.kh) (X.eJ j) + 1 +
          fetchCellsCost (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.csJ j) (binary X.TWd X.t) X.Wt + 1 +
          (2 * emitInnerCost (exprWord V).length
            (exprWord (fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length + 2) := by
        rw [fetchCellsCost_eq _ _ hA, fcSt_A_eq _ _ hA]
      rw [ecost] at hc
      have hb := branch_true (48 : Fin 60) (idle 60) hc (by show readTapeBit [(X.ggJ j).1] 0 = true; rw [hg]; rfl)
      rw [if_pos hg]
      have eF : X.jNext j S = X.grpSt j S := by unfold JCtx.jNext; rw [if_pos hv, if_pos hg]
      have eV : X.emitJ j = (X.sfJ j S).A := (sfJ_A X j S hv hg).symm
      rw [eF, eV]
      exact hb
    · have hb := branch_false (48 : Fin 60) cfeM (read_idle (fun _ => 0) T2.vec)
        (by show readTapeBit [(X.ggJ j).1] 0 = false; simp only [Bool.not_eq_true] at hg; rw [hg]; rfl)
      rw [if_neg hg]
      have eF : X.jNext j S = X.elimSt j S := by unfold JCtx.jNext; rw [if_pos hv, if_neg hg]
      have eV : X.emitJ j = [] := by unfold JCtx.emitJ; rw [if_neg (fun h => hg h.2)]
      rw [eF, eV, List.append_nil]
      exact hb
  unfold groupCost
  exact (h1.seq h2').seq h3

/-- The hypotheses of a valid counter value's group. -/
structure GroupOk (X : JCtx) (j : ℕ) (S : JState) (V : SExpr) : Prop where
  hp : GF.ModulusOk X.P.modulus X.P.ell
  hR : S.R.Ok X.P.ell 8
  hm : 1 ≤ X.m
  hplen : X.plen ≤ 8 * X.P.ell
  hcons : ∀ con ∈ X.consJ j, con.1 < 2 ^ X.P.ell
  hkc : consInnerCost 8 X.P.ell (2 * X.P.kh) ≤ X.c0
  hcap : 2 * X.P.ell + 2 ≤ X.c0
  hcap2 : X.P.ell * (innerCost X.P.ell + 2) + 1 ≤ X.c1
  hcap2' : X.P.ell * (mulIterCost X.P.ell + 2) + 1 ≤ X.c1
  hcap2'' : X.plen * (phACost X.P.ell + 2) + 1 ≤ X.c1
  hcap3 : tableCost X.P.ell 8 ≤ X.c2
  hcap3' : passesCost X.P.ell X.plen (8 * X.P.ell) ≤ X.c2
  hcap4 : 2 * X.P.kh * (rowCost X.P.ell X.plen (8 * X.P.ell) + 2) + 1 ≤ X.c4
  hRV : 2 * X.P.ell + 1 ≤ X.c3
  hcL : 2 * X.P.ell + 1 ≤ X.c5
  hcapG : 2 * (8 * X.P.ell - X.plen) + 13 ≤ X.c0
  hcapG' : (X.consJ j).length * (2 * X.P.kh) * (Gauss.rowCost (8 * X.P.ell - X.plen) + 2) + 3 ≤ X.c1
  hcapG'' : (X.consJ j).length * (2 * X.P.kh) * (2 * (8 * X.P.ell - X.plen) + 1) + 1 ≤ X.c1
  hcK : 8 * X.P.ell - X.plen ≤ X.cK
  hcE1 : loopCost X.P.ell 8 (2 * X.P.kh) X.plen (X.consJ j).length + 1 + 1 ≤ X.c6
  hcE2 : Gauss.gaussCost ((X.consJ j).length * (2 * X.P.kh)) (8 * X.P.ell - X.plen) ≤ X.c6
  hcE3 : Deficit.cost (8 * X.P.ell - X.plen) ≤ X.c6
  hcf0 : 2 * X.P.kh * (2 + 2) + 1 ≤ X.c0
  hcf1 : 2 * 8 + 1 ≤ X.c1
  hcf2 : coefCost (binary 8 j) (2 * X.P.kh) (X.eJ j) ≤ 2 * X.c2 + 2
  ok : FcOk (aOnly (X.cfJ j)) X.ents (X.esJ j) X.c0 X.c1 X.c2 X.c3 X.Wt X.c4 X.c5
  hcs : ∀ k (_hk : k < (X.esJ j).length) (hk' : k < (X.csJ j).length), binary X.Wt (X.esJ j)[k] = (X.csJ j)[k] ++ binary X.TWd X.t
  hw : ∀ c ∈ X.csJ j, c.length + (binary X.TWd X.t).length = X.Wt
  hcG : ∀ c ∈ X.csJ j, tgtInnerCost c.length (binary X.TWd X.t).length ≤ X.c6
  hcH : ((List.range ((X.esJ j).length - 0)).map (fun i => fcCost (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.csJ j) (binary X.TWd X.t) X.Wt (0 + i) + 2)).sum + 1 ≤ X.c7
  hcE : emitInnerCost (exprWord V).length (exprWord (fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length ≤ X.c0

theorem group_run' (X : JCtx) (j : ℕ) (S : JState) (V : SExpr) (cnt : ℕ) (hv : X.validJ j = true)
    (ok : GroupOk X j S V) :
    Step groupM (groupCost X j V) (fun _ => 0) (X.jt j S V cnt).vec (fun _ => 0)
      (X.jt j (X.jNext j S) (V ++ X.emitJ j) cnt).vec :=
  group_run X j S V cnt hv ok.hp ok.hR ok.hm ok.hplen ok.hcons ok.hkc ok.hcap ok.hcap2 ok.hcap2' ok.hcap2'' ok.hcap3 ok.hcap3' ok.hcap4 ok.hRV ok.hcL ok.hcapG ok.hcapG' ok.hcapG'' ok.hcK ok.hcE1 ok.hcE2 ok.hcE3 ok.hcf0 ok.hcf1 ok.hcf2 ok.ok ok.hcs ok.hw ok.hcG ok.hcH ok.hcE

/-! ## The enumeration cell -/

/-- The capacities of the split, the cell words and the validity test. -/
structure CellOk (X : JCtx) : Prop where
  hℓ : 8 * (2 + 2) + 1 ≤ X.c0
  hl : X.P.ell * (2 + 2) + 1 ≤ X.c0
  hk : X.P.kh * (2 + 2) + 1 ≤ X.c0
  hl2 : 8 * (fieldCost X.P.ell + 2) + 1 + 1 + 1 ≤ X.c1
  hk2 : 8 * (fieldCost X.P.kh + 2) + 1 + 1 + 1 ≤ X.c1
  hr2 : 2 * X.P.kh + 1 + 1 + 1 + 1 + (((List.range (7 - 0)).map (fun _ => 2 * X.P.kh + 1 + 1 + 1 + 1 + 1 + 2)).sum + 1)
    ≤ X.c1
  hcM1 : splitFieldsCost X.P.ell X.P.kh ≤ X.c2
  hcM2 : (2 * splitFieldsCost X.P.ell X.P.kh + 2) + 1 + splitRotCost X.P.kh ≤ X.c3
  hcells : cellsInnerCost X.P.kh ≤ X.c0
  hv0 : 2 * X.P.ell + 1 + 1 + 1 ≤ X.c0
  hv1 : validInnerCost 8 X.P.ell ≤ X.c1

noncomputable def jWorkM := Composition.machine (Composition.machine (Composition.machine
  (RecoveryFocus.machine slSplit2 splitM) (RecoveryFocus.machine slCells cellsM)) (RecoveryFocus.machine slValid validM))
  (branchM (8 : Fin 60) groupM (idle 60))

noncomputable def jCost (X : JCtx) (j : ℕ) (V : SExpr) : ℕ :=
  splitCost X.P.ell X.P.kh + 1 + (2 * cellsInnerCost X.P.kh + 2) + 1 + (2 * validInnerCost 8 X.P.ell + 2) + 1 +
    ((if X.validJ j = true then groupCost X j V else 0) + 2)

theorem overlay_same (w B : List Bool) (h : w.length = B.length) : overlay w B = w := by
  simp [overlay, h]

theorem flatMap_frame_length (r : ℕ) : ∀ (ws : List (List Bool)), (∀ w ∈ ws, w.length = r) →
    (ws.flatMap frame).length = ws.length * (2 * r + 1)
  | [], _ => by simp
  | w :: ws, h => by
    rw [List.flatMap_cons, List.length_append, frame_length, h w List.mem_cons_self,
      flatMap_frame_length r ws (fun v hv => h v (List.mem_cons_of_mem _ hv)), List.length_cons]
    ring

theorem digs_width (ℓ kh j : ℕ) : ∀ d ∈ digsOf ℓ kh j, d.length = kh := fields8_width _ _

theorem rot_width (ℓ kh j : ℕ) :
    ∀ d ∈ (digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []], d.length = kh := by
  intro d hd
  rw [List.mem_append] at hd
  rcases hd with hd | hd
  · exact digs_width ℓ kh j d (List.mem_of_mem_tail hd)
  · rw [List.mem_singleton] at hd
    subst hd
    have hl : (digsOf ℓ kh j).length = 8 := digsOf_length ℓ kh j
    have hm : (digsOf ℓ kh j).headD [] ∈ digsOf ℓ kh j := by
      cases h : digsOf ℓ kh j with
      | nil => rw [h] at hl; simp at hl
      | cons a l => exact List.mem_cons_self
    exact digs_width ℓ kh j _ hm

theorem rot_length (ℓ kh j : ℕ) : ((digsOf ℓ kh j).tail ++ [(digsOf ℓ kh j).headD []]).length = 8 := by
  rw [List.length_append, List.length_tail, digsOf_length]; rfl

theorem lab_width (X : JCtx) (j : ℕ) : ((X.asJ j).getD 7 []).length = X.P.ell := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [JCtx.asJ, alphasOf_length]), Option.getD_some]
  exact asJ_width X j _ (List.getElem_mem _)

theorem jWork_run (X : JCtx) (j jp : ℕ) (S : JState) (V : SExpr) (hc : CellOk X)
    (hg : X.validJ j = true → GroupOk X j S V) :
    Step jWorkM (jCost X j V) (fun _ => 0) (X.jt jp S V j).vec (fun _ => 0)
      (X.jt j (X.jNext j S) (V ++ X.emitJ j) j).vec := by
  set T0 := X.jt jp S V j
  have hdg : ∀ i, ((digsOf X.P.ell X.P.kh i).flatMap frame ++ [false]).length = 8 * (2 * X.P.kh + 1) + 1 := by
    intro i
    rw [List.length_append, flatMap_frame_length X.P.kh _ (digs_width _ _ i), digsOf_length]; rfl
  have hdn : ∀ i, (((digsOf X.P.ell X.P.kh i).tail ++ [(digsOf X.P.ell X.P.kh i).headD []]).flatMap frame ++
      [false]).length = 8 * (2 * X.P.kh + 1) + 1 := by
    intro i
    rw [List.length_append, flatMap_frame_length X.P.kh _ (rot_width _ _ i), rot_length]; rfl
  have hal : ∀ i, ((alphasOf X.P.ell i).flatMap frame ++ [false]).length = 8 * (2 * X.P.ell + 1) + 1 := by
    intro i
    rw [List.length_append, flatMap_frame_length X.P.ell (alphasOf X.P.ell i) (fields8_width _ _), alphasOf_length]; rfl
  have hcl : ∀ i, (X.clW i).length = 8 * (2 * (2 * X.P.kh) + 1) + 1 := by
    intro i
    unfold JCtx.clW
    rw [List.length_append, flatMap_frame_length (2 * X.P.kh) _ (csJ_width X i), csJ_length]; rfl
  -- 1: the split
  have h1 := stage_split T0 X.P.ell X.P.kh j X.c0 X.c1 X.c2 X.c3 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hc.hℓ hc.hl hc.hk
    hc.hl2 hc.hk2 hc.hr2 hc.hcM1 hc.hcM2
  rw [overlay_same (frame (binary 8 j)) T0.BT (by show _ = (frame (binary 8 jp)).length; simp [frame_length]),
    overlay_same _ T0.AL (by show _ = (X.alW jp).length; unfold JCtx.alW JCtx.asJ; rw [hal, hal]),
    overlay_same _ T0.DG (by show _ = (X.dgW jp).length; unfold JCtx.dgW; rw [hdg, hdg]),
    overlay_same _ T0.DN (by show _ = (X.dnW jp).length; unfold JCtx.dnW; rw [hdn, hdn])] at h1
  set T1 := { T0 with BT := frame (binary 8 j), AL := (alphasOf X.P.ell j).flatMap frame ++ [false],
                      DG := (digsOf X.P.ell X.P.kh j).flatMap frame ++ [false],
                      DN := ((digsOf X.P.ell X.P.kh j).tail ++ [(digsOf X.P.ell X.P.kh j).headD []]).flatMap frame ++
                        [false] }
  -- 2: the cell words
  have h2 := stage_cells T1 X.P.kh X.c0 (digW X.P j 0) (digW X.P j 1) (digW X.P j 2) (digW X.P j 3) (digW X.P j 4)
    (digW X.P j 5) (digW X.P j 6) (digW X.P j 7) [false] [false]
    (by show (digsOf X.P.ell X.P.kh j).flatMap frame ++ [false] = _; rw [digsOf_eq])
    (by show ((digsOf X.P.ell X.P.kh j).tail ++ [(digsOf X.P.ell X.P.kh j).headD []]).flatMap frame ++ [false] = _
        rw [digsOf_eq]; rfl)
    rfl (digW_length _ _ _) (digW_length _ _ _) (digW_length _ _ _) (digW_length _ _ _) (digW_length _ _ _)
    (digW_length _ _ _) (digW_length _ _ _) (digW_length _ _ _) hc.hcells
  have eCL : cellsOut (digW X.P j 0) (digW X.P j 1) (digW X.P j 2) (digW X.P j 3) (digW X.P j 4) (digW X.P j 5)
      (digW X.P j 6) (digW X.P j 7) ++ [false] = X.clW j := by
    rw [cellsOut_eq]; unfold JCtx.clW JCtx.csJ; rw [List.flatMap_map]
  rw [eCL, overlay_same _ T1.CL (by show _ = (X.clW jp).length; rw [hcl, hcl])] at h2
  set T2 := { T1 with CL := X.clW j }
  -- 3: the labels below `Q`
  have h3 := stage_valid T2 X.P.ell X.c0 X.c1 ((X.asJ jp).getD 7 []) X.q [false] (cmpQ X.q ((X.asJ jp).getD 7 []))
    (X.validJ jp) (X.asJ j)
    (by show _ = List.replicate (alphasOf X.P.ell j).length true ++ [false]; rw [alphasOf_length]; rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl (asJ_width X j) (lab_width X jp) (binary_length _ _) hc.hv0
    (by show validInnerCost (alphasOf X.P.ell j).length X.P.ell ≤ X.c1; rw [alphasOf_length]; exact hc.hv1)
  have eL : (X.asJ j).length = 8 := alphasOf_length _ _
  rw [eL] at h3
  have eT3 : ({ T2 with LAB := frame (labAt ((X.asJ jp).getD 7 []) (X.asJ j) 8),
                        CC := [ccAt (cmpQ X.q ((X.asJ jp).getD 7 [])) X.q (X.asJ j) 8],
                        V := [(X.asJ j).all (cmpQ X.q)] } : JT) = X.jt j S V j := rfl
  rw [eT3] at h3
  -- 4: the group, if the labels are valid
  have h4 : Step (branchM (8 : Fin 60) groupM (idle 60)) ((if X.validJ j = true then groupCost X j V else 0) + 2)
      (fun _ => 0) (X.jt j S V j).vec (fun _ => 0) (X.jt j (X.jNext j S) (V ++ X.emitJ j) j).vec := by
    by_cases hv : X.validJ j = true
    · rw [if_pos hv]
      exact branch_true (8 : Fin 60) (idle 60) (group_run' X j S V j hv (hg hv))
        (by show readTapeBit [X.validJ j] 0 = true; rw [hv]; rfl)
    · rw [if_neg hv]
      have eF : X.jNext j S = S := by unfold JCtx.jNext; rw [if_neg hv]
      have eV : X.emitJ j = [] := by unfold JCtx.emitJ; rw [if_neg (fun h => hv h.1)]
      rw [eF, eV, List.append_nil]
      exact branch_false (8 : Fin 60) groupM (read_idle (fun _ => 0) (X.jt j S V j).vec)
        (by show readTapeBit [X.validJ j] 0 = false; simp only [Bool.not_eq_true] at hv; rw [hv]; rfl)
  unfold jCost
  exact ((h1.seq h2).seq h3).seq h4

end JBody

end NearCubicWires.WireExponent3_5.SeedFix
