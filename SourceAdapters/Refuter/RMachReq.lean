import SourceAdapters.Refuter.RMachLayout

/-!
# R writes its request word and its output record (input 7, R: emission)

Paper anchor: proof of `lem:multitape-refuter` (each query is written in full, as the compiler's framed input), 
(the output `x_p`), proof of `cor:framed-refuter` (records), (request fields: code, input, witness length,
fuel in unary, the endpoint `high` in binary).

* `emRec act src`: the record `1^mi 0 1^xr 0 w_v` bit by bit (`v` stored in `src`).
* `emitReq D`: the framed request word `frame (memWord …)` (phase flag `P3` clear) or
  `frame (intWord …)` (`P3` set) on the compiler's input stream `D`, counter `rC`.
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Generic emission lemmas -/

section Generic
variable {ns nr : ℕ} (cap : ℕ)

theorem flatMap_len_le (f : Bool → List Bool) (hfl : ∀ b, (f b).length ≤ 4) (l : List Bool) :
    (l.flatMap f).length ≤ 4 * l.length := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := hfl b; omega

theorem seq_app {P Q : WMX ns nr} {σ : WState ns nr} {D : Fin (ns + 1)} {R : Fin nr} {w1 w2 : List Bool} {n k : ℕ}
    (h1 : WXExec cap P σ (app σ D R w1) n) (h2 : WXExec cap Q (app σ D R w1) (app σ D R (w1 ++ w2)) k) :
    WXExec cap (.seq P Q) σ (app σ D R (w1 ++ w2)) (n + 1 + k) := WXExec.seq h1 h2

/-- An act from an accumulated state. -/
theorem act_app {act : Bool → WMX ns nr} {D : Fin (ns + 1)} {RD : Fin nr} {f : Bool → List Bool} {c : ℕ}
    (hact : IsAct cap act D RD f c) (b : Bool) (σ : WState ns nr) (A : List Bool) (hD : σ.sh D = (σ.st D).length)
    (hc : σ.val RD + A.length + (f b).length ≤ cap) :
    WXExec cap (act b) (app σ D RD A) (app σ D RD (A ++ f b)) c := by
  have := hact b (app σ D RD A) (app_end _ _ _ _ hD) (by simp; omega)
  rwa [app_app] at this

/-- The record `1^mi 0 1^xr 0 w_v`, one act per bit. -/
def emRec (act : Bool → WMX ns nr) (src MU XU : Fin (ns + 1)) (R1 : Fin nr) : WMX ns nr :=
  .seq (forU MU R1 (act true)) (.seq (act false) (.seq (forU XU R1 (act true)) (.seq (act false) (msb src R1 act))))

theorem emRec_spec {act : Bool → WMX ns nr} {D : Fin (ns + 1)} {RD : Fin nr} {f : Bool → List Bool} {c : ℕ}
    (hact : IsAct cap act D RD f c) (hfl : ∀ b, (f b).length ≤ 4) (src MU XU : Fin (ns + 1)) (R1 : Fin nr)
    (hsD : src ≠ D) (hMD : MU ≠ D) (hXD : XU ≠ D) (hR : R1 ≠ RD) (σ : WState ns nr) (mi xr g v : ℕ)
    (hMU : σ.st MU = List.replicate mi true) (hMUh : σ.sh MU = 0) (hXU : σ.st XU = List.replicate xr true)
    (hXUh : σ.sh XU = 0) (hsrc : σ.st src = RepairOrdinary.frame (binary (g + 2) v)) (hsrch : σ.sh src = 0)
    (hR0 : σ.val R1 = 0) (hD : σ.sh D = (σ.st D).length)
    (hc : σ.val RD + 4 * (mi + xr + g + 2) ≤ cap) (hcap : mi + xr + 2 * g + 6 ≤ cap) :
    WXExec cap (emRec act src MU XU R1) σ (app σ D RD ((recList mi xr g v).flatMap f))
      ((mi + xr + g + 5) * (c + 40)) := by
  have l1 := flatMap_len_le f hfl (List.replicate mi true)
  have l2 := flatMap_len_le f hfl (List.replicate xr true)
  have f0 := hfl false
  have e1 := forU_act cap hact true MU R1 hMD hR σ mi hMU hMUh hR0 hD (by have := hfl true; nlinarith) (by omega)
  have e2 := act_app cap hact false σ ((List.replicate mi true).flatMap f) hD (by simp at l1 ⊢; omega)
  have e3 := forU_act cap hact true XU R1 hXD hR (app σ D RD ((List.replicate mi true).flatMap f ++ f false)) xr
    (by rw [app_st_ne _ _ _ _ _ hXD, hXU]) (by rw [app_sh_ne _ _ _ _ _ hXD, hXUh])
    (by rw [app_val_ne _ _ _ _ _ hR, hR0]) (app_end _ _ _ _ hD)
    (by have := hfl true; simp at l1 ⊢; nlinarith) (by omega)
  rw [app_app] at e3
  have e4 := act_app cap hact false σ ((List.replicate mi true).flatMap f ++ f false ++
    (List.replicate xr true).flatMap f) hD (by simp at l1 l2 ⊢; omega)
  have e5 := msb_spec cap hact src R1 hsD hR (app σ D RD ((List.replicate mi true).flatMap f ++ f false ++
    (List.replicate xr true).flatMap f ++ f false)) g v (by rw [app_st_ne _ _ _ _ _ hsD, hsrc])
    (by rw [app_sh_ne _ _ _ _ _ hsD, hsrch]) (by rw [app_val_ne _ _ _ _ _ hR, hR0]) (app_end _ _ _ _ hD) hfl
    (by simp at l1 l2 ⊢; omega) (by omega)
  rw [app_app] at e5
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ ?_
  · simp only [recList, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  · nlinarith

end Generic

/-! ## The request word on the compiler's input stream -/

section Request
variable {tc tT : ℕ} (cap : ℕ)

local notation "WS" => WState (NS tc tT) NR

/-- A bit of a word that is itself framed inside the compiler's input: `1 1 1 b`. -/
abbrev f2 (b : Bool) : List Bool := [true, true, true, b]
/-- A framed bit: `1 b`. -/
abbrev f1 (b : Bool) : List Bool := [true, b]

theorem fpre_frame (l : List Bool) : fpre (RepairOrdinary.frame l) = l.flatMap f2 ++ f1 false := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [fpre] at ih ⊢
    simp [RepairOrdinary.frame, ih]

theorem fpre_append (l₁ l₂ : List Bool) : fpre (l₁ ++ l₂) = fpre l₁ ++ fpre l₂ := by
  simp [fpre, List.flatMap_append]

variable (D : Fin (NS tc tT + 1))

/-- `frame code` inside the request. -/
def emCode : WMX (NS tc tT) NR := .seq (forP sCODE r1 (.ifs sCODE (em2 D rC true) (em2 D rC false))) (em1 D rC false)
/-- `frame (1^a)` from a unary stream. -/
def emOnes (U : Fin (NS tc tT + 1)) : WMX (NS tc tT) NR := .seq (forU U r1 (em2 D rC true)) (em1 D rC false)
/-- `frame ((2^g).bits) = frame (0^g 1)`. -/
def emPow : WMX (NS tc tT) NR := .seq (forU sGU r1 (em2 D rC false)) (.seq (em2 D rC true) (em1 D rC false))
/-- `frame (q.bits)`: copy `Q` to `XH`, emit by halving. -/
def emBits : WMX (NS tc tT) NR :=
  .seq (BinW.copy sXH sQ bF bR) (.seq (halve sXH sZ rF bR (em2 D rC)) (em1 D rC false))
/-- `frame record` inside the request. -/
def emRecR (src : Fin (NS tc tT + 1)) : WMX (NS tc tT) NR := .seq (emRec (em2 D rC) src sMU sXU r1) (em1 D rC false)

/-- **The request word.** Membership (`P3` clear): `frame (memWord …)`; interval (`P3` set): `frame (intWord …)`. -/
def emitReq : WMX (NS tc tT) NR :=
  .seq (emCode D) (.seq (.ifs sP3 (emRecR D sZ) (emRecR D sQ)) (.seq (emOnes D sGU) (.seq (emOnes D sTU)
    (.seq (.ifs sP3 (emBits D) (emPow D)) (WMX.wr D false)))))

/-- What the request emission reads (all heads at `0`). -/
structure ReqSrc (σ : WS) (code : List Bool) (mi xr g TN : ℕ) : Prop where
  code : σ.st sCODE = RepairOrdinary.frame code
  mu : σ.st sMU = List.replicate mi true
  xu : σ.st sXU = List.replicate xr true
  gu : σ.st sGU = List.replicate g true
  tu : σ.st sTU = List.replicate TN true
  z : σ.st sZ = num (g + 2) 0
  sh : ∀ i, σ.sh i = 0
  r1 : σ.val r1 = 0
  rC : σ.val rC = 0
  bF : σ.val bF = 0
  bR : σ.val bR = 0
  rF : σ.val rF = 0

end Request

section RequestSpec
variable {tc tT : ℕ} (cap : ℕ)

local notation "WS" => WState (NS tc tT) NR

theorem f2_len (b : Bool) : (f2 b).length ≤ 4 := by simp
theorem f1_len (b : Bool) : (f1 b).length ≤ 4 := by simp

theorem sC_ne (j : Fin tc) (X : Fin (NS tc tT + 1)) (hX : X.val < 41) : X ≠ sC j := by
  intro h; have := congrArg Fin.val h; simp [sC] at this; omega

theorem app_sets_comm (σ : WS) (D X : Fin (NS tc tT + 1)) (R : Fin NR) (h : X ≠ D) (l w : List Bool) :
    app (σ.sets X l) D R w = (app σ D R w).sets X l := by
  unfold app; wst

theorem emCode_spec (D : Fin (NS tc tT + 1)) (hD4 : sCODE ≠ D) (τ : WS) (code : List Bool)
    (hX : τ.st sCODE = RepairOrdinary.frame code) (hXh : τ.sh sCODE = 0) (hR0 : τ.val r1 = 0)
    (hD : τ.sh D = (τ.st D).length) (hc : τ.val rC + 4 * code.length + 2 ≤ cap) :
    WXExec cap (emCode D) τ (app τ D rC (code.flatMap f2 ++ f1 false)) (code.length * 56 + 19) := by
  have e1 := forP_act cap (em2_act cap D rC) sCODE r1 hD4 (by decide) τ code [false]
    (by rw [hX, frame_eq_fpre]) hXh hR0 rfl hD f2_len (by omega) (by omega)
  have e2 := act_app cap (em1_act cap D rC) false τ (code.flatMap f2) hD
    (by have := flatMap_len_le f2 f2_len code; simp at this ⊢; omega)
  exact (WXExec.seq e1 e2).cast cap rfl (by omega)

theorem emOnes_spec (D U : Fin (NS tc tT + 1)) (hUD : U ≠ D) (τ : WS) (a : ℕ)
    (hU : τ.st U = List.replicate a true) (hUh : τ.sh U = 0) (hR0 : τ.val r1 = 0)
    (hD : τ.sh D = (τ.st D).length) (hc : τ.val rC + 4 * a + 2 ≤ cap) :
    WXExec cap (emOnes D U) τ (app τ D rC ((List.replicate a true).flatMap f2 ++ f1 false)) (a * 44 + 19) := by
  have e1 := forU_act cap (em2_act cap D rC) true U r1 hUD (by decide) τ a hU hUh hR0 hD (by simp; omega)
    (by omega)
  have e2 := act_app cap (em1_act cap D rC) false τ ((List.replicate a true).flatMap f2) hD
    (by simp; omega)
  exact (WXExec.seq e1 e2).cast cap rfl (by omega)

theorem emPow_spec (D : Fin (NS tc tT + 1)) (hUD : sGU ≠ D) (τ : WS) (g : ℕ)
    (hU : τ.st sGU = List.replicate g true) (hUh : τ.sh sGU = 0) (hR0 : τ.val r1 = 0)
    (hD : τ.sh D = (τ.st D).length) (hc : τ.val rC + 4 * g + 6 ≤ cap) :
    WXExec cap (emPow D) τ (app τ D rC ((List.replicate g false).flatMap f2 ++ f2 true ++ f1 false))
      (g * 44 + 52) := by
  have e1 := forU_act cap (em2_act cap D rC) false sGU r1 hUD (by decide) τ g hU hUh hR0 hD (by simp; omega)
    (by omega)
  have e2 := act_app cap (em2_act cap D rC) true τ ((List.replicate g false).flatMap f2) hD (by simp; omega)
  have e3 := act_app cap (em1_act cap D rC) false τ ((List.replicate g false).flatMap f2 ++ f2 true) hD
    (by simp; omega)
  exact (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap rfl (by omega)

theorem emRecR_spec (D src : Fin (NS tc tT + 1)) (hsD : src ≠ D) (hMD : sMU ≠ D) (hXD : sXU ≠ D) (τ : WS)
    (mi xr g v : ℕ) (hMU : τ.st sMU = List.replicate mi true) (hMUh : τ.sh sMU = 0)
    (hXU : τ.st sXU = List.replicate xr true) (hXUh : τ.sh sXU = 0)
    (hsrc : τ.st src = RepairOrdinary.frame (binary (g + 2) v)) (hsrch : τ.sh src = 0) (hR0 : τ.val r1 = 0)
    (hD : τ.sh D = (τ.st D).length) (hc : τ.val rC + 4 * (mi + xr + g + 2) + 2 ≤ cap)
    (hcap : mi + xr + 2 * g + 6 ≤ cap) :
    WXExec cap (emRecR D src) τ (app τ D rC ((recList mi xr g v).flatMap f2 ++ f1 false))
      ((mi + xr + g + 5) * 71 + 16) := by
  have e1 := emRec_spec cap (em2_act cap D rC) f2_len src sMU sXU r1 hsD hMD hXD (by decide) τ mi xr g v hMU
    hMUh hXU hXUh hsrc hsrch hR0 hD (by omega) hcap
  have hl := flatMap_len_le f2 f2_len (recList mi xr g v)
  have hrl : (recList mi xr g v).length = mi + xr + g + 2 := by simp [recList, wbits]; omega
  have e2 := act_app cap (em1_act cap D rC) false τ ((recList mi xr g v).flatMap f2) hD (by simp; omega)
  exact (WXExec.seq e1 e2).cast cap rfl (by omega)

theorem fpre_memWord (code : List Bool) (mi xr g TN q : ℕ) :
    fpre (memWord code mi xr g TN q) =
      (code.flatMap f2 ++ f1 false) ++ ((recList mi xr g q).flatMap f2 ++ f1 false) ++
        ((List.replicate g true).flatMap f2 ++ f1 false) ++ ((List.replicate TN true).flatMap f2 ++ f1 false) ++
        ((List.replicate g false).flatMap f2 ++ f2 true ++ f1 false) := by
  simp only [memWord, fpre_append, fpre_frame, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

theorem fpre_intWord (code : List Bool) (mi xr g TN q : ℕ) :
    fpre (intWord code mi xr g TN q) =
      (code.flatMap f2 ++ f1 false) ++ ((recList mi xr g 0).flatMap f2 ++ f1 false) ++
        ((List.replicate g true).flatMap f2 ++ f1 false) ++ ((List.replicate TN true).flatMap f2 ++ f1 false) ++
        (q.bits.flatMap f2 ++ f1 false) := by
  simp only [intWord, fpre_append, fpre_frame, List.append_assoc]

/-- **The membership request is written** (`P3` clear): the compiler's input stream becomes
`frame (memWord …)`, its head at the last cell, counter `rC` = that cell's index. -/
theorem emitReq_mem (j0 : Fin tc) (σ : WS) (code : List Bool) (mi xr g TN q : ℕ)
    (hs : ReqSrc σ code mi xr g TN) (hQ : σ.st sQ = num (g + 2) q) (hP3 : σ.st sP3 = [false])
    (hD0 : σ.st (sC j0) = []) (hcap : 40 * (code.length + mi + xr + g + TN + 10) ≤ cap) :
    WXExec cap (emitReq (sC j0)) σ
      ((app σ (sC j0) rC (fpre (memWord code mi xr g TN q))).sets (sC j0)
        (RepairOrdinary.frame (memWord code mi xr g TN q)))
      (200 * (code.length + mi + xr + g + TN + 10) ^ 2) := by
  set D := sC (tT := tT) j0 with hDdef
  have hD : σ.sh D = (σ.st D).length := by rw [hs.sh, hD0]; rfl
  have nCODE : sCODE ≠ D := sC_ne j0 _ (by ds)
  have nMU : sMU ≠ D := sC_ne j0 _ (by ds)
  have nXU : sXU ≠ D := sC_ne j0 _ (by ds)
  have nGU : sGU ≠ D := sC_ne j0 _ (by ds)
  have nTU : sTU ≠ D := sC_ne j0 _ (by ds)
  have nQ : sQ ≠ D := sC_ne j0 _ (by ds)
  have nP3 : sP3 ≠ D := sC_ne j0 _ (by ds)
  have lc := flatMap_len_le f2 f2_len code
  have lr := flatMap_len_le f2 f2_len (recList mi xr g q)
  have hrl : (recList mi xr g q).length = mi + xr + g + 2 := by simp [recList, wbits]; omega
  set A1 := code.flatMap f2 ++ f1 false
  set A2 := (recList mi xr g q).flatMap f2 ++ f1 false
  set A3 := (List.replicate g true).flatMap f2 ++ f1 false
  set A4 := (List.replicate TN true).flatMap f2 ++ f1 false
  set A5 := (List.replicate g false).flatMap f2 ++ f2 true ++ f1 false
  have l1 : A1.length ≤ 4 * code.length + 2 := by simp [A1]; omega
  have l2 : A2.length ≤ 4 * (mi + xr + g + 2) + 2 := by simp [A2]; omega
  have l3 : A3.length = 4 * g + 2 := by simp [A3]; ring
  have l4 : A4.length = 4 * TN + 2 := by simp [A4]; ring
  have e1 := emCode_spec cap D nCODE σ code hs.code (hs.sh _) hs.r1 hD (by rw [hs.rC]; omega)
  have e2 := emRecR_spec cap D sQ nQ nMU nXU (app σ D rC A1) mi xr g q
    (by rw [app_st_ne _ _ _ _ _ nMU, hs.mu]) (by rw [app_sh_ne _ _ _ _ _ nMU, hs.sh])
    (by rw [app_st_ne _ _ _ _ _ nXU, hs.xu]) (by rw [app_sh_ne _ _ _ _ _ nXU, hs.sh])
    (by rw [app_st_ne _ _ _ _ _ nQ, hQ]) (by rw [app_sh_ne _ _ _ _ _ nQ, hs.sh])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.r1]) (app_end _ _ _ _ hD)
    (by simp [hs.rC]; omega) (by omega)
  rw [app_app] at e2
  have e2' : WXExec cap (.ifs sP3 (emRecR D sZ) (emRecR D sQ)) (app σ D rC A1) (app σ D rC (A1 ++ A2))
      ((mi + xr + g + 5) * 71 + 17) :=
    WXExec.ifsF (by simp only [wbit, app_st_ne _ _ _ _ _ nP3, app_sh_ne _ _ _ _ _ nP3, hP3, hs.sh]; rfl) e2
  have e3 := emOnes_spec cap D sGU nGU (app σ D rC (A1 ++ A2)) g
    (by rw [app_st_ne _ _ _ _ _ nGU, hs.gu]) (by rw [app_sh_ne _ _ _ _ _ nGU, hs.sh])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.r1]) (app_end _ _ _ _ hD) (by simp [hs.rC]; omega)
  rw [app_app] at e3
  have e4 := emOnes_spec cap D sTU nTU (app σ D rC (A1 ++ A2 ++ A3)) TN
    (by rw [app_st_ne _ _ _ _ _ nTU, hs.tu]) (by rw [app_sh_ne _ _ _ _ _ nTU, hs.sh])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.r1]) (app_end _ _ _ _ hD) (by simp [hs.rC]; omega)
  rw [app_app] at e4
  have e5 := emPow_spec cap D nGU (app σ D rC (A1 ++ A2 ++ A3 ++ A4)) g
    (by rw [app_st_ne _ _ _ _ _ nGU, hs.gu]) (by rw [app_sh_ne _ _ _ _ _ nGU, hs.sh])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.r1]) (app_end _ _ _ _ hD) (by simp [hs.rC]; omega)
  rw [app_app] at e5
  have e5' : WXExec cap (.ifs sP3 (emBits D) (emPow D)) (app σ D rC (A1 ++ A2 ++ A3 ++ A4))
      (app σ D rC (A1 ++ A2 ++ A3 ++ A4 ++ A5)) (g * 44 + 53) :=
    WXExec.ifsF (by simp only [wbit, app_st_ne _ _ _ _ _ nP3, app_sh_ne _ _ _ _ _ nP3, hP3, hs.sh]; rfl) e5
  have e6 := WXExec.wr cap D false (app σ D rC (A1 ++ A2 ++ A3 ++ A4 ++ A5))
  have hw : fpre (memWord code mi xr g TN q) = A1 ++ A2 ++ A3 ++ A4 ++ A5 := fpre_memWord code mi xr g TN q
  refine (WXExec.seq e1 (WXExec.seq e2' (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5' e6))))).cast cap ?_ ?_
  · rw [hw, frame_eq_fpre, hw]
    congr 1
    simp only [app_st_D, app_sh_D, hD0, List.nil_append, hs.sh, Nat.zero_add]
    exact wtb_append _ false
  · nlinarith

theorem emBits_spec (D : Fin (NS tc tT + 1)) (nXH : sXH ≠ D) (nZ : sZ ≠ D) (τ : WS) (g q a : ℕ)
    (hXH : τ.st sXH = num (g + 2) a) (hQ : τ.st sQ = num (g + 2) q) (hq : q < 2 ^ (g + 2))
    (hZ : τ.st sZ = num (g + 2) 0) (hXHh : τ.sh sXH = 0) (hQh : τ.sh sQ = 0) (hZh : τ.sh sZ = 0)
    (hF : τ.val bF = 0) (hR : τ.val bR = 0)
    (hrF : τ.val rF = 0) (hD : τ.sh D = (τ.st D).length) (hc : τ.val rC + 4 * (g + 2) + 2 ≤ cap)
    (hcap : 2 * (g + 2) + 1 ≤ cap) :
    WXExec cap (emBits D) τ ((app τ D rC (q.bits.flatMap f2 ++ f1 false)).sets sXH (num (g + 2) 0))
      (41 * (g + 2) + 20 + (g + 4) * (51 + 90 * (g + 2))) := by
  have e1 := BinW.copy_spec cap (g + 2) (A := sXH) (B := sQ) (F := bF) (R := bR) (by ds) (by decide) τ a q
    ⟨hXH, hXHh⟩ ⟨hQ, hQh⟩ hF hR hcap
  have e2 := halve_spec cap (em2_act cap D rC) sXH sZ rF bR nXH nZ (by ds) (by decide) (by decide) (by decide)
    (g + 2) (by omega) f2_len hcap (τ.sets sXH (num (g + 2) q))
    ⟨by simp only [WState.sets_st]; rw [Function.update_of_ne (by ds), hZ], by simp only [WState.sets_sh]; exact hZh⟩
    (by simp only [WState.sets_val]; exact hR) (by simp only [WState.sets_val]; exact hrF)
    (by simp only [WState.sets_sh, WState.sets_st, Function.update_of_ne nXH.symm]; exact hD) q
    ⟨by simp only [WState.sets_st, Function.update_self], by simp only [WState.sets_sh]; exact hXHh⟩ hq
    (by simp only [WState.sets_val]; omega)
  rw [app_sets_comm _ _ _ _ nXH, BinW.sets_sets, ← app_sets_comm _ _ _ _ nXH] at e2
  have hD' : (τ.sets sXH (num (g + 2) 0)).sh D = ((τ.sets sXH (num (g + 2) 0)).st D).length := by
    simp only [WState.sets_sh, WState.sets_st, Function.update_of_ne nXH.symm]; exact hD
  have e3 := act_app cap (em1_act cap D rC) false (τ.sets sXH (num (g + 2) 0)) (q.bits.flatMap f2) hD'
    (by
      have h1 := flatMap_len_le f2 f2_len q.bits
      have h2 : q.bits.length ≤ g + 2 := by
        have := Nat.size_eq_bits_len q; have := Nat.size_le.mpr hq; omega
      simp; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by nlinarith)
  rw [app_sets_comm _ _ _ _ nXH]

/-- **The interval request is written** (`P3` set): the compiler's input stream becomes `frame (intWord …)`
(the scratch number `XH` ends at `0`). -/
theorem emitReq_int (j0 : Fin tc) (σ : WS) (code : List Bool) (mi xr g TN q a : ℕ)
    (hs : ReqSrc σ code mi xr g TN) (hQ : σ.st sQ = num (g + 2) q) (hq : q < 2 ^ (g + 2))
    (hXH : σ.st sXH = num (g + 2) a) (hP3 : σ.st sP3 = [true])
    (hD0 : σ.st (sC j0) = []) (hcap : 40 * (code.length + mi + xr + g + TN + 10) ≤ cap) :
    WXExec cap (emitReq (sC j0)) σ
      (((app σ (sC j0) rC (fpre (intWord code mi xr g TN q))).sets (sC j0)
        (RepairOrdinary.frame (intWord code mi xr g TN q))).sets sXH (num (g + 2) 0))
      (200 * (code.length + mi + xr + g + TN + 10) ^ 2) := by
  set D := sC (tT := tT) j0 with hDdef
  have hD : σ.sh D = (σ.st D).length := by rw [hs.sh, hD0]; rfl
  have nCODE : sCODE ≠ D := sC_ne j0 _ (by ds)
  have nMU : sMU ≠ D := sC_ne j0 _ (by ds)
  have nXU : sXU ≠ D := sC_ne j0 _ (by ds)
  have nGU : sGU ≠ D := sC_ne j0 _ (by ds)
  have nTU : sTU ≠ D := sC_ne j0 _ (by ds)
  have nZ : sZ ≠ D := sC_ne j0 _ (by ds)
  have nXH : sXH ≠ D := sC_ne j0 _ (by ds)
  have nP3 : sP3 ≠ D := sC_ne j0 _ (by ds)
  have lc := flatMap_len_le f2 f2_len code
  have hrl : (recList mi xr g 0).length = mi + xr + g + 2 := by simp [recList, wbits]; omega
  have lr := flatMap_len_le f2 f2_len (recList mi xr g 0)
  set A1 := code.flatMap f2 ++ f1 false
  set A2 := (recList mi xr g 0).flatMap f2 ++ f1 false
  set A3 := (List.replicate g true).flatMap f2 ++ f1 false
  set A4 := (List.replicate TN true).flatMap f2 ++ f1 false
  set A5 := q.bits.flatMap f2 ++ f1 false
  have l1 : A1.length ≤ 4 * code.length + 2 := by simp [A1]; omega
  have l2 : A2.length ≤ 4 * (mi + xr + g + 2) + 2 := by simp [A2]; omega
  have l3 : A3.length = 4 * g + 2 := by simp [A3]; ring
  have l4 : A4.length = 4 * TN + 2 := by simp [A4]; ring
  have e1 := emCode_spec cap D nCODE σ code hs.code (hs.sh _) hs.r1 hD (by rw [hs.rC]; omega)
  have e2 := emRecR_spec cap D sZ nZ nMU nXU (app σ D rC A1) mi xr g 0
    (by rw [app_st_ne _ _ _ _ _ nMU, hs.mu]) (by rw [app_sh_ne _ _ _ _ _ nMU, hs.sh])
    (by rw [app_st_ne _ _ _ _ _ nXU, hs.xu]) (by rw [app_sh_ne _ _ _ _ _ nXU, hs.sh])
    (by rw [app_st_ne _ _ _ _ _ nZ, hs.z]) (by rw [app_sh_ne _ _ _ _ _ nZ, hs.sh])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.r1]) (app_end _ _ _ _ hD)
    (by simp [hs.rC]; omega) (by omega)
  rw [app_app] at e2
  have e2' : WXExec cap (.ifs sP3 (emRecR D sZ) (emRecR D sQ)) (app σ D rC A1) (app σ D rC (A1 ++ A2))
      ((mi + xr + g + 5) * 71 + 17) :=
    WXExec.ifsT (by simp only [wbit, app_st_ne _ _ _ _ _ nP3, app_sh_ne _ _ _ _ _ nP3, hP3, hs.sh]; rfl) e2
  have e3 := emOnes_spec cap D sGU nGU (app σ D rC (A1 ++ A2)) g
    (by rw [app_st_ne _ _ _ _ _ nGU, hs.gu]) (by rw [app_sh_ne _ _ _ _ _ nGU, hs.sh])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.r1]) (app_end _ _ _ _ hD) (by simp [hs.rC]; omega)
  rw [app_app] at e3
  have e4 := emOnes_spec cap D sTU nTU (app σ D rC (A1 ++ A2 ++ A3)) TN
    (by rw [app_st_ne _ _ _ _ _ nTU, hs.tu]) (by rw [app_sh_ne _ _ _ _ _ nTU, hs.sh])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.r1]) (app_end _ _ _ _ hD) (by simp [hs.rC]; omega)
  rw [app_app] at e4
  have e5 := emBits_spec cap D nXH nZ (app σ D rC (A1 ++ A2 ++ A3 ++ A4)) g q a
    (by rw [app_st_ne _ _ _ _ _ nXH, hXH]) (by rw [app_st_ne _ _ _ _ _ (sC_ne j0 _ (by ds)), hQ]) hq
    (by rw [app_st_ne _ _ _ _ _ nZ, hs.z])
    (by rw [app_sh_ne _ _ _ _ _ nXH, hs.sh]) (by rw [app_sh_ne _ _ _ _ _ (sC_ne j0 _ (by ds)), hs.sh])
    (by rw [app_sh_ne _ _ _ _ _ nZ, hs.sh])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.bF]) (by rw [app_val_ne _ _ _ _ _ (by decide), hs.bR])
    (by rw [app_val_ne _ _ _ _ _ (by decide), hs.rF]) (app_end _ _ _ _ hD)
    (by simp [hs.rC]; omega) (by omega)
  rw [app_app] at e5
  have e5' : WXExec cap (.ifs sP3 (emBits D) (emPow D)) (app σ D rC (A1 ++ A2 ++ A3 ++ A4))
      ((app σ D rC (A1 ++ A2 ++ A3 ++ A4 ++ A5)).sets sXH (num (g + 2) 0))
      (41 * (g + 2) + 20 + (g + 4) * (51 + 90 * (g + 2)) + 1) :=
    WXExec.ifsT (by simp only [wbit, app_st_ne _ _ _ _ _ nP3, app_sh_ne _ _ _ _ _ nP3, hP3, hs.sh]; rfl) e5
  have e6 := WXExec.wr cap D false ((app σ D rC (A1 ++ A2 ++ A3 ++ A4 ++ A5)).sets sXH (num (g + 2) 0))
  have hw : fpre (intWord code mi xr g TN q) = A1 ++ A2 ++ A3 ++ A4 ++ A5 := fpre_intWord code mi xr g TN q
  have hwr : writeTapeBit (((app σ D rC (A1 ++ A2 ++ A3 ++ A4 ++ A5)).sets sXH (num (g + 2) 0)).st D)
      (((app σ D rC (A1 ++ A2 ++ A3 ++ A4 ++ A5)).sets sXH (num (g + 2) 0)).sh D) false =
      RepairOrdinary.frame (intWord code mi xr g TN q) := by
    simp only [WState.sets_st, WState.sets_sh, Function.update_of_ne nXH.symm, app_st_D, app_sh_D, hD0,
      List.nil_append, hs.sh, Nat.zero_add]
    rw [wtb_append, frame_eq_fpre, hw]
  rw [hwr] at e6
  have hq2 : q.bits.length ≤ g + 2 := by
    have := Nat.size_eq_bits_len q; have := Nat.size_le.mpr hq; omega
  have hA5 : A5.length ≤ 4 * (g + 2) + 2 := by
    have := flatMap_len_le f2 f2_len q.bits; simp [A5]; omega
  refine (WXExec.seq e1 (WXExec.seq e2' (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5' e6))))).cast cap ?_ ?_
  · rw [hw]; wst
  · nlinarith

end RequestSpec

end NearCubicGates.Adapters.Refuter.RM
