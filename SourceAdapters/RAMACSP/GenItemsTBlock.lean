import SourceAdapters.RAMACSP.GenItemsBase

/-!
# The TIME block of the item stream

Paper: (T1)–(T10) in `def:event-trace` and "Placement" in
`app:affine-embedding`. Each fixed template has one equation per active bit
index. The generator tests these small index ranges rather than enumerating
lanes, as required by `lem:generator`.

The active time equations (`timeEqList`) are a concatenation of pieces: a template and a range of bit indices
(`w`, `w − 1`, `τ`, `τ − 1`, `β + 1`, `β`, or a single equation); the register and code-position families are
unrolled (`K`, `L` depend on `V` only). `timeEqList_pieces`: the list is the pieces' concatenation; `den_tBlock`: the
printer of the pieces prints the numbers of the time items of `machineItems`, in order.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary

variable {G : Glob}

/-! ## Counts and bit indices of a piece -/

/-- The count of a piece. -/
inductive Cnt where
  | w | wm1 | tau | taum1 | beta1 | beta | one | seg1 | seg2

/-- Its expression (`w` in 26, `τ` in 27, `β = τ − ω`). -/
def Cnt.e : Cnt → E
  | .w => .v 26
  | .wm1 => .sub (.v 26) (.k 1)
  | .tau => .v 27
  | .taum1 => .sub (.v 27) (.k 1)
  | .beta1 => .add betaE (.k 1)
  | .beta => betaE
  | .one => .k 1
  | .seg1 => .sub (.add (.v 27) (.k 2)) (.sub (.add (.v 27) (.k 2)) (.v 26))
  | .seg2 => .sub (.add (.v 27) (.k 2)) (.v 26)

/-- Its value. -/
def Cnt.val (d : Dims) : Cnt → ℕ
  | .w => d.w
  | .wm1 => d.w - 1
  | .tau => d.τ
  | .taum1 => d.τ - 1
  | .beta1 => d.β + 1
  | .beta => d.β
  | .one => 1
  | .seg1 => d.τ + 2 - (d.τ + 2 - d.w)
  | .seg2 => d.τ + 2 - d.w

/-- The bit index of pass `i` of a piece. -/
inductive JK where
  | idx | idx1 | zero

def JK.e : JK → E
  | .idx => .v vI
  | .idx1 => .add (.v vI) (.k 1)
  | .zero => k0

def JK.val (i : ℕ) : JK → ℕ
  | .idx => i
  | .idx1 => i + 1
  | .zero => 0

/-- The template representative of a time equation (bit index `0`). -/
def tRep : TEq → TEq
  | .flag r _ => .flag r 0
  | .decPc _ => .decPc 0
  | .opX _ => .opX 0
  | .opY _ => .opY 0
  | .sumAD _ => .sumAD 0
  | .carry _ => .carry 0
  | .sumSB _ => .sumSB 0
  | .borrow _ => .borrow 0
  | .andAN _ => .andAN 0
  | .ozRec _ => .ozRec 0
  | .rfFlag _ => .rfFlag 0
  | .store _ => .store 0
  | .res _ => .res 0
  | .reg r _ => .reg r 0
  | .pcNext _ => .pcNext 0
  | .recAd _ => .recAd 0
  | .recVa _ => .recVa 0
  | .tsn _ => .tsn 0
  | .tc _ => .tc 0
  | .can _ => .can 0
  | .ac _ => .ac 0
  | .cbn _ => .cbn 0
  | .bc _ => .bc 0
  | q => q

variable (V : Verifier)

theorem itemT_rep (q : TEq) : itemT V (tRep q) = itemT V q := by
  cases q <;> rfl

/-- A piece of the TIME catalog. -/
structure TPiece where
  c : Cnt
  eq : ℕ → TEq
  jk : JK
  hrep : ∀ i, tRep (eq i) = tRep (eq 0)
  hjk : ∀ i, tBit (eq i) = jk.val i

/-- Its printer. -/
def TPiece.prog (pc : TPiece) : P := .loop vI pc.c.e (.bind vJ pc.jk.e (itemT V (tRep (pc.eq 0))))

/-- A range piece. -/
def rp (c : Cnt) (mk : ℕ → TEq) (hrep : ∀ i, tRep (mk i) = tRep (mk 0)) (hjk : ∀ i, tBit (mk i) = i) : TPiece :=
  ⟨c, mk, .idx, hrep, hjk⟩

/-- A single equation. -/
def sp (q : TEq) (hq : tBit q = 0) : TPiece := ⟨.one, fun _ => q, .zero, fun _ => rfl, fun _ => hq⟩

/-- **The pieces of the TIME catalog** (`K` registers, `L` code positions). -/
def tPieces (K L : ℕ) : List TPiece :=
  (List.range K).map (fun r => rp .w (TEq.flag r) (fun _ => rfl) (fun _ => rfl)) ++ [sp .decFirst rfl] ++
  (List.range (L - 1)).map (fun p => sp (.decRec (p + 1)) rfl) ++
  (List.range (L - 1)).map (fun p => sp (.decExcl (p + 1)) rfl) ++ [sp .decLast rfl] ++
  [rp .w TEq.decPc (fun _ => rfl) (fun _ => rfl), rp .w TEq.opX (fun _ => rfl) (fun _ => rfl),
   rp .w TEq.opY (fun _ => rfl) (fun _ => rfl), sp .opXF rfl, rp .w TEq.sumAD (fun _ => rfl) (fun _ => rfl),
   rp .wm1 TEq.carry (fun _ => rfl) (fun _ => rfl), rp .w TEq.sumSB (fun _ => rfl) (fun _ => rfl),
   rp .w TEq.borrow (fun _ => rfl) (fun _ => rfl), rp .w TEq.andAN (fun _ => rfl) (fun _ => rfl), sp .ozFirst rfl,
   ⟨.wm1, fun j => TEq.ozRec (j + 1), .idx1, fun _ => rfl, fun _ => rfl⟩, sp .gt rfl,
   rp .w TEq.rfFlag (fun _ => rfl) (fun _ => rfl), rp .w TEq.store (fun _ => rfl) (fun _ => rfl),
   rp .w TEq.res (fun _ => rfl) (fun _ => rfl), sp .resF rfl] ++
  (List.range K).map (fun r => rp .w (TEq.reg r) (fun _ => rfl) (fun _ => rfl)) ++
  (List.range K).map (fun r => sp (.regF r) rfl) ++
  [rp .w TEq.pcNext (fun _ => rfl) (fun _ => rfl), sp .recAct rfl, sp .recRgn rfl,
   rp .w TEq.recAd (fun _ => rfl) (fun _ => rfl), sp .recPh rfl, rp .w TEq.recVa (fun _ => rfl) (fun _ => rfl),
   sp .recSt rfl, rp .tau TEq.tsn (fun _ => rfl) (fun _ => rfl), rp .taum1 TEq.tc (fun _ => rfl) (fun _ => rfl),
   sp .aA rfl, rp .tau TEq.can (fun _ => rfl) (fun _ => rfl), rp .taum1 TEq.ac (fun _ => rfl) (fun _ => rfl),
   sp .aB rfl, rp .beta1 TEq.cbn (fun _ => rfl) (fun _ => rfl), rp .beta TEq.bc (fun _ => rfl) (fun _ => rfl),
   sp .bound rfl]

theorem range_one_map {α : Type} (f : ℕ → α) : (List.range 1).map f = [f 0] := rfl

/-- **The TIME catalog is the concatenation of its pieces.** -/
theorem timeEqList_pieces (d : Dims) :
    timeEqList d = (tPieces d.K d.L).flatMap (fun pc => (List.range (pc.c.val d)).map pc.eq) := by
  simp [timeEqList, tPieces, List.flatMap_append, List.flatMap_map, rp, sp, Cnt.val, Function.comp_def,
    List.flatMap_singleton', range_one_map, flatMap_singleton_eq_map]

/-! ## The printer of the pieces -/

theorem cnt_le_w (r : ClockRequest) (c : Cnt) : c.val (dims (ownRam V r) (tau V r.2)) ≤ wordW V r.2 := by
  rw [dims_own V r]
  have hτ := tau_lt_wordW_all V r.2
  have : 1 ≤ wordW V r.2 := by omega
  cases c <;> simp only [Cnt.val] <;> omega

theorem wordW_lt_dom (t : ℕ) : wordW V t < 2 ^ domExp V t := by
  rw [wordW_eq]; exact Nat.pow_lt_pow_right (by norm_num) (by unfold domExp colExp; omega)

theorem cnt_eval (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (c : Cnt) :
    min (evalE G s c.e) G.N = c.val (dims (ownRam V r) (tau V r.2)) := by
  rw [dims_own V r]
  have hτ := tau_lt_wordW_all V r.2
  have hN := hR.mN
  have hc := hR.cap
  have h16 := cB_16 V
  have hp := Nat.two_pow_pos (domExp V r.2 + 8)
  have h2 := wordW_lt_dom V r.2
  have h3 : 2 ^ domExp V r.2 ≤ 2 ^ (domExp V r.2 + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : min 1 G.cap = 1 := min_cap (by omega)
  have hw := hb.pv.w
  have ht := hb.pv.ta
  have ho := hb.pv.om
  have hwτ := wordExp_le_tau V r.2
  cases c <;> simp only [Cnt.e, Cnt.val, evalE, hw, ht, ho, h1, betaE] <;> omega

theorem jk_eval {s : FS} (i : ℕ) (hc : i + 1 ≤ G.cap) (jk : JK) : evalE G (s.setv vI i) jk.e = jk.val i := by
  cases jk <;> simp [JK.e, JK.val, evalE, k0, min_cap (show 1 ≤ G.cap by omega), min_cap hc]

theorem not_baseA_vI : ¬ baseA vI := by unfold baseA vI vKL vUK vP5 vP6 vD; decide
theorem not_baseA_vJ : ¬ baseA vJ := by unfold baseA vJ vKL vUK vP5 vP6 vD; decide

/-- **One piece** prints the items of its equations. -/
theorem den_piece {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) (pc : TPiece)
    (hact : ∀ i < pc.c.val (dims (ownRam V r) (tau V r.2)), (pc.eq i).Active (dims (ownRam V r) (tau V r.2))) :
    den G s (pc.prog V) = ((List.range (pc.c.val (dims (ownRam V r) (tau V r.2)))).map pc.eq).flatMap
      (fun q => itemNums mk (tItem V r q)) := by
  rw [TPiece.prog, den_loop s vI _ _ _ (cnt_eval V r hR hb pc.c) (fun i => itemNums mk (tItem V r (pc.eq i))),
    List.flatMap_map]
  intro i hi
  have hiw : i + 1 ≤ G.cap := by
    have h1 := cnt_le_w V r pc.c
    have h2 := wordW_lt_dom V r.2
    have h3 : 2 ^ domExp V r.2 ≤ 2 ^ (domExp V r.2 + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc := hR.cap
    omega
  simp only [den]
  rw [jk_eval i hiw, ← pc.hjk i, pc.hrep i |>.symm, itemT_rep]
  exact den_itemT V mk hm0 hm1 r hR ((hb.setv V vI not_baseA_vI i).setv V vJ not_baseA_vJ _) (pc.eq i) (hact i hi)
    (by simp)

/-- **The printer of the TIME block.** -/
def tBlockP : P := seqL ((tPieces (regCount V) (codeLen V)).map (TPiece.prog V))

theorem timeEqList_own (r : ClockRequest) :
    timeEqList (dims (ownRam V r) (tau V r.2)) = (tPieces (regCount V) (codeLen V)).flatMap
      (fun pc => (List.range (pc.c.val (dims (ownRam V r) (tau V r.2)))).map pc.eq) := by
  have h := timeEqList_pieces (dims (ownRam V r) (tau V r.2))
  have hL : (dims (ownRam V r) (tau V r.2)).L = codeLen V := mnCode_length V _ _ _ _
  rw [hL] at h
  exact h

/-- **The TIME block prints the time items of `machineItems`.** -/
theorem den_tBlock {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    (r : ClockRequest) (hR : Room V r G) {s : FS} (hb : Base V r s) :
    den G s (tBlockP V) =
      (timeEqList (dims (ownRam V r) (tau V r.2))).flatMap (fun q => itemNums mk (tItem V r q)) := by
  rw [tBlockP, den_seqL, List.flatMap_map, timeEqList_own V r, List.flatMap_assoc]
  apply List.flatMap_congr
  intro pc hpc
  apply den_piece V mk hm0 hm1 r hR hb pc
  intro i hi
  apply mem_timeEqList
  rw [timeEqList_own V r]
  exact List.mem_flatMap.mpr ⟨pc, hpc, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩

end NearCubicGates.Adapters.RAMACSP.Gen.Items
