import Proof.Gates.CheckedPCPP.Framed.Core
import Mathlib.Computability.TuringMachine.Computable

namespace NearCubicGates.Close.FramedSim
open NearCubicWires
open LocalBitMultitape RepairOrdinary Turing
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `FinTM2` carries its finiteness data as plain fields; expose them as instances. -/
instance finTM2FintypeK (tm : FinTM2) : Fintype tm.K := tm.kFin
instance finTM2FintypeΛ (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin
instance finTM2Fintypeσ (tm : FinTM2) : Fintype tm.σ := tm.σFin

/-! ## Control skeleton, generic in its data types -/

/-- What to do with a popped code. -/
inductive RCont (P S : Type) where
  | pop (q : P) (v : S)
  | peek (q : P) (v : S)
  | tr
  | out
  deriving Fintype

/-- Resting points between macros. -/
inductive Cont (P S : Type) (t : ℕ) where
  | exec (q : P) (v : S)
  | ldScan
  | ldBit
  | popAt (i : Fin t) (r : RCont P S)
  | done
  deriving Fintype

/-- The finite control. -/
inductive Ctl (P S C : Type) (t B : ℕ) where
  | at (c : Cont P S t)
  | push (i : Fin t) (c : C) (j : Fin (B + 2)) (after : Cont P S t)
  | read (i : Fin t) (j : Fin B) (acc : Fin B → Bool) (r : RCont P S)
  | back (i : Fin t) (j : Fin (B + 1)) (after : Cont P S t)
  | emit (c : C)
  | emitBit (c : C)
  deriving Fintype

section Machine
variable (tm : FinTM2)

/-! ## Program points -/

open Classical in
/-- All statement subtrees of all labels: a finite set. -/
noncomputable def allStmts : Finset (TM2.Stmt tm.Γ tm.Λ tm.σ) :=
  Finset.univ.biUnion fun l => TM2.stmts₁ (tm.m l)

/-- Program points. -/
abbrev Pt := {q // q ∈ allStmts tm}

theorem mem_allStmts_self (l : tm.Λ) : tm.m l ∈ allStmts tm := by
  classical
  unfold allStmts
  exact Finset.mem_biUnion.2 ⟨l, Finset.mem_univ _, TM2.stmts₁_self⟩

theorem mem_allStmts_of {q q' : TM2.Stmt tm.Γ tm.Λ tm.σ} (h : q' ∈ TM2.stmts₁ q)
    (hq : q ∈ allStmts tm) : q' ∈ allStmts tm := by
  classical
  unfold allStmts at hq ⊢
  obtain ⟨l, hl, hql⟩ := Finset.mem_biUnion.1 hq
  exact Finset.mem_biUnion.2 ⟨l, hl, TM2.stmts₁_trans hql h⟩

noncomputable def mainPt : Pt tm := ⟨tm.m tm.main, mem_allStmts_self tm tm.main⟩

open Classical in
/-- The program point of a statement (junk outside the program). -/
noncomputable def mkPt (q : TM2.Stmt tm.Γ tm.Λ tm.σ) : Pt tm :=
  if h : q ∈ allStmts tm then ⟨q, h⟩ else mainPt tm

theorem mkPt_of_mem {q : TM2.Stmt tm.Γ tm.Λ tm.σ} (h : q ∈ allStmts tm) : mkPt tm q = ⟨q, h⟩ := by
  classical
  unfold mkPt
  rw [dif_pos h]

/-! ## Codes -/

/-- Stack-cell codes: an input bit, or (push statement, state). -/
abbrev Src := Bool ⊕ (Pt tm × tm.σ)

/-- Bits per code. -/
noncomputable def codeWidth : ℕ := Fintype.card (Src tm)

theorem codeWidth_pos : 0 < codeWidth tm := by
  unfold codeWidth
  rw [Fintype.card_sum, Fintype.card_bool]
  omega

/-- One-hot code bits. -/
noncomputable def enc (c : Src tm) : Fin (codeWidth tm) → Bool :=
  fun r => decide (Fintype.equivFin (Src tm) c = r)

theorem enc_injective : Function.Injective (enc tm) := by
  intro c d h
  have h1 := congrFun h (Fintype.equivFin (Src tm) c)
  simp only [enc, decide_true] at h1
  have h2 : Fintype.equivFin (Src tm) d = Fintype.equivFin (Src tm) c := by
    by_contra hne
    rw [decide_eq_false hne] at h1
    exact Bool.noConfusion h1
  exact ((Fintype.equivFin (Src tm)).injective h2).symm

open Classical in
/-- Decoding of an accumulator. -/
noncomputable def dec (acc : Fin (codeWidth tm) → Bool) : Option (Src tm) :=
  if h : ∃ c, enc tm c = acc then some h.choose else none

theorem dec_enc (c : Src tm) : dec tm (enc tm c) = some c := by
  classical
  have h : ∃ d, enc tm d = enc tm c := ⟨c, rfl⟩
  unfold dec
  rw [dif_pos h]
  exact congrArg some (enc_injective tm h.choose_spec)

/-- The value pushed by a push statement. -/
def pushVal : TM2.Stmt tm.Γ tm.Λ tm.σ → tm.σ → (k : tm.K) → Option (tm.Γ k)
  | .push k' f _, v, k => if h : k' = k then some (h ▸ f v) else none
  | _, _, _ => none

/-- The stack symbol a code stands for on stack `k`. -/
def val (ein : tm.Γ tm.k₀ ≃ Bool) (k : tm.K) : Src tm → Option (tm.Γ k)
  | .inl b => if h : tm.k₀ = k then some (h ▸ ein.symm b) else none
  | .inr (q, v) => pushVal tm q.1 v k

theorem val_inl_k₀ (ein : tm.Γ tm.k₀ ≃ Bool) (b : Bool) :
    val tm ein tm.k₀ (.inl b) = some (ein.symm b) := by
  simp [val]

theorem val_push (ein : tm.Γ tm.k₀ ≃ Bool) (k : tm.K) (f : tm.σ → tm.Γ k)
    (q' : TM2.Stmt tm.Γ tm.Λ tm.σ) (h : TM2.Stmt.push k f q' ∈ allStmts tm) (v : tm.σ) :
    val tm ein k (.inr (⟨.push k f q', h⟩, v)) = some (f v) := by
  simp [val, pushVal]

/-- The output bit of a code (junk `false` for codes that are not output symbols). -/
def outBit (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool) (c : Src tm) : Bool :=
  match val tm ein tm.k₁ c with
  | some x => eout x
  | none => false

/-- The framed output cells: a `true` marker before each bit (`frame w = pairs w ++ [false]`). -/
def pairs (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

@[simp] theorem pairs_nil : pairs [] = [] := rfl

@[simp] theorem pairs_cons (b : Bool) (w : List Bool) : pairs (b :: w) = true :: b :: pairs w := rfl

@[simp] theorem pairs_append (u w : List Bool) : pairs (u ++ w) = pairs u ++ pairs w := by
  simp [pairs]

@[simp] theorem pairs_length (w : List Bool) : (pairs w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]; ring

theorem frame_eq_pairs : ∀ w : List Bool, RepairOrdinary.frame w = pairs w ++ [false]
  | [] => rfl
  | b :: w => by simp [RepairOrdinary.frame, frame_eq_pairs w]

/-! ## Tapes -/

/-- Tape count: input, scratch, one per stack, output. -/
abbrev nT : ℕ := Fintype.card tm.K + 3

def inTape : Fin (nT tm) := ⟨0, by show 0 < Fintype.card tm.K + 3; omega⟩
def tmpTape : Fin (nT tm) := ⟨1, by show 1 < Fintype.card tm.K + 3; omega⟩
noncomputable def stkTape (k : tm.K) : Fin (nT tm) :=
  ⟨(Fintype.equivFin tm.K k).val + 2, by
    show _ < Fintype.card tm.K + 3; have := (Fintype.equivFin tm.K k).isLt; omega⟩
def outTape : Fin (nT tm) := ⟨Fintype.card tm.K + 2, by show _ < Fintype.card tm.K + 3; omega⟩

theorem stkTape_injective : Function.Injective (stkTape tm) := by
  intro k k' h
  have h' : (Fintype.equivFin tm.K k).val = (Fintype.equivFin tm.K k').val := by
    have := congrArg Fin.val h
    simp only [stkTape] at this
    omega
  exact (Fintype.equivFin tm.K).injective (Fin.ext h')

theorem stkTape_ne_in (k : tm.K) : stkTape tm k ≠ inTape tm := by
  intro h; have := congrArg Fin.val h; simp [stkTape, inTape] at this

theorem stkTape_ne_tmp (k : tm.K) : stkTape tm k ≠ tmpTape tm := by
  intro h; have := congrArg Fin.val h; simp [stkTape, tmpTape] at this

theorem stkTape_ne_out (k : tm.K) : stkTape tm k ≠ outTape tm := by
  intro h
  have := congrArg Fin.val h
  have hk := (Fintype.equivFin tm.K k).isLt
  simp [stkTape, outTape] at this
  omega

theorem tmpTape_ne_in : tmpTape tm ≠ inTape tm := by
  intro h; have := congrArg Fin.val h; simp [tmpTape, inTape] at this

theorem tmpTape_ne_out : tmpTape tm ≠ outTape tm := by
  intro h; have := congrArg Fin.val h; simp [tmpTape, outTape] at this

theorem inTape_ne_out : inTape tm ≠ outTape tm := by
  intro h; have := congrArg Fin.val h; simp [inTape, outTape] at this

theorem outTape_ne_zero : (outTape tm).val ≠ 0 := by simp [outTape]

/-! ## The control and the rule -/

abbrev C := Ctl (Pt tm) tm.σ (Src tm) (nT tm) (codeWidth tm)
abbrev Rc := RCont (Pt tm) tm.σ
abbrev Ct := Cont (Pt tm) tm.σ (nT tm)

/-- The control after the one dispatch step of a statement. -/
noncomputable def execNext : TM2.Stmt tm.Γ tm.Λ tm.σ → Pt tm → tm.σ → C tm
  | .push k _ q', self, v => .push (stkTape tm k) (.inr (self, v)) ⟨0, by omega⟩ (.exec (mkPt tm q') v)
  | .peek k _ _, self, v => .at (.popAt (stkTape tm k) (.peek self v))
  | .pop k _ _, self, v => .at (.popAt (stkTape tm k) (.pop self v))
  | .load a q', _, v => .at (.exec (mkPt tm q') (a v))
  | .branch f q₁ q₂, _, v => .at (.exec (mkPt tm (cond (f v) q₁ q₂)) v)
  | .goto f, _, v => .at (.exec (mkPt tm (tm.m (f v))) v)
  | .halt, _, _ => .at (.popAt (stkTape tm tm.k₁) .out)

noncomputable def resumePop (ein : tm.Γ tm.k₀ ≃ Bool) :
    TM2.Stmt tm.Γ tm.Λ tm.σ → tm.σ → Option (Src tm) → C tm
  | .pop k f q', v, x => .at (.exec (mkPt tm q') (f v (x.bind (val tm ein k))))
  | _, _, _ => .at .done

noncomputable def resumePeek (ein : tm.Γ tm.k₀ ≃ Bool) :
    TM2.Stmt tm.Γ tm.Λ tm.σ → tm.σ → Option (Src tm) → C tm
  | .peek _ f q', v, none => .at (.exec (mkPt tm q') (f v none))
  | .peek k f q', v, some c => .back (stkTape tm k) ⟨0, by omega⟩ (.exec (mkPt tm q') (f v (val tm ein k c)))
  | _, _, _ => .at .done

/-- The control after a pop macro, given the popped code (`none`: the stack was empty). -/
noncomputable def resume (ein : tm.Γ tm.k₀ ≃ Bool) : Rc tm → Option (Src tm) → C tm
  | .pop q v, x => resumePop tm ein q.1 v x
  | .peek q v, x => resumePeek tm ein q.1 v x
  | .tr, none => .at (.exec (mainPt tm) tm.initialState)
  | .tr, some c => .push (stkTape tm tm.k₀) c ⟨0, by omega⟩ (.popAt (tmpTape tm) .tr)
  | .out, none => .at .done
  | .out, some c => .emit c

def isDone : C tm → Bool
  | .at .done => true
  | _ => false

noncomputable def tapeOf : C tm → Fin (nT tm)
  | .at (.popAt i _) => i
  | .at _ => inTape tm
  | .push i _ _ _ => i
  | .read i _ _ _ => i
  | .back i _ _ => i
  | .emit _ => outTape tm
  | .emitBit _ => outTape tm

/-- The rule: next control, write and move on the control's one tape, from the scanned bit. -/
noncomputable def rule (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool) :
    C tm → Bool → C tm × Option Bool × HeadMove
  | .at (.exec q v), _ => (execNext tm q.1 q v, none, .stay)
  | .at .ldScan, b =>
      if b then (.at .ldBit, none, .right) else (.at (.popAt (tmpTape tm) .tr), none, .stay)
  | .at .ldBit, b => (.push (tmpTape tm) (.inl b) ⟨0, by omega⟩ .ldScan, none, .right)
  | .at (.popAt i r), b =>
      if b then (.read i ⟨0, codeWidth_pos tm⟩ (fun _ => false) r, none, .left)
      else (resume tm ein r none, none, .stay)
  | .at .done, _ => (.at .done, none, .stay)
  | .push i c j after, _ =>
      if j.val = 0 then (.push i c ⟨1, by omega⟩ after, none, .right)
      else if h : j.val ≤ codeWidth tm then
        (.push i c ⟨j.val + 1, by omega⟩ after, some ((blk (enc tm) c).getD (j.val - 1) false),
          .right)
      else (.at after, some ((blk (enc tm) c).getD (j.val - 1) false), .stay)
  | .read i j acc r, b =>
      if h : j.val + 1 < codeWidth tm then
        (.read i ⟨j.val + 1, h⟩ (setBit acc (codeWidth tm - 1 - j.val) b) r, none, .left)
      else (resume tm ein r (dec tm (setBit acc (codeWidth tm - 1 - j.val) b)), none, .left)
  | .back i j after, _ =>
      if h : j.val + 1 < codeWidth tm + 1 then (.back i ⟨j.val + 1, h⟩ after, none, .right)
      else (.at after, none, .right)
  | .emit c, _ => (.emitBit c, some true, .right)
  | .emitBit c, _ => (.at (.popAt (stkTape tm tm.k₁) .out), some (outBit tm ein eout c), .right)

/-- **The simulating machine.** -/
noncomputable def machine (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool) :
    Machine (nT tm) (Fintype.card (C tm)) :=
  mk (.at .ldScan) (isDone tm) (tapeOf tm) (rule tm ein eout)

/-- The control numbering. -/
noncomputable abbrev code : C tm ≃ Fin (Fintype.card (C tm)) := Fintype.equivFin (C tm)

variable (ein : tm.Γ tm.k₀ ≃ Bool) (eout : tm.Γ tm.k₁ ≃ Bool)

theorem machine_start : (machine tm ein eout).start = code tm (.at .ldScan) := rfl

theorem machine_halted_done : (machine tm ein eout).halted (code tm (.at .done)) = true := by
  simp [machine, mk_halted, isDone]

theorem loc (q : C tm) (hq : isDone tm q = false) :
    Local (machine tm ein eout) (code tm q) (tapeOf tm q)
      (fun b => (code tm (rule tm ein eout q b).1, (rule tm ein eout q b).2.1,
        (rule tm ein eout q b).2.2)) :=
  mk_local _ _ _ _ q hq

theorem Local.congr' {t s : ℕ} {M : Machine t s} {q : Fin s} {i : Fin t}
    {f f' : Bool → Fin s × Option Bool × HeadMove} (h : Local M q i f) (hf : ∀ b, f b = f' b) :
    Local M q i f' := by
  have : f = f' := funext hf
  subst this
  exact h

theorem act_none_stay {t s : ℕ} (C0 : Configuration t s) (q : Fin s) (i : Fin t) :
    act C0 q i none .stay = ⟨q, C0.heads, C0.tapes⟩ := by
  apply configuration_ext
  · rfl
  · simp [act, HeadMove.apply_stay]
  · simp

/-! ## The three stack macros of this machine, with exact step counts -/

/-- Push: `codeWidth + 2` steps. -/
theorem push_op (i : Fin (nT tm)) (c : Src tm) (after : Ct tm) (cs : List (Src tm))
    (C0 : Configuration (nT tm) (Fintype.card (C tm)))
    (hC : C0.control = code tm (.push i c ⟨0, by omega⟩ after))
    (hh : C0.heads i = cs.length * (codeWidth tm + 1))
    (ha : Agrees (C0.tapes i) (lay (enc tm) cs)) :
    ∃ C', Runs (machine tm ein eout) (codeWidth tm + 2) C0 C' ∧
      C'.control = code tm (.at after) ∧
      C'.heads i = (cs.length + 1) * (codeWidth tm + 1) ∧
      Agrees (C'.tapes i) (lay (enc tm) (c :: cs)) ∧
      (∀ j, j ≠ i → C'.heads j = C0.heads j ∧ C'.tapes j = C0.tapes j) := by
  set P : ℕ → Fin (Fintype.card (C tm)) := fun j =>
    if h : j < codeWidth tm + 2 then code tm (.push i c ⟨j, h⟩ after) else code tm (.at .done)
    with hP
  have hX : (blk (enc tm) c).length = codeWidth tm + 1 := blk_length _ c
  have h0 : Local (machine tm ein eout) (P 0) i (fun _ => (P 1, none, .right)) := by
    have := loc tm ein eout (.push i c ⟨0, by omega⟩ after) rfl
    simp only [hP, dif_pos (show 0 < codeWidth tm + 2 by omega),
      dif_pos (show 1 < codeWidth tm + 2 by omega)]
    refine Local.congr' this (fun b => ?_)
    simp [rule]
  have hmid : ∀ j, j + 1 < (blk (enc tm) c).length →
      Local (machine tm ein eout) (P (j + 1)) i
        (fun _ => (P (j + 2), some ((blk (enc tm) c).getD j false), .right)) := by
    intro j hj
    rw [hX] at hj
    have := loc tm ein eout (.push i c ⟨j + 1, by omega⟩ after) rfl
    simp only [hP, dif_pos (show j + 1 < codeWidth tm + 2 by omega),
      dif_pos (show j + 2 < codeWidth tm + 2 by omega)]
    refine Local.congr' this (fun b => ?_)
    simp only [rule]
    rw [if_neg (by simp), dif_pos (by simp; omega)]
    simp
  have hlast : Local (machine tm ein eout) (P (blk (enc tm) c).length) i
      (fun _ => (code tm (.at after), some ((blk (enc tm) c).getD ((blk (enc tm) c).length - 1)
        false), .stay)) := by
    rw [hX]
    have := loc tm ein eout (.push i c ⟨codeWidth tm + 1, by omega⟩ after) rfl
    simp only [hP, dif_pos (show codeWidth tm + 1 < codeWidth tm + 2 by omega)]
    refine Local.congr' this (fun b => ?_)
    simp only [rule]
    rw [if_neg (by simp), dif_neg (by simp)]
  obtain ⟨C', hr, hc, hh', hread, hoth⟩ :=
    push_runs i (blk (enc tm) c) (by rw [hX]; omega) P (code tm (.at after)) h0 hmid hlast C0
      (by rw [hC]; simp [hP])
  refine ⟨C', hr.of_eq (by rw [hX]), hc, ?_, ?_, hoth⟩
  · rw [hh', hh, hX]; ring
  · exact ha.push (enc tm) c (by rw [← hh]; exact hread)

/-- Pop of an empty stack: one step, nothing moves. -/
theorem pop_op_nil (i : Fin (nT tm)) (r : Rc tm)
    (C0 : Configuration (nT tm) (Fintype.card (C tm)))
    (hC : C0.control = code tm (.at (.popAt i r)))
    (hh : C0.heads i = 0) (ha : Agrees (C0.tapes i) (lay (enc tm) [])) :
    Runs (machine tm ein eout) 1 C0 ⟨code tm (resume tm ein r none), C0.heads, C0.tapes⟩ := by
  have hl := (loc tm ein eout (.at (.popAt i r)) rfl).runs C0 hC
  have hb : C0.scanned i = false := by
    simp only [Configuration.scanned, hh]
    exact ha.flag_nil (enc tm)
  simp only [tapeOf, hb, rule] at hl
  simpa [act_none_stay] using hl

/-- Pop of a nonempty stack: `1 + codeWidth` steps; the head lands on the new top; no tape
changes; the popped code is decoded exactly. -/
theorem pop_op_cons (i : Fin (nT tm)) (r : Rc tm) (c : Src tm) (cs : List (Src tm))
    (C0 : Configuration (nT tm) (Fintype.card (C tm)))
    (hC : C0.control = code tm (.at (.popAt i r)))
    (hh : C0.heads i = (cs.length + 1) * (codeWidth tm + 1))
    (ha : Agrees (C0.tapes i) (lay (enc tm) (c :: cs))) :
    ∃ C', Runs (machine tm ein eout) (1 + codeWidth tm) C0 C' ∧
      C'.control = code tm (resume tm ein r (some c)) ∧
      C'.heads i = cs.length * (codeWidth tm + 1) ∧ C'.tapes = C0.tapes ∧
      (∀ j, j ≠ i → C'.heads j = C0.heads j) := by
  have hl := (loc tm ein eout (.at (.popAt i r)) rfl).runs C0 hC
  have hb : C0.scanned i = true := by
    simp only [Configuration.scanned, hh]
    exact ha.flag_cons (enc tm)
  simp only [tapeOf, hb, rule, if_true] at hl
  set C1 := act C0 (code tm (.read i ⟨0, codeWidth_pos tm⟩ (fun _ => false) r)) i none .left
    with hC1
  set G : ℕ → (Fin (codeWidth tm) → Bool) → Fin (Fintype.card (C tm)) := fun j acc =>
    if h : j < codeWidth tm then code tm (.read i ⟨j, h⟩ acc r) else code tm (.at .done) with hG
  have hGl : ∀ j acc, j < codeWidth tm → Local (machine tm ein eout) (G j acc) i (fun b =>
      (if j + 1 < codeWidth tm then G (j + 1) (setBit acc (codeWidth tm - 1 - j) b)
        else code tm (resume tm ein r (dec tm (setBit acc (codeWidth tm - 1 - j) b))),
        none, .left)) := by
    intro j acc hj
    have := loc tm ein eout (.read i ⟨j, hj⟩ acc r) rfl
    simp only [hG, dif_pos hj]
    refine Local.congr' this (fun b => ?_)
    simp only [rule]
    by_cases hj1 : j + 1 < codeWidth tm
    · rw [dif_pos hj1, if_pos hj1, dif_pos hj1]
    · rw [dif_neg hj1, if_neg hj1]
  have hbase : C1.heads i = cs.length * (codeWidth tm + 1) + codeWidth tm := by
    simp only [hC1, act_heads_self, HeadMove.apply_left, hh]; ring_nf; omega
  obtain ⟨C', hr, hc, hh', ht, hoth⟩ :=
    read_runs i (codeWidth tm) (codeWidth_pos tm) G
      (fun acc => code tm (resume tm ein r (dec tm acc))) hGl
      (cs.length * (codeWidth tm + 1)) C1
      (by simp [hC1, hG, codeWidth_pos tm]) hbase
  refine ⟨C', Runs.trans hl hr, ?_, hh', ?_, ?_⟩
  · rw [hc]
    congr 2
    have hcode : (fun r : Fin (codeWidth tm) =>
        readTapeBit (C1.tapes i) (cs.length * (codeWidth tm + 1) + 1 + r.val)) = enc tm c := by
      funext r
      have hC1t : C1.tapes = C0.tapes := by simp [hC1]
      rw [hC1t]
      exact ha.code (enc tm) r
    rw [hcode, dec_enc]
  · rw [ht]; simp [hC1]
  · intro j hj
    rw [hoth j hj, hC1, act_heads_ne _ _ _ _ _ _ hj]

/-- Peek's return: `codeWidth + 1` right moves. -/
theorem back_op (i : Fin (nT tm)) (after : Ct tm)
    (C0 : Configuration (nT tm) (Fintype.card (C tm)))
    (hC : C0.control = code tm (.back i ⟨0, by omega⟩ after)) :
    ∃ C', Runs (machine tm ein eout) (codeWidth tm + 1) C0 C' ∧
      C'.control = code tm (.at after) ∧ C'.heads i = C0.heads i + (codeWidth tm + 1) ∧
      C'.tapes = C0.tapes ∧ (∀ j, j ≠ i → C'.heads j = C0.heads j) := by
  set Bk : ℕ → Fin (Fintype.card (C tm)) := fun j =>
    if h : j < codeWidth tm + 1 then code tm (.back i ⟨j, h⟩ after) else code tm (.at .done)
    with hBk
  have hl : ∀ j, j < codeWidth tm + 1 → Local (machine tm ein eout) (Bk j) i (fun _ =>
      (if j + 1 < codeWidth tm + 1 then Bk (j + 1) else code tm (.at after), none, .right)) := by
    intro j hj
    have := loc tm ein eout (.back i ⟨j, hj⟩ after) rfl
    simp only [hBk, dif_pos hj]
    refine Local.congr' this (fun b => ?_)
    simp only [rule]
    by_cases hj1 : j + 1 < codeWidth tm + 1
    · rw [dif_pos hj1, if_pos hj1, dif_pos hj1]
    · rw [dif_neg hj1, if_neg hj1]
  exact back_runs i (codeWidth tm + 1) (by omega) Bk (code tm (.at after)) hl C0
    (by rw [hC]; simp [hBk])

end Machine

end NearCubicGates.Close.FramedSim
