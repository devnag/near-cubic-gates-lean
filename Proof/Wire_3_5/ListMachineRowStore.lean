import Proof.Wire_3_5.ListMachineRowRows

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun atomCode monoBits recW polyWord)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5
open NearCubicWires.BlockPlatform

/-- The work tapes of the factor layout: all but the record and the output. -/
def scr (t : ℕ) (i : Fin (1 + (14 + t) + 1)) : Bool := decide (i ≠ srcO t ∧ i ≠ outI t)

theorem fA_outI {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) (log : List Bool) :
    fA src b data log (outI t) = b.o := by
  rw [outI_eq, fA_prSlot]; simp [Bank.tapes]

theorem fA_logI {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) (log : List Bool) :
    fA src b data log (logI t) = log := by simp [fA, logI]

/-- The factor layout at rest: the record, the output, every work tape blank of length `R`. -/
def restA (t : ℕ) (src o : List Bool) (R : ℕ) : Fin (1 + (14 + t) + 1) → List Bool :=
  fun i => if i = srcO t then src else if i = outI t then o else List.replicate R false

theorem blank_fA (t : ℕ) (src out B : List Bool) (log : List Bool) (R : ℕ) :
    Scrub.blank (scr t) (fA src (entryBank out B) (fun _ : Fin t => []) log) R = restA t src (overlay out B) R := by
  funext i
  unfold Scrub.blank restA scr
  by_cases h1 : i = srcO t
  · subst h1; simp [srcO_ne_outI, fA_srcO]
  · by_cases h2 : i = outI t
    · subst h2; simp [(srcO_ne_outI t).symm, fA_outI, entryBank]
    · simp [h1, h2]

theorem blank_exit (t : ℕ) (A' : Fin (1 + (14 + t) + 1) → List Bool) (src o : List Bool) (R : ℕ)
    (hs : A' (srcO t) = src) (ho : A' (outI t) = o) :
    Scrub.blank (scr t) A' R = restA t src o R := by
  funext i
  unfold Scrub.blank restA scr
  by_cases h1 : i = srcO t
  · subst h1; simp [srcO_ne_outI, hs]
  · by_cases h2 : i = outI t
    · subst h2; simp [(srcO_ne_outI t).symm, ho]
    · simp [h1, h2]

/-- One factor's data, with the side conditions of `factor_step`. -/
structure FSpec (F : EvalFam) where
  L : ℕ
  f : List Bool → Bool
  m : Member F L f
  labs : List ℕ
  d : ℕ
  cap1 : ℕ
  cap2 : ℕ
  hd : 1 ≤ d
  hlabs : L ≤ labs.length
  hc1 : 2 * L + 1 ≤ cap1
  hc2 : ∀ xs : List Bool, xs.length = L → recInnerLCost xs labs ≤ cap1

/-- Its record block, its print, its cost. -/
def FSpec.block {F : EvalFam} (x : FSpec F) : List Bool := factorBlock x.L x.d x.labs x.cap1 x.cap2 x.m.data
def FSpec.poly {F : EvalFam} (x : FSpec F) : List (List ℕ) := factorPoly x.f x.L x.d x.labs
noncomputable def FSpec.cost {F : EvalFam} (x : FSpec F) : ℕ := factorCost F x.m x.d x.labs x.cap1 x.cap2

/-- The scrubbed factor stage. -/
noncomputable def sfactorM (F : EvalFam) := Scrub.machine (factorM F) (scr F.t) (scr F.t)

/-- The scrubbed stage's cost at a capacity `R`. -/
noncomputable def sfCost {F : EvalFam} (x : FSpec F) (R : ℕ) : ℕ := 2 * x.cost + 2 + 1 + (2 * R + 4)

/-- **One scrubbed print**: from the rest bank with the record cursor at a factor block, the output receives the
factor's print and every work tape is blank again. -/
theorem sfactor_step (F : EvalFam) (x : FSpec F) (pre rest out B : List Bool) (R L : ℕ) (hR : x.cost + 1 ≤ R)
    (hL : R + 1 ≤ L) :
    Step (sfactorM F) (sfCost x R) (Scrub.heads (fH F.t pre.length out.length))
      (Scrub.bank (restA F.t (pre ++ x.block ++ rest) (overlay out B) R) R L)
      (Scrub.heads (fH F.t (pre.length + x.block.length) (out ++ Rec.polyWord x.poly).length))
      (Scrub.bank (restA F.t (pre ++ x.block ++ rest) (overlay (out ++ Rec.polyWord x.poly) B) R) R L) := by
  obtain ⟨A', h, hs, ho⟩ := factor_step F x.m x.labs x.d x.hd x.hlabs pre rest out B x.cap1 x.cap2 0 x.hc1 x.hc2
  have hc := Scrub.cleared_entry h (scr F.t) R (by
    intro i hi
    refine ⟨0, Nat.zero_le _, ?_⟩
    rcases cover F.t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
    · simp [scr] at hi
    · rw [fA_prSlot]
      by_cases hc : c = 10
      · subst hc; simp [scr, outI_eq] at hi
      · fin_cases c <;> simp_all [Bank.tapes, entryBank]
    · rw [fA_prSlot]; simp
    · rw [fA_logI])
  rw [blank_fA] at hc
  have hsc := Scrub.step hc (scr F.t) (scr F.t) R L
    (by
      intro i hi
      rcases cover F.t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
      · simp [scr] at hi
      · rw [fH_prSlot]
        by_cases hc : c = 10
        · subst hc; simp [scr, outI_eq] at hi
        · fin_cases c <;> simp_all [bh]
      · rw [fH_prSlot]; simp
      · exact fH_logI F.t _ _)
    (fun i hi => hi)
    (by intro i hi; simp [restA, scr] at hi ⊢; simp [hi.1, hi.2])
    hR hL
  have ehd : Scrub.rewound (scr F.t) (fH F.t (pre.length + (factorBlock x.L x.d x.labs x.cap1 x.cap2 x.m.data).length)
      (out ++ Rec.polyWord (factorPoly x.f x.L x.d x.labs)).length) =
      fH F.t (pre.length + x.block.length) (out ++ Rec.polyWord x.poly).length := by
    funext i
    unfold Scrub.rewound
    by_cases hi : scr F.t i = true
    · rw [if_pos hi]
      rcases cover F.t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
      · simp [scr] at hi
      · rw [fH_prSlot]
        by_cases hc : c = 10
        · subst hc; simp [scr, outI_eq] at hi
        · fin_cases c <;> simp_all [bh]
      · rw [fH_prSlot]; simp
      · exact (fH_logI F.t _ _).symm
    · rw [if_neg hi]; rfl
  have eex : Scrub.blank (scr F.t) (fun i => ZeroPadding.pad (if scr F.t i then R else 0) (A' i)) R =
      restA F.t (pre ++ x.block ++ rest) (overlay (out ++ Rec.polyWord x.poly) B) R := by
    apply blank_exit
    · show ZeroPadding.pad (if scr F.t (srcO F.t) = true then R else 0) (A' (srcO F.t)) = _
      simp only [scr, ne_eq, not_true_eq_false, false_and, decide_false, Bool.false_eq_true, if_false,
        ZeroPadding.pad_zero]
      exact hs
    · show ZeroPadding.pad (if scr F.t (outI F.t) = true then R else 0) (A' (outI F.t)) = _
      simp only [scr, ne_eq, not_true_eq_false, and_false, decide_false, Bool.false_eq_true, if_false,
        ZeroPadding.pad_zero]
      exact ho
  rw [ehd, eex] at hsc
  exact hsc

/-! ## The store loop -/

theorem fH_src_ne (t p p' o : ℕ) (j : Fin (1 + (14 + t) + 1)) (hj : j ≠ srcO t) : fH t p o j = fH t p' o j := by
  rcases cover t j with rfl | ⟨c, rfl⟩ | ⟨i, rfl⟩ | rfl
  · exact absurd rfl hj
  · rw [fH_prSlot, fH_prSlot]
  · rw [fH_prSlot, fH_prSlot]
  · rw [fH_logI, fH_logI]

/-- Pass the marker before a block. -/
noncomputable def skipSrc (t : ℕ) : Machine (1 + (14 + t) + 1 + 1 + 1) 2 :=
  RecoveryFocus.machine ![Scrub.inner (srcO t)] Rec.Skip.machine

theorem skipSrc_step (t p o : ℕ) (A : Fin (1 + (14 + t) + 1 + 1 + 1) → List Bool) :
    Step (skipSrc t) 1 (Scrub.heads (fH t p o)) A (Scrub.heads (fH t (p + 1) o)) A := by
  have hi : Function.Injective ![Scrub.inner (srcO t)] := by intro a b _; exact Subsingleton.elim a b
  have h := dockRun (Rec.Skip.run (A (Scrub.inner (srcO t))) p) ![Scrub.inner (srcO t)] hi (Scrub.heads (fH t p o)) A
    (by intro j; fin_cases j; simp [fH_srcO]) (by intro j; fin_cases j; rfl)
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ hi
    · intro j; fin_cases j; simp [fH_srcO]
    · intro i hi'
      refine Scrub.cover (motive := fun i => (∀ j, ![Scrub.inner (srcO t)] j ≠ i) →
        Scrub.heads (fH t (p + 1) o) i = Scrub.heads (fH t p o) i) (fun k hk => ?_) (fun _ => by simp)
        (fun _ => by simp) i hi'
      rw [Scrub.heads_inner, Scrub.heads_inner]
      apply fH_src_ne
      intro e; subst e; exact hk 0 rfl
  · apply install_eq_of _ hi
    · intro j; fin_cases j; rfl
    · intro i _; rfl

/-- The store's record: every block after a `true` marker, then `false`. -/
def storeRec {F : EvalFam} (xs : List (FSpec F)) : List Bool := xs.flatMap (fun x => true :: x.block) ++ [false]

/-- The store's contents: the prints in order. -/
def storeW {F : EvalFam} (xs : List (FSpec F)) : List Bool := xs.flatMap fun x => Rec.polyWord x.poly

/-- The store body: pass the marker, print the block's factor, scrub. -/
noncomputable def storeBody (F : EvalFam) := Composition.machine (skipSrc F.t) (sfactorM F)

/-- **The store loop.** -/
noncomputable def storeM (F : EvalFam) :=
  StreamController.machine (storeBody F) (Scrub.inner (srcO F.t))

/-- The cost of pass `j` at capacity `R`. -/
noncomputable def storePass {F : EvalFam} (xs : List (FSpec F)) (R j : ℕ) : ℕ :=
  (xs[j]?.map fun x => 1 + 1 + sfCost x R).getD 0

/-- Its cost at capacity `R`. -/
noncomputable def storeCost {F : EvalFam} (xs : List (FSpec F)) (R : ℕ) : ℕ :=
  ((List.range xs.length).map fun j => storePass xs R j + 2).sum + 1

theorem flatMap_take_succ' {α β : Type} (f : α → List β) (l : List α) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).flatMap f = (l.take j).flatMap f ++ f l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem storeRec_split {F : EvalFam} (xs : List (FSpec F)) (j : ℕ) (hj : j < xs.length) :
    storeRec xs = ((xs.take j).flatMap (fun x => true :: x.block) ++ [true]) ++ xs[j].block ++
      ((xs.drop (j + 1)).flatMap (fun x => true :: x.block) ++ [false]) := by
  conv_lhs => rw [storeRec, ← List.take_append_drop j xs, List.drop_eq_getElem_cons hj]
  simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- **The store loop**: the output receives every block's print, in order; the work tapes end blank. -/
theorem store_run (F : EvalFam) (xs : List (FSpec F)) (pre rest out B : List Bool) (R L : ℕ)
    (hR : ∀ x ∈ xs, x.cost + 1 ≤ R) (hL : R + 1 ≤ L) :
    Step (storeM F) (storeCost xs R) (Scrub.heads (fH F.t pre.length out.length))
      (Scrub.bank (restA F.t (pre ++ storeRec xs ++ rest) (overlay out B) R) R L)
      (Scrub.heads (fH F.t (pre.length + (xs.flatMap fun x => true :: x.block).length) (out ++ storeW xs).length))
      (Scrub.bank (restA F.t (pre ++ storeRec xs ++ rest) (overlay (out ++ storeW xs) B) R) R L) := by
  set src := pre ++ storeRec xs ++ rest with hsrc
  let pos : ℕ → ℕ := fun j => pre.length + ((xs.take j).flatMap fun x => true :: x.block).length
  let outj : ℕ → List Bool := fun j => out ++ (xs.take j).flatMap fun x => Rec.polyWord x.poly
  have hW := Block.WhileBody.run ({
    body := storeBody F
    tape := Scrub.inner (srcO F.t)
    bound := xs.length
    H := fun j => Scrub.heads (fH F.t (pos j) (outj j).length)
    A := fun j => Scrub.bank (restA F.t src (overlay (outj j) B) R) R L
    cost := storePass xs R
    step := by
      intro j hj
      have s1 := skipSrc_step F.t (pos j) (outj j).length (Scrub.bank (restA F.t src (overlay (outj j) B) R) R L)
      have hsp : src = (pre ++ ((xs.take j).flatMap (fun x => true :: x.block) ++ [true])) ++ xs[j].block ++
          ((xs.drop (j + 1)).flatMap (fun x => true :: x.block) ++ [false] ++ rest) := by
        rw [hsrc, storeRec_split xs j hj]; simp [List.append_assoc]
      have s2 := sfactor_step F xs[j] (pre ++ ((xs.take j).flatMap (fun x => true :: x.block) ++ [true]))
        ((xs.drop (j + 1)).flatMap (fun x => true :: x.block) ++ [false] ++ rest) (outj j) B R L
        (hR _ (List.getElem_mem hj)) hL
      rw [← hsp] at s2
      have e1 : (pre ++ ((xs.take j).flatMap (fun x => true :: x.block) ++ [true])).length = pos j + 1 := by
        simp [pos]; omega
      rw [e1] at s2
      have t := s1.seq s2
      have e2 : pos j + 1 + xs[j].block.length = pos (j + 1) := by
        simp only [pos, flatMap_take_succ' _ xs j hj, List.length_append, List.length_cons]; omega
      have e3 : outj j ++ Rec.polyWord xs[j].poly = outj (j + 1) := by
        simp only [outj, flatMap_take_succ' _ xs j hj, List.append_assoc]
      rw [e2, e3] at t
      refine t.enlarge (le_of_eq ?_)
      simp [storePass, List.getElem?_eq_getElem hj]
    cont := by
      intro j hj
      simp only [Scrub.bank_inner, restA, if_true, Scrub.heads_inner, fH_srcO]
      have e : src = (pre ++ (xs.take j).flatMap (fun x => true :: x.block)) ++ true ::
          (xs[j].block ++ ((xs.drop (j + 1)).flatMap (fun x => true :: x.block) ++ [false]) ++ rest) := by
        rw [hsrc, storeRec_split xs j hj]; simp [List.append_assoc]
      rw [e]
      have := Streaming.read_append (pre ++ (xs.take j).flatMap (fun x => true :: x.block))
        (xs[j].block ++ ((xs.drop (j + 1)).flatMap (fun x => true :: x.block) ++ [false]) ++ rest) true
      rwa [List.length_append] at this
    halt := by
      simp only [Scrub.bank_inner, restA, if_true, Scrub.heads_inner, fH_srcO, pos, List.take_length]
      have e : src = (pre ++ xs.flatMap (fun x => true :: x.block)) ++ false :: rest := by
        rw [hsrc, storeRec]; simp [List.append_assoc]
      rw [e]
      have := Streaming.read_append (pre ++ xs.flatMap (fun x => true :: x.block)) rest false
      rwa [List.length_append] at this } : Block.WhileBody _ _)
  have hW' : Step (storeM F) (((List.range (xs.length - 0)).map fun i => storePass xs R (0 + i) + 2).sum + 1)
      (Scrub.heads (fH F.t (pos 0) (outj 0).length)) (Scrub.bank (restA F.t src (overlay (outj 0) B) R) R L)
      (Scrub.heads (fH F.t (pos xs.length) (outj xs.length).length))
      (Scrub.bank (restA F.t src (overlay (outj xs.length) B) R) R L) := hW
  simp only [Nat.sub_zero, Nat.zero_add, pos, outj, List.take_zero, List.flatMap_nil, List.length_nil,
    Nat.add_zero, List.append_nil, List.take_length] at hW'
  exact hW'

end NearCubicWires.WireExponent3_5.ListMachine.Row
