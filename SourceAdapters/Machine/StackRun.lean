import SourceAdapters.Machine.StackMachine

/-!
# Runs of the stack machine, phase by phase

`app:short-pcp-proof`, "The exact Lean interface". Exact step counts for each phase of `prog` (`StackMachine`): the framing front end, one simulated
ordinary step, the output transfer and the cleanup.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Machine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary Turing TM2.Stmt

/-- `b` is reached from `a` in exactly `n` applications of `f` (Mathlib's `EvalsTo` as a proposition). -/
def Reach {α : Type} (f : α → Option α) (a : α) (b : Option α) (n : ℕ) : Prop :=
  (flip bind f)^[n] (some a) = b

theorem Reach.zero {α : Type} (f : α → Option α) (a : α) : Reach f a (some a) 0 := rfl

theorem Reach.single {α : Type} {f : α → Option α} {a : α} {b : Option α} (h : f a = b) : Reach f a b 1 := by
  simp [Reach, flip, h]

theorem Reach.trans {α : Type} {f : α → Option α} {a b : α} {c : Option α} {m n : ℕ}
    (h1 : Reach f a (some b) m) (h2 : Reach f b c n) : Reach f a c (m + n) := by
  unfold Reach at *
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

theorem Reach.cast {α : Type} {f : α → Option α} {a : α} {b : Option α} {m n : ℕ}
    (h : Reach f a b m) (hmn : m = n) : Reach f a b n := hmn ▸ h

section Runs

variable {T Q : ℕ} (M : LocalBitMultitape.Machine T Q) (t0 o : Fin T)

/-- The configuration type. -/
abbrev SCfg (T Q : ℕ) := TM2.Cfg (Sym (T := T)) (Label Q) (Var T)

/-- The step function of the program. -/
abbrev sstep : SCfg T Q → Option (SCfg T Q) := TM2.step (prog M t0 o)

/-! ## Framing front end -/

theorem frameRev_run : ∀ (w : List Bool) (v : Var T) (out : List Bool)
    (tp : Fin T → List (Option Bool) × List (Option Bool)) (A : List (Option Bool)), tp t0 = (A, []) →
    ∃ v' : Var T, Reach (sstep M t0 o) ⟨some .frameRev, v, stackOf w out tp⟩
      (some ⟨some .frameEmit, v',
        stackOf [] out (Function.update tp t0 ((w.map some).reverse ++ A, [some false]))⟩) (w.length + 1)
  | [], v, out, tp, A, htp => by
    refine ⟨{ v with cell := none }, Reach.single ?_⟩
    simp [prog, frameRevStmt, htp]
  | b :: w, v, out, tp, A, htp => by
    obtain ⟨v', h⟩ := frameRev_run w { v with cell := some (some b) } out
      (Function.update tp t0 (some b :: A, [])) (some b :: A) (by simp)
    refine ⟨v', Reach.cast (Reach.trans (b := ⟨some .frameRev, { v with cell := some (some b) },
      stackOf w out (Function.update tp t0 (some b :: A, []))⟩) (Reach.single ?_) ?_)
      (show 1 + (w.length + 1) = (b :: w).length + 1 by simp; omega)⟩
    · simp [prog, frameRevStmt, htp]
    · simpa using h

/-- The framed cells emitted in front of `R`. -/
def frameCells : List Bool → List (Option Bool) → List (Option Bool)
  | [], R => R
  | b :: w, R => some true :: some b :: frameCells w R

theorem frameCells_append (u v : List Bool) (R : List (Option Bool)) :
    frameCells (u ++ v) R = frameCells u (frameCells v R) := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [frameCells, ih]

theorem frameCells_false (w : List Bool) : frameCells w [some false] = (frame w).map some := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frameCells, frame, ih]

theorem frameEmit_run : ∀ (l : List Bool) (v : Var T) (i out : List Bool)
    (tp : Fin T → List (Option Bool) × List (Option Bool)) (R : List (Option Bool)), tp t0 = (l.map some, R) →
    ∃ v' : Var T, Reach (sstep M t0 o) ⟨some .frameEmit, v, stackOf i out tp⟩
      (some ⟨some (.sim M.start), v', stackOf i out (Function.update tp t0 ([], frameCells l.reverse R))⟩)
      (l.length + 1)
  | [], v, i, out, tp, R, htp => by
    refine ⟨{ v with cell := none }, Reach.single ?_⟩
    have : Function.update tp t0 ([], R) = tp := by rw [Function.update_eq_self_iff, htp]; rfl
    simp [prog, frameEmitStmt, htp, frameCells, this]
  | b :: l, v, i, out, tp, R, htp => by
    obtain ⟨v', h⟩ := frameEmit_run l { v with cell := some (some b) } i out
      (Function.update tp t0 (l.map some, some true :: some b :: R)) (some true :: some b :: R) (by simp)
    refine ⟨v', Reach.cast (Reach.trans (b := ⟨some .frameEmit, { v with cell := some (some b) },
      stackOf i out (Function.update tp t0 (l.map some, some true :: some b :: R))⟩) (Reach.single ?_) ?_)
      (show 1 + (l.length + 1) = (b :: l).length + 1 by simp; omega)⟩
    · simp [prog, frameEmitStmt, htp]
    · simpa [frameCells_append, frameCells] using h

/-! ## One simulated ordinary step -/

theorem topCell_head (R : List (Option Bool)) : topCell R.head? = topBit R := by
  cases R <;> rfl

theorem readAll_spec (st : SStmt T Q) : ∀ (l : List (Fin T)) (v : Var T) (i out : List Bool)
    (tp : Fin T → List (Option Bool) × List (Option Bool)),
    TM2.stepAux (l.foldr readOne st) v (stackOf i out tp) =
      TM2.stepAux st { v with scan := fun j => if j ∈ l then topBit (tp j).2 else v.scan j } (stackOf i out tp)
  | [], v, i, out, tp => by simp
  | j :: l, v, i, out, tp => by
    simp only [List.foldr_cons, readOne, TM2.stepAux, stackOf_rgt]
    rw [readAll_spec st l]
    congr 2
    funext j'
    by_cases h1 : j' ∈ l
    · simp [h1]
    · by_cases h2 : j' = j
      · subst h2; simp [h1, topCell_head]
      · simp [h1, h2]

theorem tapeOp_spec (q : Fin Q) (a : Action T Q) (j : Fin T) (st : SStmt T Q) (v : Var T)
    (hv : M.rule q v.scan = some a) (i out : List Bool) (tp : Fin T → List (Option Bool) × List (Option Bool)) :
    ∃ v' : Var T, v'.scan = v.scan ∧ TM2.stepAux (tapeOp M q j st) v (stackOf i out tp) =
      TM2.stepAux st v' (stackOf i out (Function.update tp j (tapeUpdate (a.write j) (a.move j) (tp j)))) := by
  have hw : ∀ s : Var T, s.scan = v.scan → wr M q s j = a.write j := by
    intro s hs; simp [wr, hs, hv]
  have hm : ∀ s : Var T, s.scan = v.scan → mv M q s j = a.move j := by
    intro s hs; simp [mv, hs, hv]
  rcases htp : tp j with ⟨L, R⟩
  rcases hW : a.write j with _ | b <;> rcases hM : a.move j with _ | _ | _ <;>
    rcases L with _ | ⟨x, L⟩ <;> rcases R with _ | ⟨y, R⟩ <;>
    simp [tapeOp, moveOp, hw, hm, hW, hM, htp, tapeUpdate, moveCells, writeCells] <;>
    first
      | (refine ⟨_, ?_, rfl⟩; rfl)
      | (rw [← htp, Function.update_eq_self]; refine ⟨_, ?_, rfl⟩; rfl)

theorem tapes_spec (q : Fin Q) (a : Action T Q) (st : SStmt T Q) : ∀ (l : List (Fin T)), l.Nodup →
    ∀ (v : Var T), M.rule q v.scan = some a → ∀ (i out : List Bool)
    (tp : Fin T → List (Option Bool) × List (Option Bool)),
    ∃ v' : Var T, v'.scan = v.scan ∧ TM2.stepAux (l.foldr (tapeOp M q) st) v (stackOf i out tp) =
      TM2.stepAux st v' (stackOf i out
        (fun j => if j ∈ l then tapeUpdate (a.write j) (a.move j) (tp j) else tp j))
  | [], _, v, _, i, out, tp => ⟨v, rfl, by simp⟩
  | j :: l, hl, v, hv, i, out, tp => by
    obtain ⟨hj, hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨v1, hv1, h1⟩ := tapeOp_spec M q a j (l.foldr (tapeOp M q) st) v hv i out tp
    obtain ⟨v2, hv2, h2⟩ := tapes_spec q a st l hl' v1 (by rw [hv1]; exact hv) i out
      (Function.update tp j (tapeUpdate (a.write j) (a.move j) (tp j)))
    refine ⟨v2, hv2.trans hv1, ?_⟩
    rw [List.foldr_cons, h1, h2]
    congr 2
    funext j'
    by_cases h : j' = j
    · subst h; simp [hj]
    · simp [h]

/-- The scanned bits of a represented configuration. -/
theorem scanned_eq (c : Configuration T Q) (tp : Fin T → List (Option Bool) × List (Option Bool))
    (hrep : ∀ j, TapeRep (tp j) (c.tapes j) (c.heads j)) : c.scanned = fun j => topBit (tp j).2 := by
  funext j
  obtain ⟨hd, hl⟩ := hrep j
  simp only [Configuration.scanned, ← hd, ← hl]
  exact readTapeBit_decode _ _

theorem sim_step (q : Fin Q) (hq : M.halted q = false) (a : Action T Q) (v : Var T)
    (tp : Fin T → List (Option Bool) × List (Option Bool))
    (ha : M.rule q (fun j => topBit (tp j).2) = some a) :
    ∃ v' : Var T, sstep M t0 o ⟨some (.sim q), v, stackOf [] [] tp⟩ =
      some ⟨some (.sim a.nextControl), v', stackOf [] [] (fun j => tapeUpdate (a.write j) (a.move j) (tp j))⟩ := by
  set v1 : Var T := { v with scan := fun j => if j ∈ List.finRange T then topBit (tp j).2 else v.scan j }
  have hv1 : v1.scan = fun j => topBit (tp j).2 := by funext j; simp [v1]
  obtain ⟨v2, hv2, h2⟩ := tapes_spec M q a (goto fun s => .sim (nxt M q s)) (List.finRange T)
    (List.nodup_finRange T) v1 (by rw [hv1]; exact ha) [] [] tp
  refine ⟨v2, ?_⟩
  have hn : nxt M q v2 = a.nextControl := by simp [nxt, hv2, hv1, ha]
  simp only [sstep, TM2.step, prog, simStmt, hq, Bool.false_eq_true, if_false]
  rw [readAll_spec]
  simp only [TM2.stepAux]
  rw [show (M.rule q v1.scan).isSome = true by rw [hv1, ha]; rfl]
  simp only [cond_true]
  rw [h2]
  simp [hn]

theorem sim_run (fuel : ℕ) : ∀ (c : Configuration T Q) (r : ExecutionReceipt T Q),
    runFrom M fuel c = some r → ∀ (v : Var T) (tp : Fin T → List (Option Bool) × List (Option Bool)) (N : ℕ),
    (∀ j, TapeRep (tp j) (c.tapes j) (c.heads j)) → (∀ j, (tp j).1.length + (tp j).2.length ≤ N) →
    ∃ (v' : Var T) (tp' : Fin T → List (Option Bool) × List (Option Bool)),
      Reach (sstep M t0 o) ⟨some (.sim c.control), v, stackOf [] [] tp⟩
        (some ⟨some (.sim r.final.control), v', stackOf [] [] tp'⟩) r.steps ∧
      (∀ j, TapeRep (tp' j) (r.final.tapes j) (r.final.heads j)) ∧
      (∀ j, (tp' j).1.length + (tp' j).2.length ≤ N + 2 * r.steps) ∧
      M.halted r.final.control = true ∧ r.steps ≤ fuel := by
  induction fuel with
  | zero =>
    intro c r hr v tp N hrep hsz
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact ⟨v, tp, Reach.zero _ _, hrep, by simpa using hsz, by assumption, le_rfl⟩
    · contradiction
  | succ fuel ih =>
    intro c r hr v tp N hrep hsz
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact ⟨v, tp, Reach.zero _ _, hrep, by simpa using hsz, by assumption, Nat.zero_le _⟩
    · rename_i hh
      have hh' : M.halted c.control = false := by simpa using hh
      cases hs : step M c with
      | none => simp [hs] at hr
      | some c' =>
        cases ht : runFrom M fuel c' with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst hr
          have hsc := scanned_eq c tp hrep
          simp only [step] at hs
          rcases hra : M.rule c.control c.scanned with _ | a
          · simp [hra] at hs
          · simp only [hra, Option.map_some, Option.some.injEq] at hs
            subst hs
            rw [hsc] at hra
            obtain ⟨v1, h1⟩ := sim_step M t0 o c.control hh' a v tp hra
            have hrep1 : ∀ j, TapeRep (tapeUpdate (a.write j) (a.move j) (tp j))
                ((applyAction c a).tapes j) ((applyAction c a).heads j) := by
              intro j
              have := tapeRep_update (a.write j) (a.move j) (tp j) (c.tapes j) (c.heads j) (hrep j)
              simp only [applyAction]
              cases hw : a.write j <;> simpa [hw] using this
            have hsz1 : ∀ j, (tapeUpdate (a.write j) (a.move j) (tp j)).1.length +
                (tapeUpdate (a.write j) (a.move j) (tp j)).2.length ≤ N + 2 := by
              intro j
              have := tapeUpdate_size (a.write j) (a.move j) (tp j)
              have := hsz j
              omega
            obtain ⟨v', tp', hR, hrep', hsz', hhalt, hle⟩ := ih (applyAction c a) tail ht v1 _ (N + 2) hrep1 hsz1
            refine ⟨v', tp', Reach.cast (Reach.trans (Reach.single h1) hR) (by simp; omega), hrep', ?_, hhalt,
              by simp; omega⟩
            intro j
            have := hsz' j
            simp only
            omega

/-! ## Output transfer and cleanup -/

theorem halted_step (q : Fin Q) (hq : M.halted q = true) (v : Var T)
    (S : ∀ k : Stack T, List (Sym k)) :
    sstep M t0 o ⟨some (.sim q), v, S⟩ = some ⟨some .gather, v, S⟩ := by
  simp [sstep, prog, simStmt, hq]

theorem gather_run : ∀ (R L : List (Option Bool)) (v : Var T) (i out : List Bool)
    (tp : Fin T → List (Option Bool) × List (Option Bool)), tp o = (L, R) →
    ∃ v' : Var T, Reach (sstep M t0 o) ⟨some .gather, v, stackOf i out tp⟩
      (some ⟨some .emit, v', stackOf i out (Function.update tp o (R.reverse ++ L, []))⟩) (R.length + 1)
  | [], L, v, i, out, tp, htp => by
    refine ⟨{ v with cell := none }, Reach.single ?_⟩
    have : Function.update tp o (L, []) = tp := by rw [Function.update_eq_self_iff, htp]
    simp [prog, gatherStmt, htp, this]
  | x :: R, L, v, i, out, tp, htp => by
    obtain ⟨v', h⟩ := gather_run R (x :: L) { v with cell := some x } i out
      (Function.update tp o (x :: L, R)) (by simp)
    refine ⟨v', Reach.cast (Reach.trans (b := ⟨some .gather, { v with cell := some x },
      stackOf i out (Function.update tp o (x :: L, R))⟩) (Reach.single ?_) ?_)
      (show 1 + (R.length + 1) = (x :: R).length + 1 by simp; omega)⟩
    · simp [prog, gatherStmt, htp]
    · simpa using h

theorem emit_run : ∀ (A : List (Option Bool)) (v : Var T) (i D : List Bool)
    (tp : Fin T → List (Option Bool) × List (Option Bool)), tp o = (A, []) →
    ∃ v' : Var T, Reach (sstep M t0 o) ⟨some .emit, v, stackOf i D tp⟩
      (some ⟨some .wipe, v', stackOf i (A.foldl (fun d c => consCell c d) D) (Function.update tp o ([], []))⟩)
      (A.length + 1)
  | [], v, i, D, tp, htp => by
    refine ⟨{ v with cell := none, flag := D.head?.isSome }, Reach.single ?_⟩
    have : Function.update tp o ([], []) = tp := by rw [Function.update_eq_self_iff, htp]
    simp [prog, emitStmt, htp, this]
  | c :: A, v, i, D, tp, htp => by
    obtain ⟨v', h⟩ := emit_run A { v with cell := some c, flag := D.head?.isSome } i (consCell c D)
      (Function.update tp o (A, [])) (by simp)
    refine ⟨v', Reach.cast (Reach.trans (b := ⟨some .emit, { v with cell := some c, flag := D.head?.isSome },
      stackOf i (consCell c D) (Function.update tp o (A, []))⟩) (Reach.single ?_) ?_)
      (show 1 + (A.length + 1) = (c :: A).length + 1 by simp; omega)⟩
    · rcases c with _ | b <;> rcases D with _ | ⟨d, D⟩ <;> simp [prog, emitStmt, htp, consCell]
    · simpa using h

theorem wipe_fold (st : SStmt T Q) : ∀ (l : List (Fin T)), l.Nodup → ∀ (v : Var T) (i out : List Bool)
    (tp : Fin T → List (Option Bool) × List (Option Bool)),
    ∃ v' : Var T, (v'.flag = true ↔ (v.flag = true ∨ ∃ j ∈ l, (tp j).1 ≠ [] ∨ (tp j).2 ≠ [])) ∧
      TM2.stepAux (l.foldr wipeOne st) v (stackOf i out tp) =
        TM2.stepAux st v' (stackOf i out (fun j => if j ∈ l then ((tp j).1.tail, (tp j).2.tail) else tp j))
  | [], _, v, i, out, tp => ⟨v, by simp, by simp⟩
  | j :: l, hl, v, i, out, tp => by
    obtain ⟨hj, hl'⟩ := List.nodup_cons.mp hl
    set v1 : Var T := { v with flag := v.flag || (tp j).1.head?.isSome || (tp j).2.head?.isSome }
    obtain ⟨v2, hv2, h2⟩ := wipe_fold st l hl' v1 i out
      (Function.update tp j ((tp j).1.tail, (tp j).2.tail))
    refine ⟨v2, ?_, ?_⟩
    · rw [hv2]
      have hne : ∀ j' ∈ l, j' ≠ j := fun j' hj' he => hj (he ▸ hj')
      constructor
      · rintro (h | ⟨j', hj', h⟩)
        · simp only [v1, Bool.or_eq_true, Option.isSome_iff_ne_none, ne_eq, List.head?_eq_none_iff] at h
          rcases h with (h | h) | h
          · exact Or.inl h
          · exact Or.inr ⟨j, by simp, Or.inl h⟩
          · exact Or.inr ⟨j, by simp, Or.inr h⟩
        · exact Or.inr ⟨j', by simp [hj'], by simpa [hne j' hj'] using h⟩
      · rintro (h | ⟨j', hj', h⟩)
        · exact Or.inl (by simp [v1, h])
        · rcases List.mem_cons.mp hj' with rfl | hj'
          · left
            simp only [v1, Bool.or_eq_true, Option.isSome_iff_ne_none, ne_eq, List.head?_eq_none_iff]
            tauto
          · exact Or.inr ⟨j', hj', by simpa [hne j' hj'] using h⟩
    · simp only [List.foldr_cons, wipeOne, TM2.stepAux, stackOf_lft, stackOf_rgt, update_stackOf_lft,
        update_stackOf_rgt, Function.update_self, Function.update_idem]
      convert h2 using 3
      funext j'
      by_cases h : j' = j
      · subst h; simp [hj]
      · simp [h]

theorem wipe_step (v : Var T) (i out : List Bool) (tp : Fin T → List (Option Bool) × List (Option Bool)) :
    ∃ v2 : Var T, (v2.flag = true ↔ ∃ j, (tp j).1 ≠ [] ∨ (tp j).2 ≠ []) ∧
      sstep M t0 o ⟨some .wipe, v, stackOf i out tp⟩ =
        some (if v2.flag then ⟨some .wipe, v2, stackOf i out (fun j => ((tp j).1.tail, (tp j).2.tail))⟩
          else ⟨none, Var.init T, stackOf i out (fun j => ((tp j).1.tail, (tp j).2.tail))⟩) := by
  obtain ⟨v2, hv2, h2⟩ := wipe_fold (T := T) (Q := Q) (branch (fun s => s.flag) (goto fun _ => .wipe)
      (load (fun _ => Var.init T) halt)) (List.finRange T) (List.nodup_finRange T) { v with flag := false }
      i out tp
  refine ⟨v2, by simpa using hv2, ?_⟩
  simp only [sstep, TM2.step, prog, wipeStmt, TM2.stepAux]
  rw [h2]
  simp only [List.mem_finRange, if_true]
  cases hf : v2.flag <;> simp [hf]

theorem wipe_run (m : ℕ) : ∀ (v : Var T) (i out : List Bool) (tp : Fin T → List (Option Bool) × List (Option Bool)),
    (∀ j, (tp j).1.length ≤ m ∧ (tp j).2.length ≤ m) →
    ∃ n ≤ m + 1, Reach (sstep M t0 o) ⟨some .wipe, v, stackOf i out tp⟩
      (some ⟨none, Var.init T, stackOf i out (fun _ => ([], []))⟩) n := by
  induction m with
  | zero =>
    intro v i out tp hsz
    obtain ⟨v2, hv2, h2⟩ := wipe_step M t0 o v i out tp
    have hnil : ∀ j, (tp j).1 = [] ∧ (tp j).2 = [] := by
      intro j; have := hsz j; exact ⟨List.eq_nil_of_length_eq_zero (by omega),
        List.eq_nil_of_length_eq_zero (by omega)⟩
    have hf : v2.flag = false := by
      by_contra hc
      obtain ⟨j, hj⟩ := hv2.mp (by simpa using hc)
      rcases hj with h | h
      · exact h (hnil j).1
      · exact h (hnil j).2
    refine ⟨1, le_rfl, Reach.single ?_⟩
    rw [h2, hf]
    simp only [Bool.false_eq_true, if_false, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
    congr 1
    funext j
    simp [(hnil j).1, (hnil j).2]
  | succ m ih =>
    intro v i out tp hsz
    obtain ⟨v2, hv2, h2⟩ := wipe_step M t0 o v i out tp
    cases hf : v2.flag with
    | true =>
      obtain ⟨n, hn, hR⟩ := ih v2 i out (fun j => ((tp j).1.tail, (tp j).2.tail)) (by
        intro j; have := hsz j; simp only [List.length_tail]; omega)
      refine ⟨1 + n, by omega, Reach.trans (Reach.single ?_) hR⟩
      rw [h2, hf]; rfl
    | false =>
      have hnil : ∀ j, (tp j).1 = [] ∧ (tp j).2 = [] := by
        intro j
        by_contra hc
        have : v2.flag = true := hv2.mpr ⟨j, by tauto⟩
        rw [hf] at this; exact Bool.false_ne_true this
      refine ⟨1, by omega, Reach.single ?_⟩
      rw [h2, hf]
      simp only [Bool.false_eq_true, if_false, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      congr 1
      funext j
      simp [(hnil j).1, (hnil j).2]

end Runs

end NearCubicGates.Adapters.Machine
