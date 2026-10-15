import Proof.Packets.PacketsGlueMetaChild

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.Touch
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.NatSum

def nw : Fin 4 → Option Bool := fun _ => none

/-- States: `0..3` scan with flag false, `4..7` with flag true, `8` write, `9` start rewind, `10` rewind,
`11` halt. -/
def machine : Machine 4 12 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 11
  rule := fun q b =>
    if q.val = 0 then some (if b 0 then ⟨1, nw, ![.right, .stay, .stay, .stay]⟩ else ⟨11, nw, fun _ => .stay⟩)
    else if q.val = 4 then some (if b 0 then ⟨5, nw, ![.right, .stay, .stay, .stay]⟩ else ⟨11, nw, fun _ => .stay⟩)
    else if q.val = 1 then some (if b 0 then ⟨2, ![none, none, none, some true], ![.right, .stay, .right, .right]⟩
      else ⟨9, nw, ![.right, .stay, .stay, .stay]⟩)
    else if q.val = 5 then some (if b 0 then ⟨6, ![none, none, none, some true], ![.right, .stay, .right, .right]⟩
      else ⟨8, nw, ![.right, .stay, .stay, .stay]⟩)
    else if q.val = 2 then some ⟨3, nw, ![.right, .stay, .stay, .stay]⟩
    else if q.val = 6 then some ⟨7, nw, ![.right, .stay, .stay, .stay]⟩
    else if q.val = 3 then some (if b 0 && b 2 then ⟨4, ![none, none, none, some true], ![.right, .stay, .right, .right]⟩
      else ⟨0, ![none, none, none, some true], ![.right, .stay, .right, .right]⟩)
    else if q.val = 7 then some ⟨4, ![none, none, none, some true], ![.right, .stay, .right, .right]⟩
    else if q.val = 8 then some ⟨9, ![none, some true, none, none], ![.stay, .right, .stay, .stay]⟩
    else if q.val = 9 then some ⟨10, nw, ![.stay, .stay, .stay, .left]⟩
    else if q.val = 10 then some (if b 3 then ⟨10, ![none, none, none, some false], ![.stay, .stay, .left, .left]⟩
      else ⟨0, nw, fun _ => .stay⟩)
    else none

/-- Tapes: support, output `1^o` (head at its end), mask, counter. -/
def cfg (q : Fin 12) (S : List Bool) (sh o : ℕ) (M : List Bool) (mh : ℕ) (C : List Bool) (ch : ℕ) :
    Configuration 4 12 :=
  ⟨q, ![sh, o, mh, ch], ![S, List.replicate o true, M, C]⟩

/-- The scan states for a flag value. -/
def sA (f : Bool) (k : ℕ) (hk : k < 4) : Fin 12 := ⟨(if f then 4 else 0) + k, by split_ifs <;> omega⟩

section Steps
variable (S : List Bool) (sh o : ℕ) (M : List Bool) (mh : ℕ) (C : List Bool) (ch : ℕ)

theorem a0t (f : Bool) (h : readTapeBit S sh = true) :
    step machine (cfg (sA f 0 (by omega)) S sh o M mh C ch) = some (cfg (sA f 1 (by omega)) S (sh+1) o M mh C ch) := by
  cases f <;> simp [step, machine, cfg, sA, Configuration.scanned, h] <;>
  (apply configuration_ext
   · rfl
   · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
   · funext i; fin_cases i <;> simp [applyAction, nw])

theorem a0f (h : readTapeBit S sh = false) :
    step machine (cfg (sA false 0 (by omega)) S sh o M mh C ch) = some (cfg 11 S sh o M mh C ch) := by
  simp [step, machine, cfg, sA, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem a1t (f : Bool) (h : readTapeBit S sh = true) :
    step machine (cfg (sA f 1 (by omega)) S sh o M mh C ch) =
      some (cfg (sA f 2 (by omega)) S (sh+1) o M (mh+1) (writeTapeBit C ch true) (ch+1)) := by
  cases f <;> simp [step, machine, cfg, sA, Configuration.scanned, h] <;>
  (apply configuration_ext
   · rfl
   · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
   · funext i; fin_cases i <;> simp [applyAction])

theorem a1f_false (h : readTapeBit S sh = false) :
    step machine (cfg (sA false 1 (by omega)) S sh o M mh C ch) = some (cfg 9 S (sh+1) o M mh C ch) := by
  simp [step, machine, cfg, sA, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem a1f_true (h : readTapeBit S sh = false) :
    step machine (cfg (sA true 1 (by omega)) S sh o M mh C ch) = some (cfg 8 S (sh+1) o M mh C ch) := by
  simp [step, machine, cfg, sA, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem a2 (f : Bool) :
    step machine (cfg (sA f 2 (by omega)) S sh o M mh C ch) = some (cfg (sA f 3 (by omega)) S (sh+1) o M mh C ch) := by
  cases f <;> simp [step, machine, cfg, sA] <;>
  (apply configuration_ext
   · rfl
   · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
   · funext i; fin_cases i <;> simp [applyAction, nw])

theorem a3 (f : Bool) :
    step machine (cfg (sA f 3 (by omega)) S sh o M mh C ch) =
      some (cfg (sA (f || (readTapeBit S sh && readTapeBit M mh)) 0 (by omega)) S (sh+1) o M (mh+1)
        (writeTapeBit C ch true) (ch+1)) := by
  cases f
  · cases hs : readTapeBit S sh <;> cases hm : readTapeBit M mh <;>
      simp [step, machine, cfg, sA, Configuration.scanned, hs, hm] <;>
      (apply configuration_ext
       · rfl
       · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
       · funext i; fin_cases i <;> simp [applyAction])
  · simp [step, machine, cfg, sA]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction]

theorem e8 : step machine (cfg 8 S sh o M mh C ch) = some (cfg 9 S sh (o+1) M mh C ch) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem r9 : step machine (cfg 9 S sh o M mh C ch) = some (cfg 10 S sh o M mh C (ch-1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem r10t (h : readTapeBit C ch = true) :
    step machine (cfg 10 S sh o M mh C ch) = some (cfg 10 S sh o M (mh-1) (writeTapeBit C ch false) (ch-1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem r10f (h : readTapeBit C ch = false) :
    step machine (cfg 10 S sh o M mh C ch) = some (cfg (sA false 0 (by omega)) S sh o M mh C ch) := by
  simp [step, machine, cfg, sA, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

end Steps

/-! ## Loops -/

def touchedB : List Bool → List Bool → Bool
  | [], _ => false
  | _ :: _, [] => false
  | b :: bs, m :: ms => (b && m) || touchedB bs ms

theorem timed_congr {n n' : ℕ} {c c' d d' : Configuration 4 12} (h : Timed machine n c d)
    (hn : n = n') (hc : c = c') (hd : d = d') : Timed machine n' c' d' := by
  subst hn hc hd
  exact h

theorem tr {n m : ℕ} {c d d' e : Configuration 4 12} (h1 : Timed machine n c d) (h2 : Timed machine m d' e)
    (h : d = d') : Timed machine (n + m) c e := by
  subst h
  exact h1.trans h2

macro "tcfg_eq" : tactic => `(tactic| (congr 1 <;> first | rfl | omega | (congr 1 <;> omega)))

theorem dbl_dbl_cons (b : Bool) (x : List Bool) :
    dbl (dbl (b :: x)) = [true, true, true, b] ++ dbl (dbl x) := by
  simp [dbl]

theorem read4 (P R : List Bool) (b : Bool) (x : List Bool) (j : ℕ) (hj : j < 4) :
    readTapeBit (P ++ dbl (dbl (b :: x)) ++ R) (P.length + j) = ([true, true, true, b] : List Bool).getD j false := by
  rw [dbl_dbl_cons, List.append_assoc, List.append_assoc, read_suffix,
    read_prefix _ _ j (by simp; omega)]
  rfl

theorem bits_loop (mask : List Bool) (o : ℕ) : ∀ (bs : List Bool) (P R : List Bool) (f : Bool) (i c kc : ℕ),
    i + bs.length ≤ mask.length →
    Timed machine (4 * bs.length)
      (cfg (sA f 0 (by omega)) (P ++ dbl (dbl bs) ++ R) P.length o (frame mask) (2 * i) (marks (2 * c) kc) (2 * c))
      (cfg (sA (f || touchedB bs (mask.drop i)) 0 (by omega)) (P ++ dbl (dbl bs) ++ R) (P.length + 4 * bs.length) o
        (frame mask) (2 * (i + bs.length)) (marks (2 * c + 2 * bs.length) (kc - 2 * bs.length))
        (2 * c + 2 * bs.length)) := by
  intro bs
  induction bs with
  | nil =>
    intro P R f i c kc _
    have e : (f || touchedB [] (mask.drop i)) = f := by simp [touchedB]
    rw [e]
    simpa using Timed.refl machine
      (cfg (sA f 0 (by omega)) (P ++ dbl (dbl []) ++ R) P.length o (frame mask) (2 * i) (marks (2 * c) kc) (2 * c))
  | cons b bs ih =>
    intro P R f i c kc hlen
    simp only [List.length_cons] at hlen
    have hi : i < mask.length := by omega
    set S := P ++ dbl (dbl (b :: bs)) ++ R with hS
    have r0 : readTapeBit S (P.length + 0) = true := read4 P R b bs 0 (by omega)
    have r1 : readTapeBit S (P.length + 1) = true := read4 P R b bs 1 (by omega)
    have r3 : readTapeBit S (P.length + 3) = b := read4 P R b bs 3 (by omega)
    have rm : readTapeBit (frame mask) (2 * i + 1) = mask[i] := read_payload mask i hi
    simp only [Nat.add_zero] at r0
    have t1 := Timed.single (p := machine) (by cases f <;> rfl)
      (a0t S P.length o (frame mask) (2 * i) (marks (2 * c) kc) (2 * c) f r0)
    have t2 := Timed.single (p := machine) (by cases f <;> rfl)
      (a1t S (P.length + 1) o (frame mask) (2 * i) (marks (2 * c) kc) (2 * c) f r1)
    rw [marks_mark] at t2
    have t3 := Timed.single (p := machine) (by cases f <;> rfl)
      (a2 S (P.length + 1 + 1) o (frame mask) (2 * i + 1) (marks (2 * c + 1) (kc - 1)) (2 * c + 1) f)
    have t4 := Timed.single (p := machine) (by cases f <;> rfl)
      (a3 S (P.length + 1 + 1 + 1) o (frame mask) (2 * i + 1) (marks (2 * c + 1) (kc - 1)) (2 * c + 1) f)
    rw [show P.length + 1 + 1 + 1 = P.length + 3 by omega, r3, rm, marks_mark] at t4
    have hS' : S = (P ++ [true, true, true, b]) ++ dbl (dbl bs) ++ R := by
      rw [hS, dbl_dbl_cons]; simp [List.append_assoc]
    have t5 := ih (P ++ [true, true, true, b]) R (f || (b && mask[i])) (i + 1) (c + 1) (kc - 1 - 1) (by omega)
    rw [← hS'] at t5
    have e1 := tr t1 t2 (by tcfg_eq)
    have e2 := tr e1 t3 (by tcfg_eq)
    have e3 := tr e2 t4 (by tcfg_eq)
    have e4 := tr e3 t5 (by simp only [List.length_append, List.length_cons, List.length_nil]; tcfg_eq)
    have hdrop : mask.drop i = mask[i] :: mask.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hflag : (f || (b && mask[i]) || touchedB bs (mask.drop (i + 1))) =
        (f || touchedB (b :: bs) (mask.drop i)) := by
      rw [hdrop]; simp [touchedB, Bool.or_assoc]
    rw [hflag] at e4
    refine timed_congr e4 (by first | omega | (simp; done) | (simp; omega)) rfl ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    tcfg_eq

theorem rewind (S : List Bool) (sh o : ℕ) (M : List Bool) :
    ∀ p m kc : ℕ, Timed machine (p + 1) (cfg 10 S sh o M (m + p) (marks p kc) (p - 1))
      (cfg (sA false 0 (by omega)) S sh o M m (marks 0 (kc + p)) 0) := by
  intro p
  induction p with
  | zero =>
    intro m kc
    have h : readTapeBit (marks 0 kc) (0 - 1) = false := by rw [read_marks]; simp
    simpa using Timed.single (p := machine) (by rfl) (r10f S sh o M (m + 0) (marks 0 kc) (0 - 1) h)
  | succ p ih =>
    intro m kc
    have h : readTapeBit (marks (p + 1) kc) (p + 1 - 1) = true := by rw [read_marks]; simp
    have t1 := Timed.single (p := machine) (by rfl)
      (r10t S sh o M (m + (p + 1)) (marks (p + 1) kc) (p + 1 - 1) h)
    rw [show p + 1 - 1 = p by omega, marks_erase, show m + (p + 1) - 1 = m + p by omega] at t1
    have t2 := ih m (kc + 1)
    have e := tr t1 t2 rfl
    exact timed_congr e (by omega) rfl (by tcfg_eq)

/-! ## One occurrence, all occurrences, the run -/

theorem dbl_frame (x : List Bool) : dbl (frame x) = dbl (dbl x) ++ [true, false] := by
  rw [frame_eq_dbl]; simp [dbl, List.flatMap_append]

/-- **One occurrence frame.** The output grows by one exactly when the frame's bits touch the mask. -/
theorem occurrence (mask : List Bool) (P R x : List Bool) (hx : x.length ≤ mask.length) (o kc : ℕ) :
    ∃ kc' : ℕ, Timed machine (4 * x.length + 2 + (if touchedB x mask then 1 else 0) + 1 + (2 * x.length + 1))
      (cfg (sA false 0 (by omega)) (P ++ dbl (frame x) ++ R) P.length o (frame mask) 0 (marks 0 kc) 0)
      (cfg (sA false 0 (by omega)) (P ++ dbl (frame x) ++ R) (P.length + (dbl (frame x)).length)
        (o + if touchedB x mask then 1 else 0) (frame mask) 0 (marks 0 kc') 0) := by
  set S := P ++ dbl (frame x) ++ R with hS
  have hS' : S = P ++ dbl (dbl x) ++ ([true, false] ++ R) := by rw [hS, dbl_frame]; simp [List.append_assoc]
  have t1 := bits_loop mask o x P ([true, false] ++ R) false 0 0 kc (by omega)
  rw [← hS'] at t1
  simp only [Bool.false_or, Nat.mul_zero, Nat.zero_add, List.drop_zero] at t1
  have hend0 : readTapeBit S (P.length + 4 * x.length) = true := by
    have h := read_suffix (P ++ dbl (dbl x)) ([true, false] ++ R) 0
    rw [Nat.add_zero, show (P ++ dbl (dbl x)).length = P.length + 4 * x.length by simp; omega] at h
    rw [hS', h]; rfl
  have hend1 : readTapeBit S (P.length + 4 * x.length + 1) = false := by
    have h := read_suffix (P ++ dbl (dbl x)) ([true, false] ++ R) 1
    rw [show (P ++ dbl (dbl x)).length = P.length + 4 * x.length by simp; omega] at h
    rw [hS', h]; rfl
  have t2 := Timed.single (p := machine) (by cases touchedB x mask <;> rfl)
    (a0t S (P.length + 4 * x.length) o (frame mask) (2 * x.length) (marks (2 * x.length) (kc - 2 * x.length))
      (2 * x.length) (touchedB x mask) hend0)
  have hlen : (dbl (frame x)).length = 4 * x.length + 2 := by simp; omega
  have hr := rewind S (P.length + 4 * x.length + 1 + 1) (o + if touchedB x mask then 1 else 0) (frame mask)
    (2 * x.length) 0 (kc - 2 * x.length)
  simp only [Nat.zero_add] at hr
  cases ht : touchedB x mask
  · have t3 := Timed.single (p := machine) (by rfl)
      (a1f_false S (P.length + 4 * x.length + 1) o (frame mask) (2 * x.length)
        (marks (2 * x.length) (kc - 2 * x.length)) (2 * x.length) hend1)
    have t4 := Timed.single (p := machine) (by rfl)
      (r9 S (P.length + 4 * x.length + 1 + 1) o (frame mask) (2 * x.length)
        (marks (2 * x.length) (kc - 2 * x.length)) (2 * x.length))
    rw [ht] at t1 t2
    simp only [ht, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hr
    have e1 := tr t1 t2 (by tcfg_eq)
    have e2 := tr e1 t3 (by tcfg_eq)
    have e3 := tr e2 t4 (by tcfg_eq)
    have e4 := tr e3 hr (by tcfg_eq)
    refine ⟨kc - 2 * x.length + 2 * x.length, timed_congr e4 (by first | omega | (simp; done) | (simp; omega)) rfl (by tcfg_eq)⟩
  · have t3 := Timed.single (p := machine) (by rfl)
      (a1f_true S (P.length + 4 * x.length + 1) o (frame mask) (2 * x.length)
        (marks (2 * x.length) (kc - 2 * x.length)) (2 * x.length) hend1)
    have t4 := Timed.single (p := machine) (by rfl)
      (e8 S (P.length + 4 * x.length + 1 + 1) o (frame mask) (2 * x.length)
        (marks (2 * x.length) (kc - 2 * x.length)) (2 * x.length))
    have t5 := Timed.single (p := machine) (by rfl)
      (r9 S (P.length + 4 * x.length + 1 + 1) (o + 1) (frame mask) (2 * x.length)
        (marks (2 * x.length) (kc - 2 * x.length)) (2 * x.length))
    rw [ht] at t1 t2
    simp only [ht, ↓reduceIte] at hr
    have e1 := tr t1 t2 (by tcfg_eq)
    have e2 := tr e1 t3 (by tcfg_eq)
    have e3 := tr e2 t4 (by tcfg_eq)
    have e4 := tr e3 t5 (by tcfg_eq)
    have e5 := tr e4 hr (by tcfg_eq)
    refine ⟨kc - 2 * x.length + 2 * x.length, timed_congr e5 (by first | omega | (simp; done) | (simp; omega)) rfl (by tcfg_eq)⟩

/-- The count of touched frames. -/
def touchCount (mask : List Bool) (xs : List (List Bool)) : ℕ :=
  (xs.map (fun x => if touchedB x mask then 1 else 0)).sum

/-- **All occurrence frames.** -/
theorem occurrences (mask R : List Bool) : ∀ (xs : List (List Bool)) (P : List Bool) (o kc : ℕ),
    (∀ x ∈ xs, x.length ≤ mask.length) →
    ∃ T kc' : ℕ, Timed machine T
      (cfg (sA false 0 (by omega)) (P ++ dbl (CountFrames.frames xs) ++ R) P.length o (frame mask) 0 (marks 0 kc) 0)
      (cfg (sA false 0 (by omega)) (P ++ dbl (CountFrames.frames xs) ++ R)
        (P.length + (dbl (CountFrames.frames xs)).length) (o + touchCount mask xs) (frame mask) 0 (marks 0 kc') 0) ∧
      T ≤ 3 * (dbl (CountFrames.frames xs)).length := by
  intro xs
  induction xs with
  | nil =>
    intro P o kc _
    refine ⟨0, kc, ?_, by simp⟩
    simpa [CountFrames.frames, touchCount] using Timed.refl machine
      (cfg (sA false 0 (by omega)) (P ++ dbl (CountFrames.frames []) ++ R) P.length o (frame mask) 0 (marks 0 kc) 0)
  | cons x xs ih =>
    intro P o kc hx
    have hw : P ++ dbl (CountFrames.frames (x :: xs)) ++ R = P ++ dbl (frame x) ++ (dbl (CountFrames.frames xs) ++ R) := by
      rw [CountFrames.frames_cons, CountFrames.dbl_append]; simp [List.append_assoc]
    have hw2 : P ++ dbl (CountFrames.frames (x :: xs)) ++ R = (P ++ dbl (frame x)) ++ dbl (CountFrames.frames xs) ++ R := by
      rw [CountFrames.frames_cons, CountFrames.dbl_append]; simp [List.append_assoc]
    obtain ⟨kc1, t1⟩ := occurrence mask P (dbl (CountFrames.frames xs) ++ R) x (hx x (by simp)) o kc
    rw [← hw] at t1
    obtain ⟨T2, kc2, t2, h2⟩ := ih (P ++ dbl (frame x)) (o + if touchedB x mask then 1 else 0) kc1
      (fun y hy => hx y (by simp [hy]))
    rw [← hw2] at t2
    have e := tr t1 t2 (by first | rfl | (simp only [List.length_append]; done) | (simp only [List.length_append]; tcfg_eq))
    have hl : (dbl (CountFrames.frames (x :: xs))).length = (dbl (frame x)).length + (dbl (CountFrames.frames xs)).length := by
      rw [CountFrames.frames_cons, CountFrames.dbl_append, List.length_append]
    have hfx : (dbl (frame x)).length = 4 * x.length + 2 := by simp; omega
    refine ⟨_, kc2, timed_congr e rfl rfl ?_, ?_⟩
    · simp only [List.length_append, hl, touchCount, List.map_cons, List.sum_cons]
      tcfg_eq
    · rw [hl, hfx]
      split_ifs <;> omega

/-- **The count.** From the doubly framed support field on tape 0 and the mask frame on tape 2 (all else
empty, heads 0): tape 1 holds `replicate (touchCount mask xs) true`. -/
theorem run (mask : List Bool) (xs : List (List Bool)) (hx : ∀ x ∈ xs, x.length ≤ mask.length) :
    ∃ (n : ℕ) (H1 : Fin 4 → ℕ) (A1 : Fin 4 → List Bool),
      Step machine n (fun _ => 0) ![frame (CountFrames.frames xs), [], frame mask, []] H1 A1 ∧
      A1 1 = List.replicate (touchCount mask xs) true ∧ n ≤ 3 * (frame (CountFrames.frames xs)).length + 1 := by
  obtain ⟨T, kc, t1, hT⟩ := occurrences mask [false] xs [] 0 0 hx
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at t1
  have hf : frame (CountFrames.frames xs) = dbl (CountFrames.frames xs) ++ [false] := frame_eq_dbl _
  rw [← hf] at t1
  have hend : readTapeBit (frame (CountFrames.frames xs)) (dbl (CountFrames.frames xs)).length = false := by
    have h := read_suffix (dbl (CountFrames.frames xs)) [false] 0
    rw [Nat.add_zero] at h
    rw [hf, h]; rfl
  have t2 := Timed.single (p := machine) (by rfl)
    (a0f (frame (CountFrames.frames xs)) (dbl (CountFrames.frames xs)).length (touchCount mask xs) (frame mask) 0
      (marks 0 kc) 0 hend)
  have e := t1.trans t2
  obtain ⟨r, hr, hfin, hs⟩ := e.run rfl
  have hc : (⟨machine.start, fun _ => 0, ![frame (CountFrames.frames xs), [], frame mask, []]⟩ :
      Configuration 4 12) = cfg (sA false 0 (by omega)) (frame (CountFrames.frames xs)) 0 0 (frame mask) 0 (marks 0 0) 0 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [← hc] at hr
  refine ⟨_, r.final.heads, r.final.tapes, ⟨r, hr, rfl, rfl, le_of_eq hs⟩, ?_, ?_⟩
  · rw [hfin]; simp [cfg]
  · rw [hf, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega

theorem touchedB_ofFn : ∀ (q : ℕ) (f g : Fin q → Bool),
    touchedB (List.ofFn f) (List.ofFn g) = decide (∃ i, f i = true ∧ g i = true) := by
  intro q
  induction q with
  | zero => intro f g; simp [touchedB]
  | succ q ih =>
    intro f g
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [touchedB, ih, Fin.exists_fin_succ]
    cases h1 : f 0 <;> cases h2 : g 0 <;> simp

end NearCubicWires.PacketsGlue.Touch

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.SupplierTouching
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent
noncomputable section

/-- `B` is the touched-frame count of the support field against the mask field. -/
theorem touch_eq (a : DecompositionAlgorithm) (r : Request) :
    touch a r = Touch.touchCount (fields a r 2)
      ((occ a r).map (fun g => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support)))) := by
  unfold touch LiveRows.bound touchingCost
  unfold Touch.touchCount
  rw [List.map_map]
  have e1 : ∀ g : SupplierPipeline.SupportedNormalizedGate r.q,
      touchIndicator (live a r) g.support =
      (fun x => if Touch.touchedB x (fields a r 2) then 1 else 0)
        (List.ofFn (fun i : Fin r.q => decide (i ∈ g.support))) := by
    intro g
    change _ = if Touch.touchedB _ (CyclicChoice.mask (r.family a).occurrences r.liveScale) then 1 else 0
    unfold CyclicChoice.mask
    rw [Touch.touchedB_ofFn]
    unfold touchIndicator
    by_cases hd : Disjoint (live a r) g.support
    · rw [if_pos hd, if_neg]
      simp only [decide_eq_true_eq, not_exists, not_and]
      intro i hi hl
      exact Finset.disjoint_left.mp hd (by simpa using hl) (by simpa using hi)
    · rw [if_neg hd, if_pos]
      rw [Finset.not_disjoint_iff] at hd
      obtain ⟨i, hl, hi⟩ := hd
      simp only [decide_eq_true_eq]
      exact ⟨i, by simpa using hi, by simpa using hl⟩
  have e2 : (List.map ((fun x => if Touch.touchedB x (fields a r 2) then 1 else 0) ∘
      fun g : SupplierPipeline.SupportedNormalizedGate r.q => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support)))
      (occ a r)) = (occ a r).map (fun g => touchIndicator (live a r) g.support) := by
    apply List.map_congr_left
    intro g _
    exact (e1 g).symm
  rw [e2, ← List.sum_ofFn]
  simp only [SupplierEstimator.occurrenceSupport]
  congr 1
  conv_rhs => rw [← List.ofFn_get (occ a r), List.map_ofFn]
  rfl

/-! ## Two fields -/

/-- The masked two-field scanner: tape 0 on field `j1`, 1 on the output, 2 on field `j2`, the rest past
the splitter. -/
def sc2 (e : ℕ) (j1 j2 : Fin 5) : Fin (3 + e + 1) → Fin (2 + (13 + e + 1)) :=
  fun k => if k.val = 0 then ⟨j1.val + 4, by omega⟩ else if k.val = 1 then ⟨1, by omega⟩
    else if k.val = 2 then ⟨j2.val + 4, by omega⟩ else ⟨k.val + 12, by omega⟩

theorem sc2_val (e : ℕ) (j1 j2 : Fin 5) (k : Fin (3 + e + 1)) :
    (sc2 e j1 j2 k).val = if k.val = 0 then j1.val + 4 else if k.val = 1 then 1
      else if k.val = 2 then j2.val + 4 else k.val + 12 := by
  unfold sc2; split_ifs <;> rfl

theorem rfE_val (e : ℕ) (i : Fin 13) : (rfE e i).val = if i.val = 0 then 0 else i.val + 1 := by
  unfold rfE; split_ifs <;> rfl

theorem sc2_injective (e : ℕ) (j1 j2 : Fin 5) (hj : j1 ≠ j2) : Function.Injective (sc2 e j1 j2) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [sc2_val, sc2_val] at hv
  have hj' : j1.val ≠ j2.val := fun h' => hj (Fin.ext h')
  apply Fin.ext
  split_ifs at hv <;> omega

theorem sc2_val_ne_zero (e : ℕ) (j1 j2 : Fin 5) (k : Fin (3 + e + 1)) : (sc2 e j1 j2 k).val ≠ 0 := by
  rw [sc2_val]; split_ifs <;> omega

theorem rfE_ne_sc2 (e : ℕ) (j1 j2 : Fin 5) (k : Fin (3 + e + 1)) (hk : k.val = 1 ∨ 3 ≤ k.val)
    (i : Fin 13) : rfE e i ≠ sc2 e j1 j2 k := by
  intro h
  have hv := congrArg Fin.val h
  rw [rfE_val, sc2_val] at hv
  have := i.isLt
  split_ifs at hv <;> omega

theorem sc2_rf (e : ℕ) (j1 j2 : Fin 5) (k : Fin (3 + e + 1)) (j : Fin 5) (hk : (sc2 e j1 j2 k).val = j.val + 4) :
    sc2 e j1 j2 k = rfE e ⟨j.val + 3, by omega⟩ := by
  apply Fin.ext; rw [hk, rfE_val]; simp

/-- The two-field scanner entry. -/
def scanIn2 (e : ℕ) (f1 f2 : List Bool) : Fin (3 + e) → List Bool :=
  fun k => if k.val = 0 then f1 else if k.val = 2 then f2 else []

def fieldMachine2 {e s : ℕ} (M : Machine (3 + e) s) (j1 j2 : Fin 5) :=
  Composition.machine (RecoveryFocus.machine (rfE e) RequestInputFields.machine)
    (RecoveryFocus.machine (sc2 e j1 j2) (MaskedReset.machine M (fun _ => true)))

theorem field_run2 {e s : ℕ} (M : Machine (3 + e) s) (j1 j2 : Fin 5) (hj : j1 ≠ j2)
    (a : DecompositionAlgorithm) (r : Request)
    (v n : ℕ) (H1 : Fin (3 + e) → ℕ) (A1 : Fin (3 + e) → List Bool)
    (hM : Step M n (fun _ => 0) (scanIn2 e (frame (fields a r j1)) (frame (fields a r j2))) H1 A1)
    (hv : A1 ⟨1, by omega⟩ = List.replicate v true) :
    ∃ (H' : Fin (2 + (13 + e + 1)) → ℕ) (A' : Fin (2 + (13 + e + 1)) → List Bool),
      Step (fieldMachine2 M j1 j2) (6*(r.input a).length+17 + 1 + (2*n+2)) (fun _ => 0)
        (inBank (2 + (13 + e + 1)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = List.replicate v true ∧ H' ⟨1, by omega⟩ = 0 := by
  have hA := RequestInputFields.request_run a r
  have d1 := hA.dock (rfE e) (rfE_injective e) (fun _ => 0) (inBank (2 + (13 + e + 1)) (Request.input a r))
    (fun _ => rfl)
    (by
      intro i
      by_cases h : i = 0
      · subst h
        rfl
      · have hv : (rfE e i).val ≠ 0 := by
          rw [rfE_val, if_neg (show ¬ (i.val = 0) by intro h'; exact h (Fin.ext h'))]
          omega
        simp only [inBank, hv, if_false, h])
  obtain ⟨k, hm⟩ := step_mask0 hM (fun _ => true) (by intro i _; rfl)
  set ws := RequestInputFields.values a r with hws
  set H1' := dockH (rfE e) (fun _ => 0) (RequestInputFields.heads ws 5) with hH1'
  set A1' := install (rfE e) (inBank (2 + (13 + e + 1)) (Request.input a r))
    (RequestInputFields.bank ws 5) with hA1'
  have hHd : ∀ i : Fin (3 + e + 1), H1' (sc2 e j1 j2 i) =
      Fin.addCases (fun _ : Fin (3 + e) => 0) (fun _ : Fin 1 => 0) i := by
    intro i
    have hr : Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin (3 + e) => 0) (fun _ : Fin 1 => 0) i = 0 := by
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
    rw [hr, hH1']
    by_cases h0 : i.val = 0
    · rw [sc2_rf e j1 j2 i j1 (by rw [sc2_val, if_pos h0]), dockH_slot _ (rfE_injective e), heads_field]
    · by_cases h2 : i.val = 2
      · rw [sc2_rf e j1 j2 i j2 (by rw [sc2_val, if_neg h0, if_neg (by omega), if_pos h2]),
          dockH_slot _ (rfE_injective e), heads_field]
      · rw [dockH_other _ _ _ _ (fun i' => rfE_ne_sc2 e j1 j2 i (by omega) i')]
  have hAd : ∀ i : Fin (3 + e + 1), A1' (sc2 e j1 j2 i) =
      Fin.addCases (scanIn2 e (frame (fields a r j1)) (frame (fields a r j2))) (fun _ : Fin 1 => ([] : List Bool)) i := by
    intro i
    by_cases h0 : i.val = 0
    · have hc : i = Fin.castAdd 1 (⟨0, by omega⟩ : Fin (3 + e)) := Fin.ext (by simp [h0])
      rw [sc2_rf e j1 j2 i j1 (by rw [sc2_val, if_pos h0]), hA1', install_slot _ (rfE_injective e), bank_field,
        hc, Fin.addCases_left]
      simp [scanIn2, hws, fields]
    · by_cases h2 : i.val = 2
      · have hc : i = Fin.castAdd 1 (⟨2, by omega⟩ : Fin (3 + e)) := Fin.ext (by simp [h2])
        rw [sc2_rf e j1 j2 i j2 (by rw [sc2_val, if_neg h0, if_neg (by omega), if_pos h2]), hA1',
          install_slot _ (rfE_injective e), bank_field, hc, Fin.addCases_left]
        simp [scanIn2, hws, fields]
      · rw [hA1', install_other _ _ _ _ (fun i' => rfE_ne_sc2 e j1 j2 i (by omega) i'), inBank,
          if_neg (sc2_val_ne_zero e j1 j2 i)]
        revert h0 h2
        refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
        · intro h0 h2
          rw [Fin.addCases_left]
          simp only [Fin.val_castAdd] at h0 h2
          simp [scanIn2, h0, h2]
        · intro _ _
          rw [Fin.addCases_right]
  have d2 := hm.dock (sc2 e j1 j2) (sc2_injective e j1 j2 hj) H1' A1' hHd hAd
  have hall := d1.seq d2
  have h0 : (⟨0, by omega⟩ : Fin (2 + (13 + e + 1))) = rfE e 0 := rfl
  have h1 : (⟨1, by omega⟩ : Fin (2 + (13 + e + 1))) = sc2 e j1 j2 ⟨1, by omega⟩ := by
    apply Fin.ext; rw [sc2_val]; simp
  have hne0 : ∀ k, sc2 e j1 j2 k ≠ rfE e 0 := by
    intro k h; exact sc2_val_ne_zero e j1 j2 k (by rw [h]; rfl)
  refine ⟨_, _, hall, ?_, ?_, ?_, ?_⟩
  · rw [h0, install_other _ _ _ _ hne0, hA1', install_slot _ (rfE_injective e)]
    change RepairOrdinary.frame (RequestInputFields.word ws) = _
    rw [hws, RequestInputFields.word_values]
  · rw [h0, dockH_other _ _ _ _ hne0, hH1', dockH_slot _ (rfE_injective e)]
    rfl
  · rw [h1, install_slot _ (sc2_injective e j1 j2 hj)]
    have hc : (⟨1, by omega⟩ : Fin (3 + e + 1)) = Fin.castAdd 1 (⟨1, by omega⟩ : Fin (3 + e)) := rfl
    rw [hc, Fin.addCases_left, hv]
  · rw [h1, dockH_slot _ (sc2_injective e j1 j2 hj)]
    have hc : (⟨1, by omega⟩ : Fin (3 + e + 1)) = Fin.castAdd 1 (⟨1, by omega⟩ : Fin (3 + e)) := rfl
    rw [hc, Fin.addCases_left]
    rfl

/-- **`touch` (B) stage.** -/
def touchStage (a : DecompositionAlgorithm) : UnaryStage a (touch a) where
  extra := 13 + 1 + 1
  states := _
  machine := fieldMachine2 Touch.machine 1 2
  cost := fun r => 6*(r.input a).length+17 + 1 + (2*(3 * (frame (fields a r 1)).length + 1) + 2)
  coefficient := 40
  degree := 1
  cost_le := by
    intro r
    have h1 := field_le_input a r 1
    have h2 := input_le_small a r
    rw [pow_one]
    omega
  run := by
    intro r
    set xs := (occ a r).map (fun g => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support))) with hxs
    have hlen : ∀ x ∈ xs, x.length ≤ (fields a r 2).length := by
      intro x hx
      rw [hxs, List.mem_map] at hx
      obtain ⟨g, _, rfl⟩ := hx
      change _ ≤ (CyclicChoice.mask (r.family a).occurrences r.liveScale).length
      simp [CyclicChoice.mask]
    obtain ⟨n, H1, A1, hs, hv, hn⟩ := Touch.run (fields a r 2) xs hlen
    have hsup : fields a r 1 = CountFrames.frames xs := support_frames a r
    have hs' : Step Touch.machine n (fun _ => 0) (scanIn2 1 (frame (fields a r 1)) (frame (fields a r 2))) H1 A1 := by
      have e : scanIn2 1 (frame (fields a r 1)) (frame (fields a r 2)) =
          ![frame (CountFrames.frames xs), [], frame (fields a r 2), []] := by
        funext k; fin_cases k <;> simp [scanIn2, hsup]
      rw [e]; exact hs
    obtain ⟨H', A', hrun, h0, hh0, h1, hh1⟩ := field_run2 (e := 1) Touch.machine 1 2 (by decide) a r
      (Touch.touchCount (fields a r 2) xs) n H1 A1 hs' (by exact hv)
    rw [← touch_eq] at h1
    have hn' : n ≤ 3 * (frame (fields a r 1)).length + 1 := by rw [hsup]; exact hn
    exact ⟨H', A', hrun.enlarge (by omega), h0, hh0, h1, hh1⟩

end
end NearCubicWires.PacketsGlue.RequestMeta

