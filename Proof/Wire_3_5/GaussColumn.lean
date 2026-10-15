import Proof.Wire_3_5.GaussPass

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Gauss
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.JoinElimination
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The rows tape -/

/-- The rows tape of a pass: the framed rows, the `false` terminator, then stale cells. -/
def rowsTape (reps : List (List Bool)) (stale : List Bool) : List Bool := reps.flatMap frame ++ false :: stale

theorem rowsTape_split (reps : List (List Bool)) (stale : List Bool) (j : ℕ) (hj : j < reps.length) :
    rowsTape reps stale =
      (reps.take j).flatMap frame ++ frame reps[j] ++ ((reps.drop (j + 1)).flatMap frame ++ false :: stale) := by
  have e : reps = reps.take j ++ reps[j] :: reps.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  calc rowsTape reps stale = rowsTape (reps.take j ++ reps[j] :: reps.drop (j + 1)) stale :=
        congrArg (fun r => rowsTape r stale) e
    _ = _ := by simp only [rowsTape, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem take_flatMap_succ (reps : List (List Bool)) (j : ℕ) (hj : j < reps.length) :
    ((reps.take (j + 1)).flatMap frame).length = ((reps.take j).flatMap frame).length + (2 * reps[j].length + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append, List.length_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, frame_length]

/-- Before a pivot is found the state has none; after, its pivot is a row's tail, of length `L`. -/
theorem prefixState_piv (reps : List (List Bool)) (L : ℕ) (hL : ∀ r ∈ reps, r.length = L + 1) (j : ℕ) :
    ∀ p, (prefixState reps j).1 = some p → p.length = L := by
  induction j with
  | zero => intro p hp; simp [prefixState] at hp
  | succ j ih =>
    intro p hp
    by_cases hj : j < reps.length
    · rw [prefixState_succ reps j hj] at hp
      have hlen := hL _ (List.getElem_mem hj)
      cases hs : (prefixState reps j).1 with
      | none =>
        simp only [rowStep, hs] at hp
        split at hp
        · simp only [Option.some.injEq] at hp
          subst hp
          simp [hlen]
        · simp at hp
      | some q =>
        simp only [rowStep, hs, Option.some.injEq] at hp
        subst hp
        exact ih q hs
    · have e : prefixState reps (j + 1) = prefixState reps j := by
        unfold prefixState
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [e] at hp
      exact ih p hp

/-! ## One column -/

theorem pass_run (reps : List (List Bool)) (L : ℕ) (hL : ∀ r ∈ reps, r.length = L + 1) (stale BW JP : List Bool)
    (cap : ℕ) (hcap : 2 * L + 13 ≤ cap) :
    Step (StreamController.machine bodyM ((0 : Fin 4).castAdd 1)) (reps.length * (rowCost L + 2) + 1)
      (Fin.addCases (rowHeads 0 []) (fun _ : Fin 1 => 0))
      (Fin.addCases (rowTapes (rowsTape reps stale) [] BW none JP) (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases (rowHeads (reps.flatMap frame).length (pass none reps)) (fun _ : Fin 1 => 0))
      (Fin.addCases (rowTapes (rowsTape reps stale) (pass none reps) BW (prefixState reps reps.length).1 JP)
        (fun _ : Fin 1 => List.replicate cap false)) := by
  let W : WhileBody (4 + 1) _ :=
    { body := bodyM
      tape := (0 : Fin 4).castAdd 1
      bound := reps.length
      H := fun j => Fin.addCases (rowHeads ((reps.take j).flatMap frame).length (prefixState reps j).2)
        (fun _ : Fin 1 => 0)
      A := fun j => Fin.addCases (rowTapes (rowsTape reps stale) (prefixState reps j).2 BW (prefixState reps j).1 JP)
        (fun _ : Fin 1 => List.replicate cap false)
      cost := fun _ => rowCost L
      step := fun j hj => by
        have hlen := hL _ (List.getElem_mem hj)
        obtain ⟨b0, tail, hr⟩ : ∃ b0 tail, reps[j] = b0 :: tail := by
          cases h : reps[j] with
          | nil => rw [h] at hlen; simp at hlen
          | cons b0 tail => exact ⟨b0, tail, rfl⟩
        have htl : tail.length = L := by rw [hr] at hlen; simpa using hlen
        have hs := row_step ((reps.take j).flatMap frame) tail ((reps.drop (j + 1)).flatMap frame ++ false :: stale)
          BW JP (prefixState reps j).2 b0 (prefixState reps j).1 cap
          (fun p hp => by rw [htl]; exact prefixState_piv reps L hL j p hp) (by omega)
        have eA0 : rowsTape reps stale = (reps.take j).flatMap frame ++ frame (b0 :: tail) ++
            ((reps.drop (j + 1)).flatMap frame ++ false :: stale) := by
          rw [← hr]; exact rowsTape_split reps stale j hj
        have eSt : rowStep ((prefixState reps j).1, (prefixState reps j).2) (b0 :: tail) = prefixState reps (j + 1) := by
          rw [prefixState_succ reps j hj, hr]
        have eLen : ((reps.take j).flatMap frame).length + (2 * tail.length + 3) =
            ((reps.take (j + 1)).flatMap frame).length := by
          rw [take_flatMap_succ reps j hj, hr]; simp; omega
        rw [eSt, eLen, ← eA0, htl] at hs
        exact hs
      cont := fun j hj => by
        show readTapeBit (rowsTape reps stale) ((reps.take j).flatMap frame).length = true
        rw [rowsTape_split reps stale j hj]
        have hlen := hL _ (List.getElem_mem hj)
        cases h : reps[j] with
        | nil => rw [h] at hlen; simp at hlen
        | cons b0 tail =>
          simpa [frame, List.append_assoc] using
            Streaming.read_append ((reps.take j).flatMap frame) (b0 :: frame tail ++
              ((reps.drop (j + 1)).flatMap frame ++ false :: stale)) true
      halt := by
        show readTapeBit (rowsTape reps stale) ((reps.take reps.length).flatMap frame).length = false
        rw [List.take_length]
        simpa [rowsTape] using Streaming.read_append (reps.flatMap frame) stale false }
  have hW := W.run
  rw [W.rest_const (rowCost L) (fun _ => rfl)] at hW
  have e0 : W.H 0 = Fin.addCases (rowHeads 0 []) (fun _ : Fin 1 => 0) := rfl
  have eA : W.A 0 = Fin.addCases (rowTapes (rowsTape reps stale) [] BW none JP) (fun _ : Fin 1 => List.replicate cap false) := rfl
  have eH : W.H W.bound = Fin.addCases (rowHeads (reps.flatMap frame).length (pass none reps)) (fun _ : Fin 1 => 0) := by
    dsimp only [W]
    rw [List.take_length, (prefixState_all reps).1]
  have eA' : W.A W.bound = Fin.addCases (rowTapes (rowsTape reps stale) (pass none reps) BW
      (prefixState reps reps.length).1 JP) (fun _ : Fin 1 => List.replicate cap false) := by
    dsimp only [W]
    rw [(prefixState_all reps).1]
  rw [e0, eA, eH, eA'] at hW
  exact hW

/-! ## Small two-tape machines: copy the rows back, tally the rank, check the right-hand sides -/

namespace Two

/-- One action on two tapes. -/
def act {s : ℕ} (next : Fin s) (w0 w1 : Option Bool) (m0 m1 : HeadMove) : Action 2 s :=
  ⟨next, ![w0, w1], ![m0, m1]⟩

def cfg {s : ℕ} (q : Fin s) (A B : List Bool) (ha hb : ℕ) : Configuration 2 s := ⟨q, ![ha, hb], ![A, B]⟩

/-- Write an optional bit at a head. -/
def wr (tape : List Bool) (head : ℕ) : Option Bool → List Bool
  | none => tape
  | some b => writeTapeBit tape head b

theorem step_cfg {s : ℕ} (p : Machine 2 s) (q next : Fin s) (A B : List Bool) (ha hb : ℕ)
    (w0 w1 : Option Bool) (m0 m1 : HeadMove)
    (hr : p.rule q ![readTapeBit A ha, readTapeBit B hb] = some (act next w0 w1 m0 m1)) :
    step p (cfg q A B ha hb) = some (cfg next (wr A ha w0) (wr B hb w1) (m0.apply ha) (m1.apply hb)) := by
  have hs : (cfg q A B ha hb).scanned = ![readTapeBit A ha, readTapeBit B hb] := by
    funext i; fin_cases i <;> rfl
  unfold step
  rw [hs]
  change (p.rule q _).map _ = _
  rw [hr]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · cases w0 <;> rfl
    · cases w1 <;> rfl

end Two

namespace CopyRows
open Two (act cfg wr)

/-- Copy framed rows and their `false` terminator from tape 0 onto tape 1. State `0` is at a row start (a
`false` there is the terminator), `1` at a marker inside a row, `2` at a bit, `3` halts. Rows are nonempty. -/
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 2 none (some true) .right .right else act 3 none (some false) .stay .stay)
    else if q.val = 1 then
      some (if sc 0 then act 2 none (some true) .right .right else act 0 none (some false) .right .right)
    else if q.val = 2 then
      some (if sc 0 then act 1 none (some true) .right .right else act 1 none (some false) .right .right)
    else none

theorem start_true (src out B : List Bool) (hs : ℕ) (hr : readTapeBit src hs = true) :
    step machine (cfg 0 src (overlay out B) hs out.length) =
      some (cfg 2 src (overlay (out ++ [true]) B) (hs + 1) (out.length + 1)) := by
  rw [Two.step_cfg machine 0 2 src (overlay out B) hs out.length none (some true) .right .right
    (by simp [machine, hr])]
  simp [wr, HeadMove.apply, overlay_write]

theorem start_false (src out B : List Bool) (hs : ℕ) (hr : readTapeBit src hs = false) :
    step machine (cfg 0 src (overlay out B) hs out.length) =
      some (cfg 3 src (overlay (out ++ [false]) B) hs out.length) := by
  rw [Two.step_cfg machine 0 3 src (overlay out B) hs out.length none (some false) .stay .stay
    (by simp [machine, hr])]
  simp [wr, HeadMove.apply, overlay_write]

theorem mark_true (src out B : List Bool) (hs : ℕ) (hr : readTapeBit src hs = true) :
    step machine (cfg 1 src (overlay out B) hs out.length) =
      some (cfg 2 src (overlay (out ++ [true]) B) (hs + 1) (out.length + 1)) := by
  rw [Two.step_cfg machine 1 2 src (overlay out B) hs out.length none (some true) .right .right
    (by simp [machine, hr])]
  simp [wr, HeadMove.apply, overlay_write]

theorem mark_false (src out B : List Bool) (hs : ℕ) (hr : readTapeBit src hs = false) :
    step machine (cfg 1 src (overlay out B) hs out.length) =
      some (cfg 0 src (overlay (out ++ [false]) B) (hs + 1) (out.length + 1)) := by
  rw [Two.step_cfg machine 1 0 src (overlay out B) hs out.length none (some false) .right .right
    (by simp [machine, hr])]
  simp [wr, HeadMove.apply, overlay_write]

theorem bit_step (src out B : List Bool) (hs : ℕ) (b : Bool) (hr : readTapeBit src hs = b) :
    step machine (cfg 2 src (overlay out B) hs out.length) =
      some (cfg 1 src (overlay (out ++ [b]) B) (hs + 1) (out.length + 1)) := by
  cases b
  · rw [Two.step_cfg machine 2 1 src (overlay out B) hs out.length none (some false) .right .right
      (by simp [machine, hr])]
    simp [wr, HeadMove.apply, overlay_write]
  · rw [Two.step_cfg machine 2 1 src (overlay out B) hs out.length none (some true) .right .right
      (by simp [machine, hr])]
    simp [wr, HeadMove.apply, overlay_write]

/-- The rest of a row, from a marker: the frame is copied and the machine is back at a row start. -/
theorem frame_timed (B post : List Bool) (w : List Bool) : ∀ (pre out : List Bool),
    RecoveryExecution.Timed machine (2 * w.length + 1)
      (cfg 1 (pre ++ frame w ++ post) (overlay out B) pre.length out.length)
      (cfg 0 (pre ++ frame w ++ post) (overlay (out ++ frame w) B) (pre.length + (2 * w.length + 1))
        (out.length + (2 * w.length + 1))) := by
  induction w with
  | nil =>
    intro pre out
    have hs := mark_false (pre ++ frame [] ++ post) out B pre.length
      (by simpa [frame] using Streaming.read_append pre post false)
    simpa [frame] using RecoveryExecution.Timed.single (p := machine) rfl hs
  | cons a w ih =>
    intro pre out
    have e : pre ++ frame (a :: w) ++ post = pre ++ [true, a] ++ frame w ++ post := by simp [frame]
    have hr1 : readTapeBit (pre ++ frame (a :: w) ++ post) pre.length = true := by
      simpa [frame] using Streaming.read_append pre (a :: (frame w ++ post)) true
    have hr2 : readTapeBit (pre ++ frame (a :: w) ++ post) (pre.length + 1) = a := by
      simpa [frame] using Streaming.read_append (pre ++ [true]) (frame w ++ post) a
    have hs1 := mark_true (pre ++ frame (a :: w) ++ post) out B pre.length hr1
    have hs2 := bit_step (pre ++ frame (a :: w) ++ post) (out ++ [true]) B (pre.length + 1) a hr2
    have e1 : (out ++ [true]).length = out.length + 1 := by simp
    rw [e1] at hs2
    have t1 := RecoveryExecution.Timed.single (p := machine) rfl hs1
    have t2 := RecoveryExecution.Timed.single (p := machine) rfl hs2
    have tail := ih (pre ++ [true, a]) (out ++ [true] ++ [a])
    rw [← e] at tail
    have e2 : (out ++ [true] ++ [a]).length = out.length + 1 + 1 := by simp
    have e3 : (pre ++ [true, a]).length = pre.length + 1 + 1 := by simp
    have e4 : out ++ [true] ++ [a] ++ frame w = out ++ frame (a :: w) := by simp [frame]
    have e5 : pre.length + 1 + 1 + (2 * w.length + 1) = pre.length + (2 * (a :: w).length + 1) := by simp; omega
    have e6 : out.length + 1 + 1 + (2 * w.length + 1) = out.length + (2 * (a :: w).length + 1) := by simp; omega
    rw [e2, e3, e4, e5, e6] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (a :: w).length + 1 by simp; omega] at this

/-- All rows, then the terminator: every cell is copied in one step. -/
theorem rows_timed (B post : List Bool) (rows : List (List Bool)) (hne : ∀ r ∈ rows, r ≠ []) : ∀ (pre out : List Bool),
    RecoveryExecution.Timed machine ((rows.flatMap frame).length + 1)
      (cfg 0 (pre ++ rows.flatMap frame ++ false :: post) (overlay out B) pre.length out.length)
      (cfg 3 (pre ++ rows.flatMap frame ++ false :: post) (overlay (out ++ rows.flatMap frame ++ [false]) B)
        (pre.length + (rows.flatMap frame).length) (out.length + (rows.flatMap frame).length)) := by
  induction rows with
  | nil =>
    intro pre out
    have hs := start_false (pre ++ [].flatMap frame ++ false :: post) out B pre.length
      (by simpa using Streaming.read_append pre post false)
    simpa using RecoveryExecution.Timed.single (p := machine) rfl hs
  | cons r rows ih =>
    intro pre out
    obtain ⟨b, w, rfl⟩ : ∃ b w, r = b :: w := by
      cases r with
      | nil => exact absurd rfl (hne [] List.mem_cons_self)
      | cons b w => exact ⟨b, w, rfl⟩
    have hne' : ∀ r ∈ rows, r ≠ [] := fun r hr => hne r (List.mem_cons_of_mem _ hr)
    let src := pre ++ ((b :: w) :: rows).flatMap frame ++ false :: post
    have ea : src = pre ++ [true, b] ++ frame w ++ (rows.flatMap frame ++ false :: post) := by
      simp [src, frame, List.append_assoc]
    have eb : src = pre ++ frame (b :: w) ++ rows.flatMap frame ++ false :: post := by
      simp [src, List.append_assoc]
    have hr1 : readTapeBit src pre.length = true := by
      rw [ea]; simpa [List.append_assoc] using Streaming.read_append pre (b :: (frame w ++ (rows.flatMap frame ++ false :: post))) true
    have hr2 : readTapeBit src (pre.length + 1) = b := by
      rw [ea]; simpa [List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ (rows.flatMap frame ++ false :: post)) b
    have hs1 := start_true src out B pre.length hr1
    have hs2 := bit_step src (out ++ [true]) B (pre.length + 1) b hr2
    have e1 : (out ++ [true]).length = out.length + 1 := by simp
    rw [e1] at hs2
    have t1 := RecoveryExecution.Timed.single (p := machine) rfl hs1
    have t2 := RecoveryExecution.Timed.single (p := machine) rfl hs2
    have t3 := frame_timed B (rows.flatMap frame ++ false :: post) w (pre ++ [true, b]) (out ++ [true] ++ [b])
    rw [← ea] at t3
    have e2 : (out ++ [true] ++ [b]).length = out.length + 1 + 1 := by simp
    have e3 : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    rw [e2, e3] at t3
    have t4 := ih hne' (pre ++ frame (b :: w)) (out ++ frame (b :: w))
    have eb' : pre ++ frame (b :: w) ++ rows.flatMap frame ++ false :: post = src := eb.symm
    rw [eb'] at t4
    have e4 : out ++ [true] ++ [b] ++ frame w = out ++ frame (b :: w) := by simp [frame]
    have e5 : pre.length + 1 + 1 + (2 * w.length + 1) = (pre ++ frame (b :: w)).length := by simp; omega
    have e6 : out.length + 1 + 1 + (2 * w.length + 1) = (out ++ frame (b :: w)).length := by simp; omega
    rw [e4, e5, e6] at t3
    have e7 : out ++ frame (b :: w) ++ rows.flatMap frame ++ [false] = out ++ ((b :: w) :: rows).flatMap frame ++ [false] := by
      simp [List.append_assoc]
    have e8 : (pre ++ frame (b :: w)).length + (rows.flatMap frame).length = pre.length + (((b :: w) :: rows).flatMap frame).length := by
      simp; omega
    have e9 : (out ++ frame (b :: w)).length + (rows.flatMap frame).length = out.length + (((b :: w) :: rows).flatMap frame).length := by
      simp; omega
    rw [e7, e8, e9] at t4
    have := ((t1.trans t2).trans t3).trans t4
    rwa [show 1 + 1 + (2 * w.length + 1) + ((rows.flatMap frame).length + 1) =
      (((b :: w) :: rows).flatMap frame).length + 1 by simp; omega] at this

/-- **Copy the rows back** as one `Step`: `rows` framed and terminated on tape 0 are written over tape 1. -/
theorem run (rows : List (List Bool)) (hne : ∀ r ∈ rows, r ≠ []) (post B : List Bool) :
    Step machine ((rows.flatMap frame).length + 1) ![0, 0] ![rows.flatMap frame ++ false :: post, B]
      ![(rows.flatMap frame).length, (rows.flatMap frame).length]
      ![rows.flatMap frame ++ false :: post, overlay (rows.flatMap frame ++ [false]) B] := by
  obtain ⟨r, hr, hf, hs⟩ := (rows_timed B post rows hne [] []).run rfl
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; simp [cfg]
  · rw [hf]; simp [cfg]

end CopyRows

/-! ### The rank tally and the terminator -/

namespace Tally
open Two (act cfg wr)

/-- Move the found flag onto the rank: if tape 0 reads `true`, clear it and append `true` to tape 1. -/
def machine : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 1 (some false) (some true) .stay .right else act 1 none none .stay .stay)
    else none

theorem run (f : Bool) (k : ℕ) :
    Step machine 1 ![0, k] ![[f], List.replicate k true]
      ![0, k + (if f then 1 else 0)] ![[false], List.replicate (k + (if f then 1 else 0)) true] := by
  cases f
  · have hs : step machine (cfg 0 [false] (List.replicate k true) 0 k) =
        some (cfg 1 [false] (List.replicate k true) 0 k) := by
      rw [Two.step_cfg machine 0 1 [false] (List.replicate k true) 0 k none none .stay .stay
        (by simp [machine, readTapeBit])]
      rfl
    obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := machine) rfl hs).run rfl
    exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩
  · have hs : step machine (cfg 0 [true] (List.replicate k true) 0 k) =
        some (cfg 1 [false] (List.replicate (k + 1) true) 0 (k + 1)) := by
      rw [Two.step_cfg machine 0 1 [true] (List.replicate k true) 0 k (some false) (some true) .stay .right
        (by simp [machine, readTapeBit])]
      have hw : writeTapeBit (List.replicate k true) k true = List.replicate (k + 1) true := by
        simp [List.replicate_succ']
      simp only [wr, HeadMove.apply, hw]
      rfl
    obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := machine) rfl hs).run rfl
    exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end Tally

/-- Write `false` under the head (the output's terminator), without moving. -/
def termM : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some false, fun _ => .stay⟩ else none

theorem term_run (X B : List Bool) : Step termM 1 ![X.length] ![overlay X B] ![X.length] ![overlay (X ++ [false]) B] := by
  have hs : step termM ⟨termM.start, ![X.length], ![overlay X B]⟩ = some ⟨1, ![X.length], ![overlay (X ++ [false]) B]⟩ := by
    simp [step, termM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, overlay_write]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := termM) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

theorem nudge_step (tape : List Bool) (h : ℕ) : Step nudge 1 ![h] ![tape] ![h + 1] ![tape] := by
  obtain ⟨r, hr, hh, ht⟩ := nudge_run tape h
  exact Step.of_run hr hh ht

/-! ### The final check: every remaining row `[rhs]` has a clear right-hand side -/

namespace CheckRhs
open Two (act cfg wr)

/-- Tape 0 holds rows `[b]`, framed and terminated; tape 1 the flag. State `0` at a row start, `1` at the
row's bit (a set bit clears the flag), `2` at the row's end marker, `3` halts. -/
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 1 none none .right .stay else act 3 none none .stay .stay)
    else if q.val = 1 then some (if sc 0 then act 2 none (some false) .right .stay else act 2 none none .right .stay)
    else if q.val = 2 then some (act 0 none none .right .stay)
    else none

theorem timed (post : List Bool) (bs : List Bool) : ∀ (pre : List Bool) (g : Bool),
    RecoveryExecution.Timed machine (3 * bs.length + 1)
      (cfg 0 (pre ++ (bs.map (fun b => [b])).flatMap frame ++ false :: post) [g] pre.length 0)
      (cfg 3 (pre ++ (bs.map (fun b => [b])).flatMap frame ++ false :: post) [g && bs.all (fun b => !b)]
        (pre.length + 3 * bs.length) 0) := by
  induction bs with
  | nil =>
    intro pre g
    have hs : step machine (cfg 0 (pre ++ false :: post) [g] pre.length 0) =
        some (cfg 3 (pre ++ false :: post) [g] pre.length 0) := by
      rw [Two.step_cfg machine 0 3 (pre ++ false :: post) [g] pre.length 0 none none .stay .stay
        (by simp [machine, Streaming.read_append pre post false])]
      rfl
    simpa using RecoveryExecution.Timed.single (p := machine) rfl hs
  | cons b bs ih =>
    intro pre g
    let src := pre ++ ((b :: bs).map (fun b => [b])).flatMap frame ++ false :: post
    have ea : src = pre ++ true :: b :: false :: ((bs.map (fun b => [b])).flatMap frame ++ false :: post) := by
      simp [src, frame, List.append_assoc]
    have eb : pre ++ [true, b, false] ++ (bs.map (fun b => [b])).flatMap frame ++ false :: post = src := by
      simp [src, frame, List.append_assoc]
    have hr0 : readTapeBit src pre.length = true := by rw [ea]; exact Streaming.read_append pre _ true
    have hr1 : readTapeBit src (pre.length + 1) = b := by
      rw [ea]; simpa using Streaming.read_append (pre ++ [true]) (false :: ((bs.map (fun b => [b])).flatMap frame ++ false :: post)) b
    have hs0 : step machine (cfg 0 src [g] pre.length 0) = some (cfg 1 src [g] (pre.length + 1) 0) := by
      rw [Two.step_cfg machine 0 1 src [g] pre.length 0 none none .right .stay (by simp [machine, hr0])]
      rfl
    have hs1 : step machine (cfg 1 src [g] (pre.length + 1) 0) = some (cfg 2 src [g && !b] (pre.length + 1 + 1) 0) := by
      cases b
      · rw [Two.step_cfg machine 1 2 src [g] (pre.length + 1) 0 none none .right .stay (by simp [machine, hr1])]
        simp [wr, HeadMove.apply]
      · rw [Two.step_cfg machine 1 2 src [g] (pre.length + 1) 0 none (some false) .right .stay (by simp [machine, hr1])]
        simp [wr, HeadMove.apply, writeTapeBit]
    have hs2 : step machine (cfg 2 src [g && !b] (pre.length + 1 + 1) 0) =
        some (cfg 0 src [g && !b] (pre.length + 1 + 1 + 1) 0) := by
      rw [Two.step_cfg machine 2 0 src [g && !b] (pre.length + 1 + 1) 0 none none .right .stay (by simp [machine])]
      rfl
    have t0 := RecoveryExecution.Timed.single (p := machine) rfl hs0
    have t1 := RecoveryExecution.Timed.single (p := machine) rfl hs1
    have t2 := RecoveryExecution.Timed.single (p := machine) rfl hs2
    have tail := ih (pre ++ [true, b, false]) (g && !b)
    rw [eb] at tail
    have e3 : (pre ++ [true, b, false]).length = pre.length + 1 + 1 + 1 := by simp
    have e4 : (g && !b && bs.all (fun b => !b)) = (g && (b :: bs).all (fun b => !b)) := by
      simp [Bool.and_assoc]
    have e5 : pre.length + 1 + 1 + 1 + 3 * bs.length = pre.length + 3 * (b :: bs).length := by simp; omega
    rw [e3, e4, e5] at tail
    have := ((t0.trans t1).trans t2).trans tail
    rwa [show 1 + 1 + 1 + (3 * bs.length + 1) = 3 * (b :: bs).length + 1 by simp; omega] at this

theorem run (bs post : List Bool) (g : Bool) :
    Step machine (3 * bs.length + 1) ![0, 0] ![(bs.map (fun b => [b])).flatMap frame ++ false :: post, [g]]
      ![3 * bs.length, 0] ![(bs.map (fun b => [b])).flatMap frame ++ false :: post, [g && bs.all (fun b => !b)]] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed post bs [] g).run rfl
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; simp [cfg]
  · rw [hf]; simp [cfg]

end CheckRhs

/-! ## The column loop

Tapes: 0 the rows `R`, 1 the pass output `W`, 2 the pivot `P`, 3 the found flag `F`, 4 the row body's rewind
log, 5 the rank `K` (unary, appended), 6 the column counter `N` (`nvars` cells), 7 the consistency flag `G`,
8 the rewind log of the column stages. One column: the pass and the output's terminator (then `R` and `W`
rewound), the rank tally, the rows copied back from `W` to `R` (then rewound), one step of `N`. -/

/-- Pass output rows keep the uniform length. -/
theorem pass_length (L : ℕ) (reps : List (List Bool)) : ∀ (st : Option (List Bool)),
    (∀ r ∈ reps, r.length = L + 1) → (∀ p, st = some p → p.length = L) → ∀ r ∈ pass st reps, r.length = L := by
  induction reps with
  | nil => intro st _ _ r hr; simp [pass] at hr
  | cons x xs ih =>
    intro st hx hp r hr
    have hxl : x.length = L + 1 := hx x List.mem_cons_self
    have hxs : ∀ r ∈ xs, r.length = L + 1 := fun r h => hx r (List.mem_cons_of_mem _ h)
    cases st with
    | none =>
      simp only [pass] at hr
      split at hr
      · exact ih (some x.tail) hxs (fun p h => by simp only [Option.some.injEq] at h; subst h; simp [hxl]) r hr
      · rcases List.mem_cons.mp hr with rfl | h
        · simp [hxl]
        · exact ih none hxs (fun p h => by simp at h) r h
    | some q =>
      have hq := hp q rfl
      simp only [pass] at hr
      rcases List.mem_cons.mp hr with rfl | h
      · split <;> simp [hxl, hq]
      · exact ih (some q) hxs hp r h

theorem pass_count : ∀ (reps : List (List Bool)) (st : Option (List Bool)), (pass st reps).length ≤ reps.length
  | [], _ => by simp [pass]
  | x :: xs, none => by
      simp only [pass]
      split
      · have := pass_count xs (some x.tail); simp; omega
      · have := pass_count xs none; simp; omega
  | x :: xs, some p => by
      simp only [pass, List.length_cons]
      have := pass_count xs (some p); omega

/-- The column loop's state: the rows, the rank, and the stale contents of `R`, `W` and `P`. -/
structure ColState where
  reps : List (List Bool)
  rank : ℕ
  stale : List Bool
  W : List Bool
  P : List Bool

/-- One column on the state. -/
def ColState.next (s : ColState) : ColState where
  reps := pass none s.reps
  rank := s.rank + if found s.reps then 1 else 0
  stale := (rowsTape s.reps s.stale).drop (((pass none s.reps).flatMap frame).length + 1)
  W := overlay ((pass none s.reps).flatMap frame ++ [false]) s.W
  P := pivTape (prefixState s.reps s.reps.length).1 s.P

abbrev T : ℕ := 4 + 1 + 3

/-- The bank before column `c`. -/
def colH (s : ColState) (c : ℕ) : Fin (T + 1) → ℕ := ![0, 0, 0, 0, 0, s.rank, c, 0, 0]
def colA (nvars cap cap' : ℕ) (s : ColState) : Fin (T + 1) → List Bool :=
  ![rowsTape s.reps s.stale, s.W, s.P, [false], List.replicate cap false, List.replicate s.rank true,
    List.replicate nvars true, [true], List.replicate cap' false]

theorem dockRun {t u s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (RecoveryRootRound.install slots A tout) := by
  have hf := h.focus slots hi H A
  have e1 : dockH slots H hin = H := by
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [dockH, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [dockH, hp]
      rw [← he]
      exact (hH j).symm
  rwa [e1, RecoveryRootRound.install_existing slots A tin hA] at hf

/-! ### Stage A: the pass, the terminator, then `R` and `W` rewound -/

def R5 : Fin (4 + 1) := (0 : Fin 4).castAdd 1
def slotTerm : Fin 1 → Fin (4 + 1) := ![1]
noncomputable def passT := Composition.machine (StreamController.machine bodyM R5) (RecoveryFocus.machine slotTerm termM)
noncomputable def passTE := TapeEmbedding.machine 3 passT
def selRW : Fin T → Bool := fun i => decide (i = 0 ∨ i = 1)
noncomputable def stageA := MaskedReset.machine passTE selRW

theorem dockH_term (H : Fin (4 + 1) → ℕ) (v : Fin 1 → ℕ) :
    dockH slotTerm H v = ![H 0, v 0, H 2, H 3, H 4] := by
  funext i
  fin_cases i
  · exact dockH_other _ _ _ _ (by decide)
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_other _ _ _ _ (by decide)
  · exact dockH_other _ _ _ _ (by decide)
  · exact dockH_other _ _ _ _ (by decide)

theorem install_term (A : Fin (4 + 1) → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slotTerm A v = ![A 0, v 0, A 2, A 3, A 4] := by
  funext i
  fin_cases i
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  · exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def passCostA (m L : ℕ) : ℕ := m * (rowCost L + 2) + 1 + 1 + 1

/-- Stage A as one `Step`: after it, `W` holds the pass output and its terminator, `P` the pass's pivot tape,
`F` the found flag; the heads of `R` and `W` are back at cell 0. -/
theorem stageA_step (s : ColState) (c L nvars cap cap' : ℕ) (hL : ∀ r ∈ s.reps, r.length = L + 1)
    (hcap : 2 * L + 13 ≤ cap) (hcap' : passCostA s.reps.length L ≤ cap') :
    Step stageA (2 * passCostA s.reps.length L + 2) (colH s c) (colA nvars cap cap' s)
      (colH s c)
      ![rowsTape s.reps s.stale, s.next.W, s.next.P, [found s.reps], List.replicate cap false,
        List.replicate s.rank true, List.replicate nvars true, [true], List.replicate cap' false] := by
  have hp := pass_run s.reps L hL s.stale s.W s.P cap hcap
  have ht := dockRun (term_run ((pass none s.reps).flatMap frame) s.W) slotTerm (by decide)
    (Fin.addCases (rowHeads (s.reps.flatMap frame).length (pass none s.reps)) (fun _ : Fin 1 => 0))
    (Fin.addCases (rowTapes (rowsTape s.reps s.stale) (pass none s.reps) s.W (prefixState s.reps s.reps.length).1 s.P)
      (fun _ : Fin 1 => List.replicate cap false))
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_term, install_term] at ht
  have he := (hp.seq ht).embed ![s.rank, c, 0] ![List.replicate s.rank true, List.replicate nvars true, [true]]
  have hm := he.mask selRW (by intro i hi; fin_cases i <;> first | rfl | simp [selRW] at hi) hcap'
  refine (hm.congr_in ?_ ?_).congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    all_goals first
      | rfl
      | (show [(prefixState s.reps s.reps.length).1.isSome] = [found s.reps]
         rw [(prefixState_all s.reps).2])

/-! ### Stages B, C, D: the rank tally, the rows copied back, the column counter -/

def slotsB : Fin 2 → Fin (T + 1) := ![3, 5]
def slotsC : Fin 2 → Fin T := ![1, 0]
def slotsD : Fin 1 → Fin (T + 1) := ![6]
noncomputable def stageB := RecoveryFocus.machine slotsB Tally.machine
noncomputable def stageC := MaskedReset.machine (RecoveryFocus.machine slotsC CopyRows.machine) selRW
noncomputable def stageD := RecoveryFocus.machine slotsD nudge

theorem dockH_B (H : Fin (T + 1) → ℕ) (v : Fin 2 → ℕ) :
    dockH slotsB H v = ![H 0, H 1, H 2, v 0, H 4, v 1, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

theorem install_B (A : Fin (T + 1) → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slotsB A v = ![A 0, A 1, A 2, v 0, A 4, v 1, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_C (H : Fin T → ℕ) (v : Fin 2 → ℕ) :
    dockH slotsC H v = ![v 1, v 0, H 2, H 3, H 4, H 5, H 6, H 7] := by
  funext i
  fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

theorem install_C (A : Fin T → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slotsC A v = ![v 1, v 0, A 2, A 3, A 4, A 5, A 6, A 7] := by
  funext i
  fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_D (H : Fin (T + 1) → ℕ) (v : Fin 1 → ℕ) :
    dockH slotsD H v = ![H 0, H 1, H 2, H 3, H 4, H 5, v 0, H 7, H 8] := by
  funext i
  fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

theorem install_D (A : Fin (T + 1) → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slotsD A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 0, A 7, A 8] := by
  funext i
  fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem overlay_term (X W : List Bool) : overlay (X ++ [false]) W = X ++ false :: W.drop (X.length + 1) := by
  simp [overlay, List.append_assoc]

theorem rowsTape_next (s : ColState) :
    overlay ((pass none s.reps).flatMap frame ++ [false]) (rowsTape s.reps s.stale) =
      rowsTape s.next.reps s.next.stale := by
  rw [overlay_term]; rfl

/-- The tapes between stages A and B. -/
def midA (nvars cap cap' : ℕ) (s : ColState) (f : Bool) (k : ℕ) : Fin (T + 1) → List Bool :=
  ![rowsTape s.reps s.stale, s.next.W, s.next.P, [f], List.replicate cap false,
    List.replicate k true, List.replicate nvars true, [true], List.replicate cap' false]

theorem stageB_step (s : ColState) (c nvars cap cap' : ℕ) :
    Step stageB 1 (colH s c) (midA nvars cap cap' s (found s.reps) s.rank)
      (colH s.next c) (midA nvars cap cap' s false s.next.rank) := by
  have h := dockRun (Tally.run (found s.reps) s.rank) slotsB (by decide) (colH s c)
    (midA nvars cap cap' s (found s.reps) s.rank) (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_B, install_B] at h
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def copyCost (s : ColState) : ℕ := ((pass none s.reps).flatMap frame).length + 1

theorem stageC_step (s : ColState) (c nvars cap cap' : ℕ) (hne : ∀ r ∈ pass none s.reps, r ≠ [])
    (hcap' : copyCost s ≤ cap') :
    Step stageC (2 * copyCost s + 2) (colH s.next c) (midA nvars cap cap' s false s.next.rank)
      (colH s.next c) (colA nvars cap cap' s.next) := by
  have hr := CopyRows.run (pass none s.reps) hne (s.W.drop (((pass none s.reps).flatMap frame).length + 1))
    (rowsTape s.reps s.stale)
  rw [← overlay_term, rowsTape_next] at hr
  have h := dockRun hr slotsC (by decide)
    ![0, 0, 0, 0, 0, s.next.rank, c, 0]
    ![rowsTape s.reps s.stale, s.next.W, s.next.P, [false], List.replicate cap false,
      List.replicate s.next.rank true, List.replicate nvars true, [true]]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_C, install_C] at h
  have hm := h.mask selRW (by intro i hi; fin_cases i <;> first | rfl | simp [selRW] at hi) hcap'
  refine (hm.congr_in ?_ ?_).congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem stageD_step (s : ColState) (c nvars cap cap' : ℕ) :
    Step stageD 1 (colH s c) (colA nvars cap cap' s) (colH s (c + 1)) (colA nvars cap cap' s) := by
  have h := dockRun (nudge_step (List.replicate nvars true) c) slotsD (by decide) (colH s c) (colA nvars cap cap' s)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_D, install_D] at h
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- **One column** of the elimination: from the bank of state `s` before column `c` to the bank of
`s.next` before column `c + 1`. -/
noncomputable def colBody := Composition.machine (Composition.machine (Composition.machine stageA stageB) stageC) stageD

def colCost (s : ColState) (L : ℕ) : ℕ := 2 * passCostA s.reps.length L + 2 + 1 + 1 + 1 + (2 * copyCost s + 2) + 1 + 1

theorem col_step (s : ColState) (c L nvars cap cap' : ℕ) (hL : ∀ r ∈ s.reps, r.length = L + 1) (hL1 : 1 ≤ L)
    (hcap : 2 * L + 13 ≤ cap) (hcapA : passCostA s.reps.length L ≤ cap') (hcapC : copyCost s ≤ cap') :
    Step colBody (colCost s L) (colH s c) (colA nvars cap cap' s) (colH s.next (c + 1)) (colA nvars cap cap' s.next) := by
  have hne : ∀ r ∈ pass none s.reps, r ≠ [] := by
    intro r hr h
    have := pass_length L s.reps none hL (fun p hp => by simp at hp) r hr
    rw [h] at this
    simp at this
    omega
  exact (((stageA_step s c L nvars cap cap' hL hcap hcapA).seq (stageB_step s c nvars cap cap')).seq
    (stageC_step s c nvars cap cap' hne hcapC)).seq (stageD_step s.next c nvars cap cap')

/-! ### The loop over the columns -/

/-- The state before column `c`. -/
def colState (s0 : ColState) : ℕ → ColState
  | 0 => s0
  | c + 1 => (colState s0 c).next

theorem colState_passes (s0 : ColState) (c : ℕ) :
    ((colState s0 c).reps, (colState s0 c).rank) = passes c (s0.reps, s0.rank) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    show (pass none (colState s0 c).reps, (colState s0 c).rank + if found (colState s0 c).reps then 1 else 0) = _
    rw [passes, ← ih]

theorem colState_length (s0 : ColState) (nvars : ℕ) (h0 : ∀ r ∈ s0.reps, r.length = nvars + 1) (c : ℕ) (hc : c ≤ nvars) :
    ∀ r ∈ (colState s0 c).reps, r.length = nvars - c + 1 := by
  induction c with
  | zero => exact h0
  | succ c ih =>
    have hL := ih (by omega)
    have hp := pass_length (nvars - c) (colState s0 c).reps none hL (fun p hp => by simp at hp)
    intro r hr
    rw [hp r hr]
    omega

theorem colState_count (s0 : ColState) (c : ℕ) : (colState s0 c).reps.length ≤ s0.reps.length := by
  induction c with
  | zero => exact le_refl _
  | succ c ih => exact (pass_count _ none).trans ih

theorem flatMap_frame_length (rows : List (List Bool)) (K : ℕ) (h : ∀ r ∈ rows, r.length = K) :
    (rows.flatMap frame).length = rows.length * (2 * K + 1) := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    rw [List.flatMap_cons, List.length_append, frame_length, h r List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.length_cons]
    ring

theorem read_rep (n i : ℕ) : readTapeBit (List.replicate n true) i = decide (i < n) := by
  by_cases h : i < n
  · have e : List.replicate n true = List.replicate i true ++ true :: List.replicate (n - i - 1) true := by
      rw [← List.replicate_succ, ← List.replicate_add]; congr 1; omega
    rw [e, decide_eq_true h]
    simpa using Streaming.read_append (List.replicate i true) (List.replicate (n - i - 1) true) true
  · rw [decide_eq_false h]
    unfold readTapeBit
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

/-- The uniform per-column cost bound for `m` rows of `nvars + 1` bits. -/
def colBound (m nvars : ℕ) : ℕ :=
  2 * (m * (rowCost nvars + 2) + 3) + 2 + 1 + 1 + 1 + (2 * (m * (2 * nvars + 1) + 1) + 2) + 1 + 1

theorem colCost_le (s : ColState) (m L nvars : ℕ) (hm : s.reps.length ≤ m) (hL : ∀ r ∈ s.reps, r.length = L + 1)
    (hLn : L ≤ nvars) : colCost s L ≤ colBound m nvars ∧ passCostA s.reps.length L ≤ m * (rowCost nvars + 2) + 3 ∧
      copyCost s ≤ m * (2 * nvars + 1) + 1 := by
  have hX : ((pass none s.reps).flatMap frame).length = (pass none s.reps).length * (2 * L + 1) :=
    flatMap_frame_length _ L (pass_length L s.reps none hL (fun p hp => by simp at hp))
  have hc := pass_count s.reps none
  have h1 : s.reps.length * (rowCost L + 2) ≤ m * (rowCost nvars + 2) :=
    Nat.mul_le_mul hm (by unfold rowCost; omega)
  have h2 : (pass none s.reps).length * (2 * L + 1) ≤ m * (2 * nvars + 1) :=
    Nat.mul_le_mul (hc.trans hm) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold colCost colBound passCostA copyCost; rw [hX]; omega
  · unfold passCostA; omega
  · unfold copyCost; rw [hX]; omega

def N9 : Fin (T + 1) := 6

/-- **The column loop**: `nvars` columns, as one `Step` of the stream loop over the counter tape. -/
theorem cols_run (s0 : ColState) (nvars cap cap' : ℕ) (h0 : ∀ r ∈ s0.reps, r.length = nvars + 1)
    (hcap : 2 * nvars + 13 ≤ cap) (hcap' : s0.reps.length * (rowCost nvars + 2) + 3 ≤ cap')
    (hcap'' : s0.reps.length * (2 * nvars + 1) + 1 ≤ cap') :
    Step (StreamController.machine colBody N9) (nvars * (colBound s0.reps.length nvars + 2) + 1)
      (colH s0 0) (colA nvars cap cap' s0) (colH (colState s0 nvars) nvars) (colA nvars cap cap' (colState s0 nvars)) := by
  let W : WhileBody (T + 1) _ :=
    { body := colBody
      tape := N9
      bound := nvars
      H := fun c => colH (colState s0 c) c
      A := fun c => colA nvars cap cap' (colState s0 c)
      cost := fun _ => colBound s0.reps.length nvars
      step := fun c hc => by
        have hL := colState_length s0 nvars h0 c (by omega)
        have e : nvars - c + 1 = (nvars - c) + 1 := rfl
        obtain ⟨hk, hA, hC⟩ := colCost_le (colState s0 c) s0.reps.length (nvars - c) nvars
          (colState_count s0 c) hL (by omega)
        exact (col_step (colState s0 c) c (nvars - c) nvars cap cap' hL (by omega) (by omega)
          (hA.trans hcap') (hC.trans hcap'')).enlarge hk
      cont := fun c hc => by
        show readTapeBit (List.replicate nvars true) c = true
        rw [read_rep]; simpa using hc
      halt := by
        show readTapeBit (List.replicate nvars true) nvars = false
        rw [read_rep]; simp }
  have hW := W.run
  rw [W.rest_const _ (fun _ => rfl)] at hW
  exact hW

/-! ## The whole elimination -/

def slotsE : Fin 2 → Fin (T + 1) := ![0, 7]
noncomputable def stageE := RecoveryFocus.machine slotsE CheckRhs.machine

/-- **The binary elimination machine**: the column loop, then the right-hand-side check. -/
noncomputable def gaussM := Composition.machine (StreamController.machine colBody N9) stageE

theorem dockH_E (H : Fin (T + 1) → ℕ) (v : Fin 2 → ℕ) :
    dockH slotsE H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, v 1, H 8] := by
  funext i
  fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

theorem install_E (A : Fin (T + 1) → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slotsE A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, v 1, A 8] := by
  funext i
  fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem singletons (rows : List (List Bool)) (h : ∀ r ∈ rows, r.length = 1) :
    rows = (rows.map (fun r => r.headD false)).map (fun b => [b]) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have hr := h r List.mem_cons_self
    obtain ⟨b, rfl⟩ : ∃ b, r = [b] := by
      match r, hr with
      | [b], _ => exact ⟨b, rfl⟩
    simp only [List.map_cons, List.headD_cons]
    rw [← ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The entry layout: the rows (each the `nvars` mask bits, low first, then the right-hand side) framed and
terminated; the column counter `nvars` cells; the flag `G` set; two all-false rewind logs. -/
def gaussIn (nvars : ℕ) (rows : List Row) (cap cap' : ℕ) : Fin (T + 1) → List Bool :=
  ![rowsTape (rows.map (rowBits nvars)) [], [], [], [false], List.replicate cap false, [],
    List.replicate nvars true, [true], List.replicate cap' false]

def gaussCost (m nvars : ℕ) : ℕ := nvars * (colBound m nvars + 2) + 1 + 1 + (3 * m + 1)

/-- The final check on the state after the last column (every row is `[rhs]`). -/
theorem check_step (sf : ColState) (nvars cap cap' : ℕ) (hlen : ∀ r ∈ sf.reps, r.length = 1) :
    Step stageE (3 * sf.reps.length + 1) (colH sf nvars) (colA nvars cap cap' sf)
      ![3 * sf.reps.length, 0, 0, 0, 0, sf.rank, nvars, 0, 0]
      ![rowsTape sf.reps sf.stale, sf.W, sf.P, [false], List.replicate cap false, List.replicate sf.rank true,
        List.replicate nvars true, [sf.reps.all (fun r => !(r.headD false))], List.replicate cap' false] := by
  have hc := CheckRhs.run (sf.reps.map (fun r => r.headD false)) sf.stale true
  rw [← singletons sf.reps hlen] at hc
  have hE := dockRun hc slotsE (by decide) (colH sf nvars) (colA nvars cap cap' sf)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_E, install_E, List.length_map] at hE
  have hG : [true && (sf.reps.map (fun r => r.headD false)).all (fun b => !b)] =
      [sf.reps.all (fun r => !(r.headD false))] := by
    simp [List.all_map, Function.comp_def]
  have hR : List.flatMap frame sf.reps ++ false :: sf.stale = rowsTape sf.reps sf.stale := rfl
  rw [hR, hG] at hE
  refine hE.congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

/-- The whole machine on any start state: the column loop, then the check. -/
theorem gauss_raw (s0 : ColState) (nvars cap cap' : ℕ) (h0 : ∀ r ∈ s0.reps, r.length = nvars + 1)
    (hcap : 2 * nvars + 13 ≤ cap) (hcap' : s0.reps.length * (rowCost nvars + 2) + 3 ≤ cap')
    (hcap'' : s0.reps.length * (2 * nvars + 1) + 1 ≤ cap') :
    Step gaussM (nvars * (colBound s0.reps.length nvars + 2) + 1 + 1 + (3 * (colState s0 nvars).reps.length + 1))
      (colH s0 0) (colA nvars cap cap' s0)
      ![3 * (colState s0 nvars).reps.length, 0, 0, 0, 0, (colState s0 nvars).rank, nvars, 0, 0]
      ![rowsTape (colState s0 nvars).reps (colState s0 nvars).stale, (colState s0 nvars).W, (colState s0 nvars).P,
        [false], List.replicate cap false, List.replicate (colState s0 nvars).rank true, List.replicate nvars true,
        [(colState s0 nvars).reps.all (fun r => !(r.headD false))], List.replicate cap' false] := by
  have hlen : ∀ r ∈ (colState s0 nvars).reps, r.length = 1 := by
    intro r hr
    have := colState_length s0 nvars h0 nvars (le_refl _) r hr
    omega
  exact (cols_run s0 nvars cap cap' h0 hcap hcap' hcap'').seq (check_step (colState s0 nvars) nvars cap cap' hlen)

theorem gauss_run (nvars : ℕ) (rows : List Row) (hrows : ∀ r ∈ rows, r.1 < 2 ^ nvars) (cap cap' : ℕ)
    (hcap : 2 * nvars + 13 ≤ cap) (hcap' : rows.length * (rowCost nvars + 2) + 3 ≤ cap')
    (hcap'' : rows.length * (2 * nvars + 1) + 1 ≤ cap') :
    ∃ (hR : ℕ) (R W P : List Bool), Step gaussM (gaussCost rows.length nvars) ![0, 0, 0, 0, 0, 0, 0, 0, 0]
      (gaussIn nvars rows cap cap')
      ![hR, 0, 0, 0, 0, (gauss nvars rows).2, nvars, 0, 0]
      ![R, W, P, [false], List.replicate cap false, List.replicate (gauss nvars rows).2 true,
        List.replicate nvars true, [(gauss nvars rows).1], List.replicate cap' false] := by
  let s0 : ColState := ⟨rows.map (rowBits nvars), 0, [], [], []⟩
  have h0 : ∀ r ∈ s0.reps, r.length = nvars + 1 := by
    intro r hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    simp [rowBits]
  have hm : s0.reps.length = rows.length := by simp [s0]
  have hraw := gauss_raw s0 nvars cap cap' h0 hcap (by rw [hm]; exact hcap') (by rw [hm]; exact hcap'')
  have hcnt : (colState s0 nvars).reps.length ≤ rows.length := hm ▸ colState_count s0 nvars
  have hsteps : nvars * (colBound s0.reps.length nvars + 2) + 1 + 1 + (3 * (colState s0 nvars).reps.length + 1)
      ≤ gaussCost rows.length nvars := by
    unfold gaussCost
    rw [hm]
    omega
  have hg : gaussDrop nvars rows = ((colState s0 nvars).reps.all (fun r => !(r.headD false)), (colState s0 nvars).rank) := by
    have hp := colState_passes s0 nvars
    unfold gaussDrop
    simp only [s0] at hp
    rw [← hp]
  have hgauss := gaussDrop_eq nvars rows hrows
  rw [hg] at hgauss
  refine ⟨3 * (colState s0 nvars).reps.length, rowsTape (colState s0 nvars).reps (colState s0 nvars).stale,
    (colState s0 nvars).W, (colState s0 nvars).P, ?_⟩
  rw [← hgauss]
  exact hraw.enlarge hsteps

/-! ## Cost in a class, and twins -/

theorem gaussCost_le (m n q : ℕ) (hq : 1 ≤ q) (hm : m ≤ q) (hn : n ≤ q) : gaussCost m n ≤ 100 * q ^ 3 := by
  unfold gaussCost colBound rowCost
  have h1 : n * (m * n) ≤ q * (q * q) := Nat.mul_le_mul hn (Nat.mul_le_mul hm hn)
  have h2 : n * m ≤ q * q := Nat.mul_le_mul hn hm
  have h3 : q ≤ q * q := Nat.le_mul_of_pos_left q hq
  have h4 : q * q ≤ q * (q * q) := Nat.le_mul_of_pos_left _ hq
  have e : q ^ 3 = q * (q * q) := by ring
  rw [e]
  nlinarith

/-- **The elimination's cost in a named class**: `≤ 100 q³` for `q ≥` the row count and the variable count,
so within every class whose polynomial degree is at least 3. -/
theorem gauss_within {E : Envelope} {cls : BudgetClass} {q k psi m n : ℕ} (hq : 1 ≤ q) (hm : m ≤ q) (hn : n ≤ q)
    (hd : 3 ≤ classDeg E cls) : Within E cls 100 q k psi (gaussCost m n) :=
  Within.of_poly hq (gaussCost_le m n q hq hm hn) hd

/-- Twin: on a pilot system, the column-state semantics the machine realizes gives `gauss`. -/
theorem colState_twin :
    (((colState ⟨(system 19 4 2 2 3 5 [(1, 3), (3, 1)]).map (rowBits 5), 0, [], [], []⟩ 5).reps.all
        (fun r => !(r.headD false)),
      (colState ⟨(system 19 4 2 2 3 5 [(1, 3), (3, 1)]).map (rowBits 5), 0, [], [], []⟩ 5).rank) =
      gauss 5 (system 19 4 2 2 3 5 [(1, 3), (3, 1)])) := by decide

/-- Twin: the copy-back machine on two rows and a terminator, over a longer stale tape. -/
theorem copyRows_twin :
    (runFrom CopyRows.machine 20 ⟨CopyRows.machine.start, ![0, 0],
        ![frame [true] ++ frame [false] ++ [false, true], List.replicate 8 true]⟩).map (fun r => r.final.tapes 1) =
      some [true, true, false, true, false, false, false, true] := by decide

/-- Twin: the check clears the flag when a right-hand side is set. -/
theorem checkRhs_twin :
    (runFrom CheckRhs.machine 20 ⟨CheckRhs.machine.start, ![0, 0],
        ![frame [false] ++ frame [true] ++ [false], [true]]⟩).map (fun r => r.final.tapes 1) = some [false] ∧
    (runFrom CheckRhs.machine 20 ⟨CheckRhs.machine.start, ![0, 0],
        ![frame [false] ++ frame [false] ++ [false], [true]]⟩).map (fun r => r.final.tapes 1) = some [true] := by
  decide

end NearCubicWires.WireExponent3_5.Gauss
