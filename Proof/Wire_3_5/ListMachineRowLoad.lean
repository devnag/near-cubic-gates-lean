import Proof.Wire_3_5.ListMachinePrintGen

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun)

theorem overlay_nil (w : List Bool) : overlay w [] = w := by simp [overlay]

/-! ## A masked run from any blank log -/

theorem maskBlank {t s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (sel : Fin t → Bool) (hstart : ∀ i, sel i = true → hin i = 0) (k : ℕ) :
    ∃ m, Step (MaskedReset.machine p sel) (2 * n + 2) (Fin.addCases hin (fun _ : Fin 1 => 0))
      (Fin.addCases tin (fun _ : Fin 1 => List.replicate k false))
      (Fin.addCases (fun i => if sel i then 0 else hout i) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hhead : ∀ i, sel i = true → r.final.heads i ≤ r.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run p n _ r hr).1 i
    simpa only [hstart i hi, zero_add] using h
  obtain ⟨base, hb, hf, hbs, _⟩ := MaskedReset.reset_run p sel n _ r hr hhead
  obtain ⟨res, hrun, hfinal, hsteps, _⟩ := ZeroPadding.run_config (MaskedReset.machine p sel)
    (Rewind.Workspace.capacities t k) _ _ base hb
  have hentry : ZeroPadding.config (Rewind.Workspace.capacities t k)
      (Rewind.recording (⟨p.start, hin, tin⟩ : Configuration t s) 0) =
      (⟨(MaskedReset.machine p sel).start, Fin.addCases hin (fun _ : Fin 1 => 0),
        Fin.addCases tin (fun _ : Fin 1 => List.replicate k false)⟩ : Configuration (t+1) (s+2)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
      · simp only [ZeroPadding.config, Rewind.recording, Rewind.config, Fin.addCases_left,
          Rewind.Workspace.capacities, ZeroPadding.pad_zero]
      · have hj : j = 0 := Fin.eq_zero j
        subst hj
        simp only [ZeroPadding.config, Rewind.recording, Rewind.config, Fin.addCases_right,
          Rewind.Workspace.capacities, List.replicate_zero, ZeroPadding.pad, List.nil_append,
          List.length_nil, Nat.sub_zero]
  rw [hentry] at hrun
  have hfuel : 2 * r.steps + 2 ≤ 2 * n + 2 := by omega
  have hmore := runFrom_moreFuel (MaskedReset.machine p sel) (2 * r.steps + 2) (2 * n + 2 - (2 * r.steps + 2)) _
    res hrun
  rw [Nat.add_sub_of_le hfuel] at hmore
  refine ⟨max k r.steps, res, hmore, ?_, ?_, by omega⟩
  · rw [hfinal, hf, SelectiveReset.padded_finished]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, hh]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]
  · rw [hfinal, hf, SelectiveReset.padded_finished]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, ht]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]

/-! ## Unframe: the content of one framed field -/

namespace Unframe
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)

/-- Tape 0 the record (read), tape 1 the output. State `0` reads a pair's marker or the terminator, `1` copies the
pair's bit, `2` halts one cell past the terminator. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 1 none none .right .stay else act 2 none none .right .stay)
    else if q.val = 1 then some (act 0 none (some (sc 0)) .right .right)
    else none

theorem pair_steps (A : List Bool) (h : ℕ) (o B : List Bool) (b : Bool) (hr : readTapeBit A h = true)
    (hb : readTapeBit A (h + 1) = b) :
    Timed machine 2 (cfg 0 A (overlay o B) h o.length) (cfg 0 A (overlay (o ++ [b]) B) (h + 1 + 1) (o ++ [b]).length) := by
  have s1 := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg machine 0 1 A (overlay o B) h o.length none none
    .right .stay (by simp [machine, hr])
  have s2 := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg machine 1 0 A (overlay o B) (h + 1) o.length none (some b)
    .right .right (by simp [machine, hb])
  simp only [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply, overlay_write] at s1 s2
  have e : (o ++ [b]).length = o.length + 1 := by simp
  rw [← e] at s2
  exact (Timed.single (p := machine) rfl s1).trans (Timed.single (p := machine) rfl s2)

theorem end_step (A : List Bool) (h : ℕ) (o B : List Bool) (hr : readTapeBit A h = false) :
    Timed machine 1 (cfg 0 A (overlay o B) h o.length) (cfg 2 A (overlay o B) (h + 1) o.length) := by
  have s1 := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg machine 0 2 A (overlay o B) h o.length none none
    .right .stay (by simp [machine, hr])
  simp only [NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply] at s1
  exact Timed.single (p := machine) rfl s1

theorem timed (tail B : List Bool) : ∀ (w pre o : List Bool),
    Timed machine (2 * w.length + 1)
      (cfg 0 (pre ++ frame w ++ tail) (overlay o B) pre.length o.length)
      (cfg 2 (pre ++ frame w ++ tail) (overlay (o ++ w) B) (pre.length + (2 * w.length + 1)) (o ++ w).length) := by
  intro w
  induction w with
  | nil =>
    intro pre o
    have hr : readTapeBit (pre ++ frame [] ++ tail) pre.length = false := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre tail false
    simpa using end_step _ pre.length o B hr
  | cons b w ih =>
    intro pre o
    have hr : readTapeBit (pre ++ frame (b :: w) ++ tail) pre.length = true := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre (b :: frame w ++ tail) true
    have hb : readTapeBit (pre ++ frame (b :: w) ++ tail) (pre.length + 1) = b := by
      simpa [frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ tail) b
    have t1 := pair_steps _ pre.length o B b hr hb
    have e0 : pre ++ frame (b :: w) ++ tail = (pre ++ [true, b]) ++ frame w ++ tail := by
      simp [frame, List.append_assoc]
    have t2 := ih (pre ++ [true, b]) (o ++ [b])
    rw [← e0] at t2
    have e1 : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    rw [e1, show o ++ [b] ++ w = o ++ b :: w by simp,
      show pre.length + 1 + 1 + (2 * w.length + 1) = pre.length + (2 * (b :: w).length + 1) by simp; omega] at t2
    have := t1.trans t2
    rwa [show 2 + (2 * w.length + 1) = 2 * (b :: w).length + 1 by simp; omega] at this

/-- **Unframe**: the content `w` of the framed field at the record cursor is written at the output cursor; the record
cursor stops one cell past the field. -/
theorem run (pre w tail o B : List Bool) :
    Step machine (2 * w.length + 1) ![pre.length, o.length] ![pre ++ frame w ++ tail, overlay o B]
      ![pre.length + (2 * w.length + 1), (o ++ w).length] ![pre ++ frame w ++ tail, overlay (o ++ w) B] := by
  obtain ⟨r, hr, hf, _⟩ := (timed tail B w pre o).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end Unframe

/-! ## Loading a list of fields -/

/-- One field: the framed word at the record cursor (tape `src`) is copied into tape `tg`. -/
noncomputable def field1 {u : ℕ} (src tg : Fin u) : Machine u 3 := RecoveryFocus.machine ![src, tg] Unframe.machine

theorem pair_inj {u : ℕ} {a b : Fin u} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem dockH_pair {u : ℕ} {a b : Fin u} (h : a ≠ b) (H : Fin u → ℕ) (v : Fin 2 → ℕ) :
    dockH ![a, b] H v = fun i => if i = a then v 0 else if i = b then v 1 else H i := by
  funext i
  by_cases ha : i = a
  · subst ha; simpa using dockH_slot ![i, b] (pair_inj h) H v 0
  · by_cases hb : i = b
    · subst hb; simpa [ha] using dockH_slot ![a, i] (pair_inj h) H v 1
    · rw [dockH_other _ _ _ _ (by
        intro j; fin_cases j
        · simpa using fun e : a = i => ha e.symm
        · simpa using fun e : b = i => hb e.symm)]
      simp [ha, hb]

theorem install_pair {u : ℕ} {a b : Fin u} (h : a ≠ b) (A : Fin u → List Bool) (v : Fin 2 → List Bool) :
    install ![a, b] A v = fun i => if i = a then v 0 else if i = b then v 1 else A i := by
  funext i
  by_cases ha : i = a
  · subst ha; simpa using install_slot ![i, b] (pair_inj h) A v 0
  · by_cases hb : i = b
    · subst hb; simpa [ha] using install_slot ![a, i] (pair_inj h) A v 1
    · rw [install_other _ _ _ _ (by
        intro j; fin_cases j
        · simpa using fun e : a = i => ha e.symm
        · simpa using fun e : b = i => hb e.symm)]
      simp [ha, hb]

/-- **One field loaded**: the record cursor passes the field, the (empty) target receives its content. -/
theorem field1_step {u : ℕ} (src tg : Fin u) (hne : src ≠ tg) (pre w tail : List Bool) (H : Fin u → ℕ)
    (A : Fin u → List Bool) (hHs : H src = pre.length) (hAs : A src = pre ++ frame w ++ tail) (hHt : H tg = 0)
    (hAt : A tg = []) :
    Step (field1 src tg) (2 * w.length + 1) H A
      (fun i => if i = src then pre.length + (2 * w.length + 1) else if i = tg then w.length else H i)
      (fun i => if i = tg then w else A i) := by
  have h := dockRun (Unframe.run pre w tail [] []) ![src, tg] (pair_inj hne) H A
    (by intro j; fin_cases j <;> simp [hHs, hHt])
    (by intro j; fin_cases j <;> simp [hAs, hAt, overlay_nil])
  rw [dockH_pair hne, install_pair hne] at h
  refine h.congr ?_ ?_
  · funext i; simp
  · funext i
    by_cases hs : i = src
    · subst hs; simp [hne, hAs]
    · simp [hs, overlay_nil]

/-- The state count of a load. -/
def loadS {α : Type} : List α → ℕ
  | [] => 1
  | _ :: l => 3 + loadS l

/-- Load the fields at the record cursor into the target tapes `l`, in order. -/
noncomputable def loadL {u : ℕ} (src : Fin u) : (l : List (Fin u)) → Machine u (loadS l)
  | [] => NearCubicWires.WireExponent3_5.Block.idle u
  | tg :: l => Composition.machine (field1 src tg) (loadL src l)

/-- The cost of a load. -/
def loadCost : List (List Bool) → ℕ
  | [] => 0
  | w :: ws => 2 * w.length + 1 + 1 + loadCost ws

/-- The record word of a list of fields. -/
def fieldsWord (ws : List (List Bool)) : List Bool := ws.flatMap frame

theorem fieldsWord_cons (w : List Bool) (ws : List (List Bool)) : fieldsWord (w :: ws) = frame w ++ fieldsWord ws := by
  simp [fieldsWord]

/-- **The load**: the fields `F i` (`i ∈ l`, in order) at the record cursor are copied into the empty target tapes;
the record cursor passes them; every target head stops at the end of its field. -/
theorem loadL_run {u : ℕ} (src : Fin u) (F : Fin u → List Bool) : ∀ (l : List (Fin u)), l.Nodup → src ∉ l →
    ∀ (pre tail : List Bool) (H : Fin u → ℕ) (A : Fin u → List Bool), H src = pre.length →
      A src = pre ++ fieldsWord (l.map F) ++ tail → (∀ i ∈ l, H i = 0) → (∀ i ∈ l, A i = []) →
      Step (loadL src l) (loadCost (l.map F)) H A
        (fun i => if i = src then pre.length + (fieldsWord (l.map F)).length else if i ∈ l then (F i).length else H i)
        (fun i => if i ∈ l then F i else A i) := by
  intro l
  induction l with
  | nil =>
    intro _ _ pre tail H A hHs _ _ _
    have h := Print.idle_step H A
    refine h.congr ?_ ?_
    · funext i; by_cases hi : i = src
      · subst hi; simp [hHs, fieldsWord]
      · simp [hi]
    · funext i; simp
  | cons tg l ih =>
    intro hnd hsrc pre tail H A hHs hAs hH hA
    have hne : src ≠ tg := fun h => hsrc (h ▸ List.mem_cons_self)
    have hsrc' : src ∉ l := fun h => hsrc (List.mem_cons_of_mem _ h)
    have htg : tg ∉ l := (List.nodup_cons.mp hnd).1
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    rw [List.map_cons, fieldsWord_cons, List.append_assoc, List.append_assoc] at hAs
    have h1 := field1_step src tg hne pre (F tg) (fieldsWord (l.map F) ++ tail) H A hHs (by rw [hAs]; simp)
      (hH tg List.mem_cons_self) (hA tg List.mem_cons_self)
    have h2 := ih hnd' hsrc' (pre ++ frame (F tg)) tail
      (fun i => if i = src then pre.length + (2 * (F tg).length + 1) else if i = tg then (F tg).length else H i)
      (fun i => if i = tg then F tg else A i)
      (by simp [frame_length])
      (by simp [hne, hAs, List.append_assoc])
      (by intro i hi; have h1 : i ≠ src := fun e => hsrc' (e ▸ hi); have h2 : i ≠ tg := fun e => htg (e ▸ hi)
          simp [h1, h2, hH i (List.mem_cons_of_mem _ hi)])
      (by intro i hi; have h2 : i ≠ tg := fun e => htg (e ▸ hi)
          simp [h2, hA i (List.mem_cons_of_mem _ hi)])
    have h := h1.seq h2
    refine (h.enlarge (by simp [loadCost])).congr ?_ ?_
    · funext i
      by_cases hs : i = src
      · subst hs; simp [fieldsWord_cons, frame_length]; omega
      · by_cases ht : i = tg
        · subst ht; simp [hs, htg]
        · simp [hs, ht]
    · funext i
      by_cases ht : i = tg
      · subst ht; simp [htg]
      · simp [ht]

end NearCubicWires.WireExponent3_5.ListMachine.Row
