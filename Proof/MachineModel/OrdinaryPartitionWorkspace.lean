import Proof.Foundations.OrdinaryStablePartition

namespace NearCubicWires.RepairOrdinary.StablePartition.Workspace
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def overlay (pre backing : List Bool) : List Bool := pre ++ backing.drop pre.length

@[simp] theorem overlay_length (pre backing : List Bool) :
    (overlay pre backing).length = max pre.length backing.length := by
  simp only [overlay, List.length_append, List.length_drop]
  omega

theorem write_boundary (pre tail : List Bool) (bit : Bool) :
    writeTapeBit (pre ++ tail) pre.length bit = pre ++ bit :: tail.drop 1 := by
  induction pre with
  | nil => cases tail <;> rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem overlay_write (pre backing : List Bool) (bit : Bool) :
    writeTapeBit (overlay pre backing) pre.length bit = overlay (pre ++ [bit]) backing := by
  rw [overlay, write_boundary]
  simp [overlay, List.append_assoc, List.drop_drop]

def outputTape (tag : Bool) : Fin 3 := if tag then 2 else 1

def backed (c : Configuration 3 9) (old : Bool → List Bool) : Configuration 3 9 where
  control := c.control
  heads := c.heads
  tapes := fun i => if i.val = 0 then c.tapes i else overlay (c.tapes i) (old (i.val == 2))

def appendHeads (c : Configuration 3 9) : Prop :=
  ∀ tag, c.heads (outputTape tag) = (c.tapes (outputTape tag)).length

def goodAction (a : Action 3 9) : Prop :=
  a.write 0 = none ∧ ∀ tag,
    a.move (outputTape tag) = if (a.write (outputTape tag)).isSome then .right else .stay

theorem rule_good (state : Fin 9) (scanned : Fin 3 → Bool) (a : Action 3 9)
    (hr : machine.rule state scanned = some a) : goodAction a := by
  fin_cases state <;> cases h : scanned 0 <;>
    simp [machine, tagState, bitState, bodyState, h] at hr
  all_goals subst a
  all_goals constructor
  all_goals first | rfl | (intro tag; cases tag <;> rfl)

theorem rule_backed (c : Configuration 3 9) (old : Bool → List Bool) :
    machine.rule (backed c old).control (backed c old).scanned =
      machine.rule c.control c.scanned := by
  simp only [machine, backed]
  rfl

theorem action_heads (c : Configuration 3 9) (a : Action 3 9)
    (hh : appendHeads c) (ha : goodAction a) : appendHeads (applyAction c a) := by
  intro tag
  have hm := ha.2 tag
  have hc := hh tag
  cases hw : a.write (outputTape tag) with
  | none =>
    simp only [hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hm
    simp [applyAction, hw, hm, HeadMove.apply, hc]
  | some bit =>
    simp only [hw, Option.isSome_some, ↓reduceIte] at hm
    simp [applyAction, hw, hm, HeadMove.apply, hc, Streaming.write_append]

theorem apply_backed (c : Configuration 3 9) (a : Action 3 9) (old : Bool → List Bool)
    (hh : appendHeads c) (ha : goodAction a) :
    applyAction (backed c old) a = backed (applyAction c a) old := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i
    · simp [applyAction, backed, ha.1]
    · have hc := hh false
      simp only [outputTape, Bool.false_eq_true, ↓reduceIte] at hc
      cases hw : a.write 1 <;>
        simp [applyAction, backed, hw, hc, Streaming.write_append, overlay_write]
    · have hc := hh true
      simp only [outputTape, ↓reduceIte] at hc
      cases hw : a.write 2 <;>
        simp [applyAction, backed, hw, hc, Streaming.write_append, overlay_write]

theorem step_backed (c d : Configuration 3 9) (old : Bool → List Bool)
    (hh : appendHeads c) (hs : step machine c = some d) :
    step machine (backed c old) = some (backed d old) ∧ appendHeads d := by
  cases hr : machine.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some a =>
    have hd : applyAction c a = d := by simpa [step, hr] using hs
    subst d
    have ha := rule_good c.control c.scanned a hr
    constructor
    · simp only [step, rule_backed, hr, Option.map_some, Option.some.injEq]
      exact apply_backed c a old hh ha
    · exact action_heads c a hh ha

theorem backed_cells (c : Configuration 3 9) (old : Bool → List Bool) :
    (backed c old).tapeCells ≤ c.tapeCells + outCells old := by
  simp [Configuration.tapeCells, backed, outCells, Fin.sum_univ_succ]
  omega

theorem run_backed (fuel : ℕ) (c : Configuration 3 9) (source : ExecutionReceipt 3 9)
    (old : Bool → List Bool) (hh : appendHeads c) (hr : runFrom machine fuel c = some source) :
    ∃ r : ExecutionReceipt 3 9, runFrom machine fuel (backed c old) = some r ∧
      r.final = backed source.final old ∧ r.steps = source.steps ∧
      r.peakTapeCells ≤ source.peakTapeCells + outCells old := by
  induction fuel generalizing c source with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · next hc =>
      cases hr
      refine ⟨⟨backed c old, 0, (backed c old).tapeCells⟩, ?_, rfl, rfl, backed_cells c old⟩
      simp [runFrom, backed, hc]
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · next hc =>
      cases hr
      refine ⟨⟨backed c old, 0, (backed c old).tapeCells⟩, ?_, rfl, rfl, backed_cells c old⟩
      simp [runFrom, backed, hc]
    · next hc =>
      cases hs : step machine c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom machine fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst source
          obtain ⟨hstep, hheads⟩ := step_backed c d old hh hs
          obtain ⟨suffix, hsuffix, hf, hsteps, hpeak⟩ := ih d tail hheads ht
          have hnot : machine.halted (backed c old).control = false := by simpa [backed] using hc
          have hj := runFrom_step machine (backed c old) (backed d old) suffix hnot hstep hsuffix
          refine ⟨⟨suffix.final, suffix.steps + 1, max (backed c old).tapeCells suffix.peakTapeCells⟩,
            hj, hf, ?_, ?_⟩
          · dsimp only
            omega
          · dsimp only
            have hb := backed_cells c old
            have hcmax := Nat.le_max_left c.tapeCells tail.peakTapeCells
            have htmax := Nat.le_max_right c.tapeCells tail.peakTapeCells
            omega

theorem finish_suffix_step (pre junk : List Bool) (out : Bool → List Bool) :
    step machine (config 0 (pre ++ false :: junk) pre.length out) =
      some (config 8 (pre ++ false :: junk) pre.length (finishedOut out [])) := by
  have hread := Streaming.read_append pre junk false
  simp [step, machine, Configuration.scanned, config, hread]
  apply configuration_ext
  · rfl
  · funext t
    fin_cases t <;>
      simp [applyAction, finishAction, HeadMove.apply, finishedOut, selected, recordsBits]
  · funext t
    fin_cases t <;>
      simp [applyAction, finishAction, finishedOut, selected, recordsBits, Streaming.write_append]

theorem records_suffix_prefix (rs : List Record) (pre junk : List Bool) (out : Bool → List Bool)
    (space : ℕ) (hspace : (pre ++ stream rs ++ junk).length + outCells out +
      (recordsBits rs).length + 2 ≤ space) :
    Prefix machine space ((recordsBits rs).length + rs.length + 1)
      (config 0 (pre ++ stream rs ++ junk) pre.length out)
      (config 8 (pre ++ stream rs ++ junk) (pre.length + (recordsBits rs).length) (finishedOut out rs)) := by
  induction rs generalizing pre out with
  | nil =>
    simp only [recordsBits, List.flatMap_nil, List.length_nil, Nat.zero_add, stream,
      List.nil_append, Nat.add_zero, List.append_assoc, List.cons_append] at hspace ⊢
    refine Prefix.step ?_ (by rfl) (finish_suffix_step pre junk out) (Prefix.refl _ ?_)
    · simp only [config_cells]
      omega
    · simpa only [config_cells, finishedOut_cells, recordsBits, List.flatMap_nil,
        List.length_nil, Nat.add_zero, Nat.add_assoc] using hspace
  | cons r rs ih =>
    let input := pre ++ stream (r :: rs) ++ junk
    have htailspace : ((pre ++ recordBits r) ++ stream rs ++ junk).length +
        outCells (extend r.1 (recordBits r) out) + (recordsBits rs).length + 2 ≤ space := by
      simp only [stream, recordsBits, List.flatMap_cons, List.length_append,
        extend_cells] at hspace ⊢
      omega
    have htail := ih (pre ++ recordBits r) (extend r.1 (recordBits r) out) htailspace
    have htail' : Prefix machine space ((recordsBits rs).length + rs.length + 1)
        (config 0 input (pre.length + (recordBits r).length) (extend r.1 (recordBits r) out))
        (config 8 input (pre.length + (recordsBits (r :: rs)).length)
          (finishedOut out (r :: rs))) := by
      simpa [input, stream, recordsBits, List.append_assoc, Nat.add_assoc] using htail
    have hrecordspace : (pre ++ recordBits r ++ (stream rs ++ junk)).length + outCells out +
        (recordBits r).length ≤ space := by
      simp only [stream, recordsBits, List.flatMap_cons, List.length_append] at hspace ⊢
      omega
    have hfirst := record_prefix r pre (stream rs ++ junk) out space hrecordspace
    have hfirst' : Prefix machine space ((recordBits r).length + 1)
        (config 0 input pre.length out)
        (config 0 input (pre.length + (recordBits r).length) (extend r.1 (recordBits r) out)) := by
      simpa [input, stream, recordsBits, List.append_assoc] using hfirst
    have hj := hfirst'.trans htail'
    simpa [input, recordsBits, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

theorem fresh_suffix_run (rs : List Record) (junk : List Bool) :
    ∃ r : ExecutionReceipt 3 9,
      run machine ((stream rs).length + rs.length)
        (fun t => if t.val = 0 then stream rs ++ junk else []) = some r ∧
      r.final = config 8 (stream rs ++ junk) (recordsBits rs).length
        (finishedOut (fun _ => []) rs) ∧
      r.steps = (stream rs).length + rs.length ∧
      r.peakTapeCells ≤ 2 * (stream rs).length + 1 + junk.length := by
  have hprefix := records_suffix_prefix rs [] junk (fun _ => [])
    (2 * (stream rs).length + 1 + junk.length) (by simp [stream, outCells]; omega)
  have hspace : (config 8 ([] ++ stream rs ++ junk) (0 + (recordsBits rs).length)
      (finishedOut (fun _ => []) rs)).tapeCells ≤ 2 * (stream rs).length + 1 + junk.length := by
    rw [config_cells, finishedOut_cells]
    simp only [outCells, List.length_nil, List.nil_append, stream, List.length_append,
      List.length_singleton]
    omega
  obtain ⟨r, hr, hf, hs, hp⟩ := hprefix.run (by rfl) hspace
  refine ⟨r, ?_, ?_, ?_, hp⟩
  · simpa [run, initialConfiguration, machine, config, outCells, stream,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
  · simpa only [List.nil_append, List.length_nil, Nat.zero_add] using hf
  · simpa [stream, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

theorem partition_workspace (rs : List Record) (junk : List Bool) (old : Bool → List Bool) :
    ∃ r : ExecutionReceipt 3 9,
      run machine ((stream rs).length + rs.length)
        (fun i => if i.val = 0 then stream rs ++ junk else old (i.val == 2)) = some r ∧
      r.final.tapes 0 = stream rs ++ junk ∧
      (∀ tag, r.final.tapes (outputTape tag) = overlay (stream (selected tag rs)) (old tag)) ∧
      (∀ tag, r.final.heads (outputTape tag) = (stream (selected tag rs)).length) ∧
      r.steps = (stream rs).length + rs.length ∧
      r.peakTapeCells ≤ 2 * (stream rs).length + 1 + junk.length + outCells old := by
  obtain ⟨source, hr, hf, hs, hp⟩ := fresh_suffix_run rs junk
  have hheads : appendHeads (initialConfiguration machine
      (fun t : Fin 3 => if t.val = 0 then stream rs ++ junk else [])) := by
    intro tag
    cases tag <;> simp [initialConfiguration, outputTape]
  obtain ⟨r, hrun, hfinal, hsteps, hpeak⟩ := run_backed
    ((stream rs).length + rs.length) _ source old hheads hr
  have hinit : backed (initialConfiguration machine
        (fun t : Fin 3 => if t.val = 0 then stream rs ++ junk else [])) old =
      initialConfiguration machine
        (fun i => if i.val = 0 then stream rs ++ junk else old (i.val == 2)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [backed, initialConfiguration, overlay]
  refine ⟨r, ?_, ?_, ?_, ?_, hsteps.trans hs, ?_⟩
  · rw [hinit] at hrun
    exact hrun
  · simp [hfinal, hf, backed, config]
  · intro tag
    cases tag <;> simp [hfinal, hf, backed, config, outputTape, finishedOut, stream]
  · intro tag
    cases tag <;> simp [hfinal, hf, backed, config, outputTape, finishedOut, stream]
  · omega

theorem selected_stream_length_le (tag : Bool) (rs : List Record) :
    (stream (selected tag rs)).length ≤ (stream rs).length := by
  have h := selected_lengths rs
  cases tag <;> simp only [stream, List.length_append, List.length_singleton] <;> omega

theorem partition_retains_capacity (rs : List Record) (junk : List Bool) (old : Bool → List Bool)
    (capacity : ℕ) (hi : (stream rs).length + junk.length ≤ capacity)
    (ho : ∀ tag, (old tag).length ≤ capacity) :
    ∃ r : ExecutionReceipt 3 9,
      run machine ((stream rs).length + rs.length)
        (fun i => if i.val = 0 then stream rs ++ junk else old (i.val == 2)) = some r ∧
      (∀ tag, r.final.tapes (outputTape tag) = overlay (stream (selected tag rs)) (old tag)) ∧
      (∀ i, (r.final.tapes i).length ≤ capacity) ∧
      r.steps ≤ 2 * (stream rs).length ∧ r.peakTapeCells ≤ 4 * capacity + 1 := by
  obtain ⟨r, hr, hf, hout, _, hs, hp⟩ := partition_workspace rs junk old
  refine ⟨r, hr, hout, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [hf] using hi
    · have he := hout false
      have hl := selected_stream_length_le false rs
      change (r.final.tapes (outputTape false)).length ≤ capacity
      rw [he, overlay_length]
      exact max_le (by omega) (ho false)
    · have he := hout true
      have hl := selected_stream_length_le true rs
      change (r.final.tapes (outputTape true)).length ≤ capacity
      rw [he, overlay_length]
      exact max_le (by omega) (ho true)
  · have hc := record_count_le rs
    simp only [stream, List.length_append, List.length_singleton] at hs ⊢
    omega
  · have h0 := ho false
    have h1 := ho true
    simp only [outCells] at hp
    omega

end NearCubicWires.RepairOrdinary.StablePartition.Workspace
