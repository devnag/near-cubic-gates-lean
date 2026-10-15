import Proof.Hierarchy.HierarchyProjectionPrefix

/-! A constant finite transducer forms the literal ordinary input of the
selected PCP constructor from its two already framed fields. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.SourceFrame
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def active (phase : Bool) : Fin 3 := if phase then 1 else 0
def state (phase : Bool) (j : Fin 5) : Fin 12 := ⟨(if phase then 5 else 0)+j.val,by split <;> omega⟩
def cfg (phase : Bool) (q : Fin 12) (source : List Bool) (pos : ℕ)
    (other : List Bool) (otherPos : ℕ) (out : List Bool) : Configuration 3 12 :=
  ⟨q,fun i => if i.val=2 then out.length else if i=active phase then pos else otherPos,
    fun i => if i.val=2 then out else if i=active phase then source else other⟩
@[simp] theorem cfg_control (phase : Bool) (q : Fin 12) (source : List Bool) (pos : ℕ)
    (other : List Bool) (otherPos : ℕ) (out : List Bool) :
    (cfg phase q source pos other otherPos out).control=q := rfl

def action (phase : Bool) (next : Fin 12) (b : Bool) (move : Bool) : Action 3 12 :=
  ⟨next,fun i => if i.val=2 then some b else none,
    fun i => if i.val=2 ∨ (i=active phase ∧ move=true) then .right else .stay⟩
def raw : Machine 3 12 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==11
  rule := fun q bits =>
    if q.val=0 then some (action false (if bits 0 then 1 else 4) true false)
    else if q.val=1 then some (action false 2 true true)
    else if q.val=2 then some (action false 3 true false)
    else if q.val=3 then some (action false 0 (bits 0) true)
    else if q.val=4 then some (action false 5 false true)
    else if q.val=5 then some (action true (if bits 1 then 6 else 9) true false)
    else if q.val=6 then some (action true 7 true true)
    else if q.val=7 then some (action true 8 true false)
    else if q.val=8 then some (action true 5 (bits 1) true)
    else if q.val=9 then some (action true 10 false true)
    else if q.val=10 then some ⟨11,![none,none,some false],fun _ => .stay⟩
    else none

theorem active_not_halted (phase : Bool) (j : Fin 5) : raw.halted (state phase j)=false := by
  cases phase <;> fin_cases j <;> rfl

theorem apply_action (phase : Bool) (q next : Fin 12) (source : List Bool) (pos : ℕ)
    (other : List Bool) (otherPos : ℕ) (out : List Bool) (b move : Bool) :
    applyAction (cfg phase q source pos other otherPos out) (action phase next b move)=
      cfg phase next source (pos+move.toNat) other otherPos (out++[b]) := by
  apply configuration_ext
  · rfl
  · funext i; cases phase <;> cases move <;> fin_cases i <;>
      simp [applyAction,cfg,action,active,HeadMove.apply]
  · funext i; cases phase <;> fin_cases i <;>
      simp [applyAction,cfg,action,active,Streaming.write_append]

theorem mark_step (phase : Bool) (pre tail other out : List Bool) (otherPos : ℕ) :
    step raw (cfg phase (state phase 0) (pre++true::tail) pre.length other otherPos out)=
      some (cfg phase (state phase 1) (pre++true::tail) pre.length other otherPos (out++[true])) := by
  have h := Streaming.read_append pre tail true
  have hr : raw.rule (state phase 0)
      (cfg phase (state phase 0) (pre++true::tail) pre.length other otherPos out).scanned=
      some (action phase (state phase 1) true false) := by
    cases phase <;> simp [raw,state,cfg,active,Configuration.scanned,h]
  simp only [step,cfg_control,hr,Option.map_some,Option.some.injEq]
  simpa using apply_action phase (state phase 0) (state phase 1) (pre++true::tail) pre.length other otherPos out true false

theorem fixed_step (phase : Bool) (pre tail other out : List Bool) (otherPos : ℕ) :
    step raw (cfg phase (state phase 1) (pre++true::tail) pre.length other otherPos out)=
      some (cfg phase (state phase 2) (pre++true::tail) (pre.length+1) other otherPos (out++[true])) := by
  have hr : raw.rule (state phase 1)
      (cfg phase (state phase 1) (pre++true::tail) pre.length other otherPos out).scanned=
      some (action phase (state phase 2) true true) := by cases phase <;> rfl
  simp only [step,cfg_control,hr,Option.map_some,Option.some.injEq]
  simpa using apply_action phase (state phase 1) (state phase 2) (pre++true::tail) pre.length other otherPos out true true

theorem bit_mark_step (phase : Bool) (source other out : List Bool) (pos otherPos : ℕ) :
    step raw (cfg phase (state phase 2) source pos other otherPos out)=
      some (cfg phase (state phase 3) source pos other otherPos (out++[true])) := by
  have hr : raw.rule (state phase 2) (cfg phase (state phase 2) source pos other otherPos out).scanned=
      some (action phase (state phase 3) true false) := by cases phase <;> rfl
  simp only [step,cfg_control,hr,Option.map_some,Option.some.injEq]
  simpa using apply_action phase (state phase 2) (state phase 3) source pos other otherPos out true false

theorem bit_step (phase b : Bool) (pre tail other out : List Bool) (otherPos : ℕ) :
    step raw (cfg phase (state phase 3) (pre++b::tail) pre.length other otherPos out)=
      some (cfg phase (state phase 0) (pre++b::tail) (pre.length+1) other otherPos (out++[b])) := by
  have h := Streaming.read_append pre tail b
  have hr : raw.rule (state phase 3)
      (cfg phase (state phase 3) (pre++b::tail) pre.length other otherPos out).scanned=
      some (action phase (state phase 0) b true) := by
    cases phase <;> simp [raw,state,cfg,active,Configuration.scanned,h]
  simp only [step,cfg_control,hr,Option.map_some,Option.some.injEq]
  simpa using apply_action phase (state phase 3) (state phase 0) (pre++b::tail) pre.length other otherPos out b true

theorem delimiter_step (phase : Bool) (pre other out : List Bool) (otherPos : ℕ) :
    step raw (cfg phase (state phase 0) (pre++[false]) pre.length other otherPos out)=
      some (cfg phase (state phase 4) (pre++[false]) pre.length other otherPos (out++[true])) := by
  have h := Streaming.read_append pre [] false
  have hr : raw.rule (state phase 0)
      (cfg phase (state phase 0) (pre++[false]) pre.length other otherPos out).scanned=
      some (action phase (state phase 4) true false) := by
    cases phase <;> simp [raw,state,cfg,active,Configuration.scanned,h]
  simp only [step,cfg_control,hr,Option.map_some,Option.some.injEq]
  simpa using apply_action phase (state phase 0) (state phase 4) (pre++[false]) pre.length other otherPos out true false

theorem finish_step (phase : Bool) (pre other out : List Bool) (otherPos : ℕ) :
    step raw (cfg phase (state phase 4) (pre++[false]) pre.length other otherPos out)=
      some (cfg phase (if phase then 10 else 5) (pre++[false]) (pre.length+1) other otherPos (out++[false])) := by
  have hr : raw.rule (state phase 4)
      (cfg phase (state phase 4) (pre++[false]) pre.length other otherPos out).scanned=
      some (action phase (if phase then 10 else 5) false true) := by cases phase <;> rfl
  simp only [step,cfg_control,hr,Option.map_some,Option.some.injEq]
  simpa using apply_action phase (state phase 4) (if phase then 10 else 5) (pre++[false]) pre.length other otherPos out false true

theorem field (phase : Bool) (pre bits other out : List Bool) (otherPos : ℕ) :
    Timed raw (4*bits.length+2)
      (cfg phase (state phase 0) (pre++frame bits) pre.length other otherPos out)
      (cfg phase (if phase then 10 else 5) (pre++frame bits) (pre.length+(frame bits).length)
        other otherPos (out++Streaming.marks (frame bits))) := by
  induction bits generalizing pre out with
  | nil =>
    have ht := (Timed.single (active_not_halted phase 0)
      (delimiter_step phase pre other out otherPos)).trans
      (Timed.single (active_not_halted phase 4)
        (finish_step phase pre other (out++[true]) otherPos))
    simpa [RepairOrdinary.frame,Streaming.marks,List.append_assoc] using ht
  | cons b bs ih =>
    have ht := ih (pre++[true,b]) (out++[true,true,true,b])
    have h1 := mark_step phase pre (b::frame bs) other out otherPos
    have h2 := fixed_step phase pre (b::frame bs) other (out++[true]) otherPos
    have h3 := bit_mark_step phase (pre++true::b::frame bs) other (out++[true,true]) (pre.length+1) otherPos
    have h4 := bit_step phase b (pre++[true]) (frame bs) other (out++[true,true,true]) otherPos
    simp only [List.append_assoc,List.singleton_append,List.length_append,List.length_cons,List.length_nil,Nat.add_assoc] at h1 h2 h3 h4 ht
    have hrun := (Timed.single (active_not_halted phase 0) h1).trans
      ((Timed.single (active_not_halted phase 1) h2).trans
      ((Timed.single (active_not_halted phase 2) h3).trans
      ((Timed.single (active_not_halted phase 3) h4).trans ht)))
    have htime : 1+(1+(1+(1+(4*bs.length+2))))=4*(b::bs).length+2 := by simp; omega
    rw [htime] at hrun
    simpa [RepairOrdinary.frame,Streaming.marks,List.append_assoc,Nat.add_assoc,
      show 1+(1+(2*bs.length+1))=2*bs.length+3 by omega] using hrun

def final (left right : List Bool) : Configuration 3 12 :=
  ⟨11,![(frame left).length,(frame right).length,2*(frame left++frame right).length],
    ![frame left,frame right,frame (frame left++frame right)]⟩

theorem raw_run (left right : List Bool) : ∃ r,
    run raw (4*(left.length+right.length)+5) ![frame left,frame right,[]]=some r ∧
      r.final=final left right ∧ r.steps=4*(left.length+right.length)+5 := by
  have h1 := field false [] left (frame right) [] 0
  have h2 := field true [] right (frame left) (Streaming.marks (frame left)) (frame left).length
  simp only [List.nil_append,List.length_nil,Nat.zero_add,Bool.false_eq_true,if_false,if_true] at h1 h2
  have he : cfg false 5 (frame left) (frame left).length (frame right) 0 (Streaming.marks (frame left))=
      cfg true (state true 0) (frame right) 0 (frame left) (frame left).length (Streaming.marks (frame left)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at h1
  have hf : step raw (cfg true 10 (frame right) (frame right).length (frame left) (frame left).length
      (Streaming.marks (frame left)++Streaming.marks (frame right)))=some (final left right) := by
    simp [step,raw,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,final,active,HeadMove.apply]; omega
    · funext i; fin_cases i
      · rfl
      · rfl
      · change writeTapeBit (Streaming.marks (frame left)++Streaming.marks (frame right))
          (2*(2*left.length+1)+2*(2*right.length+1)) false=_
        have hpos : 2*(2*left.length+1)+2*(2*right.length+1)=
            (Streaming.marks (frame left)++Streaming.marks (frame right)).length := by simp
        rw [hpos,Streaming.write_append,←Streaming.marks_append]
        change Streaming.marks (frame left++frame right)++[false]=frame (frame left++frame right)
        simpa only [List.append_nil,RepairOrdinary.frame] using
          (Streaming.frame_append (frame left++frame right) []).symm
  have ht := h1.trans (h2.trans (Timed.single (by rfl : raw.halted (10 : Fin 12)=false) hf))
  have htime : (4*left.length+2)+(4*right.length+2+1)=4*(left.length+right.length)+5 := by omega
  rw [htime] at ht
  obtain ⟨r,hr,hfinal,hs⟩ := ht.run (by rfl)
  have hi : cfg false (state false 0) (frame left) 0 (frame right) 0 []=
      initialConfiguration raw ![frame left,frame right,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hr
  exact ⟨r,hr,hfinal,hs⟩

def machine := Rewind.machine raw
def input (left right : List Bool) : Fin 4 → List Bool := ![frame left,frame right,[],[]]
def output (left right : List Bool) : Fin 4 → List Bool :=
  ![frame left,frame right,frame (frame left++frame right),List.replicate (4*(left.length+right.length)+5) false]

theorem ready (left right : List Bool) :
    ClockJoin.ReadyRun machine (8*(left.length+right.length)+12) (input left right) (output left right) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run left right
  obtain ⟨r,hr,ht,hcount,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![frame left,frame right,[]] (fun _ : Fin 1 => []))=input left right := by
    funext i; fin_cases i <;> rfl
  change run machine (2*base.steps+2) (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
    ![frame left,frame right,[]] (fun _ : Fin 1 => []))=some r at hr
  rw [hi] at hr
  have he : 2*base.steps+2=8*(left.length+right.length)+12 := by omega
  rw [he] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i; fin_cases i
  · simpa [output,hf,final] using ht 0
  · simpa [output,hf,final] using ht 1
  · simpa [output,hf,final] using ht 2
  · simpa [output,hs] using hcount

end NearCubicWires.RepairSource.ProjectionNormalization.SourceFrame
