import SourceAdapters.Machine.CappedRequestReady

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: physical backward writing of the exact double-framed output. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputFrame
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def blocks (word : List Bool) : List Bool := word.flatMap (fun b => [true,true,true,b])

@[simp] theorem blocks_length (word : List Bool) : (blocks word).length = 4*word.length := by
  induction word with
  | nil => rfl
  | cons b bs ih => simp [blocks] at *; omega

@[simp] theorem blocks_append (a b : List Bool) : blocks (a++b) = blocks a ++ blocks b := by
  simp [blocks]

theorem result_frame (status : Bool) (word : List Bool) :
    frame (status :: frame word) = [true,status] ++ blocks word ++ [true,false,false] := by
  have h : ∀ w : List Bool, frame (frame w) = blocks w ++ [true,false,false] := by
    intro w
    induction w with
    | nil => rfl
    | cons b bs ih => simpa [frame, blocks] using congrArg (fun t => true::true::true::b::t) ih
  simpa [frame] using congrArg (fun t => true::status::t) (h word)

theorem write_before_suffix (n : ℕ) (tail : List Bool) (bit : Bool) :
    writeTapeBit (List.replicate (n+1) false ++ tail) n bit = List.replicate n false ++ bit::tail := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, writeTapeBit] using congrArg (List.cons false) ih

theorem write_blank (n : ℕ) (bit : Bool) :
    writeTapeBit [] n bit = List.replicate n false ++ [bit] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [writeTapeBit, List.replicate_succ] using congrArg (List.cons false) ih

def action (q : Fin 8) (sourceMove outputMove : HeadMove) (bit : Option Bool) : Action 4 8 where
  nextControl := q
  write := fun i => if i.val=1 then bit else none
  move := fun i => if i.val=0 then sourceMove else if i.val=1 then outputMove else if i.val=2 then sourceMove else .stay

/-- Tapes: immutable source, final output, protected origin marker, write marker. -/
def machine : Machine 4 8 where
  descriptionBits := 0
  start := 6
  halted := fun q => q.val==7
  rule := fun q scan =>
    if q.val=0 then some (action 1 .stay .left (some (scan 0)))
    else if q.val=1 then some (action 2 .stay .left (some true))
    else if q.val=2 then some (action 3 .stay .left (some true))
    else if q.val=3 then
      if scan 2 then some (action 4 .stay .left (some true))
      else some (action 0 .left .left (some true))
    else if q.val=4 then some (action 5 .stay .left (some true))
    else if q.val=5 then some (action 7 .stay .stay (some true))
    else if q.val=6 then
      if scan 3 then some (action 0 .stay .stay none)
      else some (action 4 .stay .stay none)
    else none

def config (q : Fin 8) (source output marker : List Bool) (pos oh mh : ℕ) : Configuration 4 8 where
  control := q
  heads := fun i => if i.val=0 then pos else if i.val=1 then oh else if i.val=2 then pos else mh
  tapes := fun i => if i.val=0 then source else if i.val=1 then output else if i.val=2 then [true] else marker

def written (output : List Bool) (pos : ℕ) (bit : Option Bool) : List Bool :=
  match bit with | none => output | some b => writeTapeBit output pos b

theorem apply_action (q next : Fin 8) (source output marker : List Bool)
    (pos oh mh : ℕ) (sm om : HeadMove) (bit : Option Bool) :
    applyAction (config q source output marker pos oh mh) (action next sm om bit) =
      config next source (written output oh bit)
        marker (sm.apply pos) (om.apply oh) mh := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, config, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, config, written]
    cases bit <;> rfl

theorem step_known (q next : Fin 8) (source output marker : List Bool)
    (pos oh mh : ℕ) (sm om : HeadMove) (bit : Option Bool)
    (hr : machine.rule q (config q source output marker pos oh mh).scanned = some (action next sm om bit)) :
    step machine (config q source output marker pos oh mh) =
      some (config next source (written output oh bit)
        marker (sm.apply pos) (om.apply oh) mh) := by
  rw [step, show (config q source output marker pos oh mh).control=q from rfl, hr]
  simp only [Option.map_some, apply_action]

theorem header_run (source tail marker : List Bool) (mh : ℕ) :
    ∃ r, runFrom machine 2 (config 4 source (false::false::tail) marker 0 1 mh) = some r ∧
      r.final = config 7 source (true::true::tail) marker 0 0 mh ∧ r.steps=2 := by
  have h1 := step_known 4 5 source (false::false::tail) marker 0 1 mh .stay .left (some true) (by rfl)
  have h2 := step_known 5 7 source (false::true::tail) marker 0 0 mh .stay .stay (some true) (by rfl)
  simp only [written, writeTapeBit, HeadMove.apply] at h1 h2
  let final := config 7 source (true::true::tail) marker 0 0 mh
  let r : ExecutionReceipt 4 8 := ⟨final,0,final.tapeCells⟩
  have h0 : runFrom machine 0 final = some r := by rfl
  have hr2 := runFrom_step machine _ _ r (by rfl) h2 h0
  have hr1 := runFrom_step machine _ _ _ (by rfl) h1 hr2
  exact ⟨_, hr1, rfl, rfl⟩

end NearCubicGates.Adapters.Machine.Capped.OutputFrame
