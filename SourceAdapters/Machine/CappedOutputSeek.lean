import SourceAdapters.Machine.CappedOutputWord

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: locate the physical output end, including final false writes, in linear time. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open OutputFrame (written)
set_option autoImplicit false

def action (q : Fin 20) (sm om mm cm : HeadMove) (bit : Option Bool) : Action 5 20 where
  nextControl := q
  write := fun i => if i.val=1 then bit else none
  move := fun i => if i.val=0 then sm else if i.val=1 then om else if i.val=2 then sm else if i.val=3 then mm else cm

def initialAction : Action 5 20 :=
  { action 1 .stay .right .stay .stay none with
    write := fun i => if i.val=2 then some true else none }

/-- Source, fresh output, protected origin, physical-write marker, and unary cap. -/
def machine : Machine 5 20 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==19
  rule := fun q scan =>
    if q.val=0 then some initialAction
    else if q.val=1 then some (action 2 .stay .right .stay .stay none)
    else if q.val=2 then
      if scan 4 then some (action 3 .right .right .right .right none)
      else some (action 6 .stay .stay .stay .stay none)
    else if q.val=3 then some (action 4 .stay .right .stay .stay none)
    else if q.val=4 then some (action 5 .stay .right .stay .stay none)
    else if q.val=5 then some (action 2 .stay .right .stay .stay none)
    else if q.val=6 then
      if scan 3 then some (action 10 .stay .stay .stay .stay none)
      else if scan 2 then some (action 14 .stay .stay .stay .stay none)
      else some (action 7 .left .left .left .left none)
    else if q.val=7 then some (action 8 .stay .left .stay .stay none)
    else if q.val=8 then some (action 9 .stay .left .stay .stay none)
    else if q.val=9 then some (action 6 .stay .left .stay .stay none)
    else if q.val=10 then some (action 11 .right .right .stay .stay none)
    else if q.val=11 then some (action 12 .stay .right .stay .stay none)
    else if q.val=12 then some (action 13 .stay .right .stay .stay none)
    else if q.val=13 then some (action 14 .stay .right .stay .stay none)
    else if q.val=14 then some (action 15 .stay .right .stay .stay (some true))
    else if q.val=15 then some (action 16 .stay .right .stay .stay (some false))
    else if q.val=16 then some (action 17 .stay .left .stay .stay (some false))
    else if q.val=17 then some (action 18 .stay .left .stay .stay none)
    else if q.val=18 then some (action 19 .left .left .stay .stay none)
    else none

def config (q : Fin 20) (source output marker : List Bool)
    (cap pos oh mh ch : ℕ) : Configuration 5 20 where
  control := q
  heads := fun i => if i.val=0 then pos else if i.val=1 then oh else if i.val=2 then pos else if i.val=3 then mh else ch
  tapes := fun i => if i.val=0 then source else if i.val=1 then output else if i.val=2 then [true] else if i.val=3 then marker else List.replicate cap true

theorem apply_action (q next : Fin 20) (source output marker : List Bool)
    (cap pos oh mh ch : ℕ) (sm om mm cm : HeadMove) (bit : Option Bool) :
    applyAction (config q source output marker cap pos oh mh ch) (action next sm om mm cm bit) =
      config next source (written output oh bit) marker cap
        (sm.apply pos) (om.apply oh) (mm.apply mh) (cm.apply ch) := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, config, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, config, written]
    cases bit <;> rfl

theorem step_known (q next : Fin 20) (source output marker : List Bool)
    (cap pos oh mh ch : ℕ) (sm om mm cm : HeadMove) (bit : Option Bool)
    (hr : machine.rule q (config q source output marker cap pos oh mh ch).scanned = some (action next sm om mm cm bit)) :
    step machine (config q source output marker cap pos oh mh ch) =
      some (config next source (written output oh bit) marker cap
        (sm.apply pos) (om.apply oh) (mm.apply mh) (cm.apply ch)) := by
  rw [step, show (config q source output marker cap pos oh mh ch).control=q from rfl, hr]
  simp only [Option.map_some, apply_action]

def walk (q : Fin 20) (source marker : List Bool) (cap pos : ℕ) : Configuration 5 20 :=
  config q source [] marker cap pos (4*pos+2) pos pos

end NearCubicGates.Adapters.Machine.Capped.OutputSeek
