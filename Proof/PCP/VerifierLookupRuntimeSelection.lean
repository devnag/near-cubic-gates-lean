import Proof.PCP.VerifierLookupRuntimeFields

/-! Physical ordinal selection is wired into the same lookup store. The
actual source cursor returned by the linear walk is used by the field readers. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selectionSlots (table : Bool) : Fin 7→Fin 21 := if table then tableSelectSlots else flagsSelectSlots
def queryBacking (d : Store) (table : Bool) : List Bool := if table then d.query else d.flagQuery
def counterBacking (d : Store) (table : Bool) : List Bool := if table then d.counter else d.flagCounter
def selectionSource (d : Store) (query counter : List Bool) (pos : ℕ) (flag : Bool) : LookupSelect.Store :=
  ⟨frame d.code,pos,query,counter,flag,d.cap,CompareMachine.word d.j,CapMachine.counter d.code.length d.t⟩
def selectionOut (d : Store) (table : Bool) (pos : ℕ) (counter : List Bool) (flag : Bool) : Store :=
  if table then {d with codePos:=pos,counter:=frame counter,flag:=flag}
  else {d with codePos:=pos,flagCounter:=frame counter,flag:=flag}

theorem selection_place {n : ℕ} (table : Bool) (q : Fin n) (d : Store) (query counter : List Bool)
    (pos : ℕ) (flag : Bool) (hq : queryBacking d table=frame query) :
    RecoveryFocus.config (selectionSlots table) (cfg q d).heads (cfg q d).tapes
      (LookupSelect.cfg q (selectionSource d query counter pos flag))=
      cfg q (selectionOut d table pos counter flag) := by
  cases table
  all_goals apply TransitionEvent.focused_eq _ (by decide) (cfg q d)
  all_goals first
    | rfl
    | (intro z; fin_cases z <;> first | rfl | exact hq.symm)
    | (intro z h; fin_cases z <;> first | exact False.elim (h 0 rfl) | exact False.elim (h 2 rfl) | exact False.elim (h 3 rfl) | rfl)

theorem selection_lift {n : ℕ} (p : Machine 7 n) (table : Bool) (d : Store) (query : List Bool)
    (stride fuel : ℕ) (base : ExecutionReceipt 7 n)
    (hq : queryBacking d table=frame query)
    (hz : counterBacking d table=frame (binary query.length 0))
    (hb : runFrom p fuel (LookupSelect.cfg p.start
      (selectionSource d query (binary query.length 0) d.codePos d.flag))=some base)
    (hbf : base.final=LookupSelect.cfg base.final.control
      (LookupSelect.completed (selectionSource d query (binary query.length 0) d.codePos d.flag) (value query) stride)) :
    ∃ r,runFrom (RecoveryFocus.machine (selectionSlots table) p) fuel (cfg p.start d)=some r ∧
      r.final=cfg r.final.control
        (selectionOut d table (d.codePos+value query*stride) (binary query.length (value query)) true) ∧
      r.steps≤fuel := by
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config (selectionSlots table) (by cases table <;> decide) p
    (cfg p.start d).heads (cfg p.start d).tapes _ _ base hb
  have hi := selection_place table p.start d query (binary query.length 0) d.codePos d.flag hq
  have he : selectionOut d table d.codePos (binary query.length 0) d.flag=d := by
    cases table
    · change ({d with flagCounter:=frame (binary query.length 0)} : Store)=d
      rw [show frame (binary query.length 0)=d.flagCounter from hz.symm]
    · change ({d with counter:=frame (binary query.length 0)} : Store)=d
      rw [show frame (binary query.length 0)=d.counter from hz.symm]
  rw [he] at hi
  rw [hi] at hr
  have ho : RecoveryFocus.config (selectionSlots table) (cfg p.start d).heads (cfg p.start d).tapes base.final=
      cfg base.final.control
        (selectionOut d table (d.codePos+value query*stride) (binary query.length (value query)) true) := by
    rw [hbf]
    exact selection_place table base.final.control d query _ _ true hq
  have hsteps := runFrom_steps_le p fuel _ base hb
  exact ⟨r,hr,by rw [hrf,ho]; rfl,hrs.trans_le hsteps⟩

theorem flags_select_run (d : Store) (query : List Bool)
    (hq : d.flagQuery=frame query) (hz : d.flagCounter=frame (binary query.length 0))
    (hf : d.flag=false) (hc : 2*query.length+1≤d.cap) :
    ∃ r,runFrom flagsSelectProgram ((value query+1)*(8*query.length+14)) (cfg flagsSelectProgram.start d)=some r ∧
      r.final=cfg r.final.control
        (selectionOut d false (d.codePos+value query*4) (binary query.length (value query)) true) ∧
      r.steps≤(value query+1)*(8*query.length+14) := by
  obtain ⟨base,hb,hbf,_⟩ := LookupPosition.flags_run
    (selectionSource d query (binary query.length 0) d.codePos d.flag) rfl hf hc
  exact selection_lift LookupPosition.flagsMachine false d query 4 _ base hq hz hb hbf

theorem table_select_run (d : Store) (query : List Bool)
    (hq : d.query=frame query) (hz : d.counter=frame (binary query.length 0))
    (hf : d.flag=false) (hc : 2*query.length+1≤d.cap) :
    ∃ r,runFrom tableSelectProgram ((value query+1)*(8*query.length+3*d.j+12*d.t+27))
      (cfg tableSelectProgram.start d)=some r ∧
      r.final=cfg r.final.control
        (selectionOut d true (d.codePos+value query*(2*(1+d.j+4*d.t))) (binary query.length (value query)) true) ∧
      r.steps≤(value query+1)*(8*query.length+3*d.j+12*d.t+27) := by
  obtain ⟨base,hb,hbf,_⟩ := LookupPosition.table_run
    (selectionSource d query (binary query.length 0) d.codePos d.flag) d.j d.t d.code.length rfl rfl rfl hf hc
  exact selection_lift LookupPosition.tableMachine true d query (2*(1+d.j+4*d.t)) _ base hq hz hb hbf

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
