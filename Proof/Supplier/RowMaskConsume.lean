import Proof.Supplier.RowMaskPositionParts

/-! Consume the selected raw incidence row in the retained nine-tape bank.
The same machine accepts the allocated zero-padded index template. -/
namespace NearCubicWires.RepairOrdinary.RowMaskConsume
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (N : ℕ) : Fin 9→ℕ := ![0,N+2,0,0,0,0,0,0,0]
def bank {s : ℕ} (q : Fin s) (N w : ℕ) (x : Data) := ZeroPadding.config (capacities N) (cfg q N w x)
def localCaps (N : ℕ) : Fin 5→ℕ := ![0,N+2,0,0,N+2]
def slots : Fin 5→Fin 9 := ![0,1,2,3,4]
theorem injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots RowMaskLoop.machine

theorem pick (i : Fin 9) : RecoveryFocus.pick slots i=
    if i=0 then some 0 else if i=1 then some 1 else if i=2 then some 2 else if i=3 then some 3
      else if i=4 then some 4 else none := by
  fin_cases i
  all_goals
    first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2
    | exact RecoveryFocus.pick_slot slots injective 3
    | exact RecoveryFocus.pick_slot slots injective 4
    | decide

theorem pad_driver (N : ℕ) : ZeroPadding.pad (N+2) (CompareMachine.word N)=UnaryTemplate.tape N := by
  simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem local_heads (phase : Fin 5) (source : List Bool) (pos j count : ℕ) (out : List Bool) (N : ℕ) :
    (RowMaskLoop.cfg phase source pos j count out N 1).heads=![pos,1,out.length,count+1,1] := by
  funext i; fin_cases i <;> rfl

theorem local_tapes (phase : Fin 5) (source : List Bool) (pos j count : ℕ) (out : List Bool) (N : ℕ) :
    (RowMaskLoop.cfg phase source pos j count out N 1).tapes=
      ![source,UnaryTemplate.tape j,out,CompareMachine.word count,CompareMachine.word N] := by
  funext i; fin_cases i <;> rfl

def consumed (N : ℕ) (bits : List Bool) (x : Data) : Data :=
  {x with pos:=x.pos+N,index:=N,count:=x.count+bits.count true,out:=x.out++RowMaskLoop.word 0 bits}

theorem consume_run (N w : ℕ) (pre bits tail : List Bool) (x : Data)
    (hx : x.source=pre++bits++tail) (hp : x.pos=pre.length) (hi : x.index=0) (hn : bits.length=N) :
    ∃ r,runFrom machine (N*(4*N+21)+3) (bank machine.start N w x)=some r ∧
      r.final.heads=(bank machine.start N w (consumed N bits x)).heads ∧
      r.final.tapes=(bank machine.start N w (consumed N bits x)).tapes ∧
      r.steps≤N*(4*N+21)+3 := by
  obtain ⟨base,hbase,bf,bs⟩ := RowMaskLoop.mask_run pre bits tail x.out x.count
  rw [hn] at hbase bs
  obtain ⟨padded,hpad,pf,ps,_⟩ := ZeroPadding.run_config RowMaskLoop.machine (localCaps N) _ _ base hbase
  let ambient := bank machine.start N w x
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots injective RowMaskLoop.machine
    ambient.heads ambient.tapes _ _ padded hpad
  have he : RecoveryFocus.config slots ambient.heads ambient.tapes
      (ZeroPadding.config (localCaps N) (RowMaskLoop.cfg 0 (pre++bits++tail) pre.length 0 x.count x.out N 1))=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      change heads x (slots i)=_
      rw [show (ZeroPadding.config (localCaps N) (RowMaskLoop.cfg 0 (pre++bits++tail) pre.length 0 x.count x.out N 1)).heads=
        (RowMaskLoop.cfg 0 (pre++bits++tail) pre.length 0 x.count x.out N 1).heads by rfl,local_heads]
      fin_cases i <;> simp [heads,slots,hp]
    · intro i
      change ZeroPadding.pad (capacities N (slots i)) (tapes N w x (slots i))=
        ZeroPadding.pad (localCaps N i) ((RowMaskLoop.cfg 0 (pre++bits++tail) pre.length 0 x.count x.out N 1).tapes i)
      rw [local_tapes]
      fin_cases i <;> simp [capacities,localCaps,slots,tapes,hx,hi,pad_driver]
  rw [he] at hr
  refine ⟨r,hr,?_,?_,rs.le.trans (ps.le.trans bs)⟩
  · rw [rf,pf,bf]
    change (RecoveryFocus.config slots ambient.heads ambient.tapes
      (ZeroPadding.config (localCaps N) (RowMaskLoop.cfg 3 (pre++bits++tail) (pre.length+bits.length)
        bits.length (x.count+bits.count true) (x.out++RowMaskLoop.word 0 bits) bits.length 1))).heads=_
    simp only [RecoveryFocus.config,ZeroPadding.config,local_heads]
    funext i; fin_cases i <;> simp [pick,ambient,bank,cfg,heads,consumed,hp,hn,ZeroPadding.config]
  · rw [rf,pf,bf]
    change install slots ambient.tapes (fun i=>ZeroPadding.pad (localCaps N i)
      ((RowMaskLoop.cfg 3 (pre++bits++tail) (pre.length+bits.length) bits.length
        (x.count+bits.count true) (x.out++RowMaskLoop.word 0 bits) bits.length 1).tapes i))=_
    rw [local_tapes,hn]
    funext i; fin_cases i <;> simp [install,pick,ambient,bank,cfg,tapes,consumed,capacities,localCaps,
      ZeroPadding.config,hx,pad_driver]

end NearCubicWires.RepairOrdinary.RowMaskConsume
