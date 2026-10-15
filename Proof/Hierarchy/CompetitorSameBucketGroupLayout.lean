import Proof.Hierarchy.CompetitorSameBucketGroupArithmeticFields
import Proof.Hierarchy.CompetitorSameBucketGroupFlush
import Proof.Hierarchy.CompetitorSameBucketGroupEntry
import Proof.Hierarchy.CompetitorSameBucketGroupCompare

/-! Fixed shared physical bank for the signed grouping scan. The public cold
source and width inputs occupy 0..3; raw dense output is appended on 4.
Temporary arithmetic, copy and comparison logs are shared only after reset. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorSameBucketGroup RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  magnitude : List Bool
  ids : List Bool
  current : List Bool
  sign : Bool
  present : Bool
  same : Bool
  positive : ℕ
  negative : ℕ

def heads (pos opos : ℕ) : Fin 24 → ℕ :=
  ![pos,0,0,0,opos,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def Store.tapes (s : Store) (cap w p m : ℕ) (source out : List Bool) : Fin 24 → List Bool :=
  let zero := CompetitorSameBucketGroupArithmetic.zeros cap
  let field := CompetitorSameBucketGroupArithmetic.field cap
  let scalar := CompetitorSameBucketGroupArithmetic.scalar cap w
  ![source,List.replicate w true,List.replicate p true,List.replicate m true,out,
    RepairSource.VerifierDecoding.CompareMachine.word p,RepairSource.VerifierDecoding.CompareMachine.word (2*m),field s.magnitude,field s.ids,field s.current,
    [s.sign],[s.present],[s.same],scalar s.positive,scalar s.negative,scalar 0,
    zero,zero,zero,zero,zero,zero,List.replicate cap true,
    CompetitorSameBucketGroupArithmetic.zeros (cap+1)]
def readSlots : Fin 6 → Fin 24 := ![0,7,8,5,6,10]
def compareSlots : Fin 4 → Fin 24 := ![9,8,12,16]
def copySlots : Fin 4 → Fin 24 := ![8,9,17,16]
def accumulator (negative : Bool) : Fin 24 := if negative then 14 else 13
def arithmeticSlots (negative : Bool) : Fin 11 → Fin 24 :=
  ![1,7,16,17,18,accumulator negative,19,20,21,22,23]
def flushSlots (negative : Bool) : Fin 5 → Fin 24 := ![accumulator negative,4,16,15,17]
noncomputable def readProgram := RecoveryFocus.machine readSlots CompetitorSameBucketGroupRead.machine
noncomputable def compareProgram := RecoveryFocus.machine compareSlots CompetitorSameBucketGroupCompare.machine
noncomputable def copyProgram := RecoveryFocus.machine copySlots copyMachine
noncomputable def flushProgram (negative : Bool) :=
  RecoveryFocus.machine (flushSlots negative) CompetitorSameBucketGroupFlush.machine

def selected (s : Store) (negative : Bool) : ℕ := if negative then s.negative else s.positive
def accumulated (s : Store) (negative : Bool) : Store :=
  if negative then {s with negative:=RadixSemantics.value s.magnitude+s.negative}
  else {s with positive:=RadixSemantics.value s.magnitude+s.positive}
def flushed (s : Store) (negative : Bool) : Store :=
  if negative then {s with negative:=0} else {s with positive:=0}
def copied (s : Store) : Store := {s with current:=s.ids}
def compared (s : Store) : Store := {s with same:=s.same && decide (s.current=s.ids)}
def loaded (s : Store) (p m : ℕ) (e : Entry) : Store :=
  {s with magnitude:=binary p e.coefficient.natAbs,ids:=e.ids m,sign:=decide (e.coefficient<0)}

def Run {states : ℕ} (p : Machine 24 states) (time cap w width m pos npos : ℕ)
    (source out nout : List Bool) (before after : Store) : Prop :=
  ∃ r,runFrom p time (RecoveryCalls.restarted p (heads pos out.length)
      (before.tapes cap w width m source out))=some r ∧
    r.final.heads=heads npos nout.length ∧
    r.final.tapes=after.tapes cap w width m source nout ∧ r.steps=time

theorem focused_existing {t u states : ℕ} (slot : Fin t → Fin u)
    (heads : Fin u → ℕ) (data : Fin u → List Bool) (c : Configuration t states)
    (hh : ∀ i,heads (slot i)=c.heads i) (ht : ∀ i,data (slot i)=c.tapes i) :
    RecoveryFocus.config slot heads data c=⟨c.control,heads,data⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simpa only [RecoveryFocus.config,hp] using (hh j).symm.trans (congrArg heads he)
  · exact install_existing slot data c.tapes ht

theorem focused_run {t u states fuel : ℕ} (slot : Fin t → Fin u) (inj : Function.Injective slot)
    (p : Machine t states) (heads : Fin u → ℕ) (data : Fin u → List Bool)
    (source : Configuration t states) (base : ExecutionReceipt t states)
    (h : runFrom p fuel source=some base)
    (hh : ∀ i,heads (slot i)=source.heads i) (ht : ∀ i,data (slot i)=source.tapes i) :
    ∃ r,runFrom (RecoveryFocus.machine slot p) fuel ⟨source.control,heads,data⟩=some r ∧
      r.final=RecoveryFocus.config slot heads data base.final ∧ r.steps=base.steps := by
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config slot inj p heads data fuel source base h
  rw [focused_existing slot heads data source hh ht] at hr
  exact ⟨r,hr,hf,hs⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
