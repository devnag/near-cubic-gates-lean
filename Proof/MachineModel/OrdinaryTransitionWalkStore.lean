import Proof.PCP.VerifierLookupClaimGuard

/-! Common physical store for binary-counted transition execution. Lookup
and array emission share the exact tag and witness tapes; event output retains
its append cursor. The two counters m/i are framed binary words, not unary. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  lookup : LookupRuntime.Store
  tagPos : ℕ
  head : HeadUpdate.Store
  serial : ℕ
  tape : ℕ
  out : List Bool
  read : Bool
  after : Bool
  array : List Bool
  arrayOut : List Bool
  w : ℕ
  cap : ℕ
  C : ℕ
  m : ℕ
  index : ℕ
  countFlag : Bool

def eventStore (d : Store) : TransitionTape.Store :=
  ⟨d.lookup.tags,d.tagPos,d.lookup.scans,d.lookup.scanPos,d.head,d.serial,d.tape,d.out,d.read,d.after⟩

def cfg {s : ℕ} (q : Fin s) (d : Store) : Configuration 42 s :=
  ⟨q,fun i=>if h:i.val<21 then (LookupRuntime.usedCfg q d.lookup d.tagPos).heads ⟨i.val,h⟩
      else if i.val=33 then d.out.length else 0,
    fun i=>if h:i.val<21 then (LookupRuntime.cfg q d.lookup).tapes ⟨i.val,h⟩ else
      match i.val with
      | 21=>[d.read]
      | 22=>[d.after]
      | 23=>[HeadUpdate.low d.head.move]
      | 24=>[HeadUpdate.high d.head.move]
      | 25=>frame (binary d.w d.head.head)
      | 26=>frame (binary d.w 1)
      | 27=>d.head.difference
      | 28=>[d.head.flag]
      | 29=>List.replicate d.cap false
      | 30=>List.replicate d.cap false
      | 31=>binary (2*d.w) d.serial
      | 32=>List.replicate (2*d.w) true
      | 33=>d.out
      | 34=>frame (binary d.w d.tape)
      | 35=>d.array
      | 36=>d.arrayOut
      | 37=>List.replicate (d.C+1) false
      | 38=>List.replicate d.C true
      | 39=>frame (binary d.w d.m)
      | 40=>frame (binary d.w d.index)
      | 41=>[d.countFlag]
      | _=>[]⟩

def lookupSlots (i : Fin 21) : Fin 42 := i.castAdd 21
def arraySlots : Fin 20→Fin 42 := ![12,21,22,23,24,7,25,26,27,28,29,30,31,32,33,34,35,36,37,38]

theorem lookup_injective : Function.Injective lookupSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 42=>z.val) h)

theorem lookup_place {s : ℕ} (q : Fin s) (d : Store) (e : LookupRuntime.Store) (pos : ℕ) :
    RecoveryFocus.config lookupSlots (cfg q d).heads (cfg q d).tapes
      (LookupRuntime.usedCfg q e pos)=cfg q {d with lookup:=e,tagPos:=pos} := by
  apply TransitionEvent.focused_eq lookupSlots lookup_injective (cfg q d)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i h
    have hi : ¬i.val<21 := by
      intro hi
      exact h ⟨i.val,hi⟩ (Fin.ext rfl)
    simp only [cfg,hi,↓reduceDIte]
  · intro i h
    have hi : ¬i.val<21 := by
      intro hi
      exact h ⟨i.val,hi⟩ (Fin.ext rfl)
    simp only [cfg,hi,↓reduceDIte]

def withArray (d : Store) (e : TransitionTape.Store) (source out : List Bool) : Store :=
  {d with
    lookup:={d.lookup with tags:=e.source,scans:=e.scans,scanPos:=e.cursor},
    tagPos:=e.pos,head:=e.head,serial:=e.serial,tape:=e.tape,out:=e.out,read:=e.read,after:=e.after,
    array:=source,arrayOut:=out}

theorem array_place {s : ℕ} (q : Fin s) (d : Store) (e : TransitionTape.Store) (source out : List Bool) :
    RecoveryFocus.config arraySlots (cfg q d).heads (cfg q d).tapes
      (TransitionArrayReuse.cfg q e d.w d.cap d.C source out)=cfg q (withArray d e source out) := by
  apply TransitionEvent.focused_eq arraySlots (by decide) (cfg q d)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | exact False.elim (h 5 rfl) | exact False.elim (h 14 rfl) | rfl
  · intro i h; fin_cases i <;> first
      | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl) | exact False.elim (h 2 rfl)
      | exact False.elim (h 3 rfl) | exact False.elim (h 4 rfl) | exact False.elim (h 5 rfl)
      | exact False.elim (h 6 rfl) | exact False.elim (h 7 rfl) | exact False.elim (h 8 rfl)
      | exact False.elim (h 9 rfl) | exact False.elim (h 12 rfl) | exact False.elim (h 14 rfl)
      | exact False.elim (h 15 rfl) | exact False.elim (h 16 rfl) | exact False.elim (h 17 rfl) | rfl

end NearCubicWires.RepairOrdinary.TransitionWalk
