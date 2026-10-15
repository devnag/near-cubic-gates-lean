import Proof.Hierarchy.CompetitorSameBucketGroupTapeCases

/-! Literal read, ID comparison, ID copy and flush calls on the shared
streaming grouping bank. Every selected inverse tape map is checked once. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem read_injective : Function.Injective readSlots := by decide

def readPicks : Fin 24 → Option (Fin 6) := ![some 0,none,none,none,none,some 3,some 4,some 1,some 2,none,some 5,none,none,none,none,none,none,none,none,none,none,none,none,none]

theorem read_pick (i : Fin 24) : RecoveryFocus.pick readSlots i=readPicks i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot readSlots read_injective 0
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot readSlots read_injective 3
  · exact RecoveryFocus.pick_slot readSlots read_injective 4
  · exact RecoveryFocus.pick_slot readSlots read_injective 1
  · exact RecoveryFocus.pick_slot readSlots read_injective 2
  · decide
  · exact RecoveryFocus.pick_slot readSlots read_injective 5
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem compare_injective : Function.Injective compareSlots := by decide

def comparePicks : Fin 24 → Option (Fin 4) := ![none,none,none,none,none,none,none,none,some 1,some 0,none,none,some 2,none,none,none,some 3,none,none,none,none,none,none,none]

theorem compare_pick (i : Fin 24) : RecoveryFocus.pick compareSlots i=comparePicks i := by
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 1
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 0
  · decide
  · decide
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 2
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 3
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem copy_injective : Function.Injective copySlots := by decide

def copyPicks : Fin 24 → Option (Fin 4) := ![none,none,none,none,none,none,none,none,some 0,some 1,none,none,none,none,none,none,some 3,some 2,none,none,none,none,none,none]

theorem copy_pick (i : Fin 24) : RecoveryFocus.pick copySlots i=copyPicks i := by
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot copySlots copy_injective 0
  · exact RecoveryFocus.pick_slot copySlots copy_injective 1
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot copySlots copy_injective 3
  · exact RecoveryFocus.pick_slot copySlots copy_injective 2
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem read_tapes (s : Store) (cap w p m : ℕ) (source out : List Bool) (e : Entry) :
    install readSlots (s.tapes cap w p m source out)
      (CompetitorSameBucketGroupRead.data source (frame (binary p e.coefficient.natAbs))
        (frame (e.ids m)) [decide (e.coefficient<0)] p (2*m) cap)=
      (loaded s p m e).tapes cap w p m source out := by
  funext i
  fin_cases i <;> simp only [install,read_pick,readPicks] <;>
    simp only [Store.tapes_at] <;> rfl

theorem compare_tapes (s : Store) (cap w p m : ℕ) (source out : List Bool) :
    install compareSlots (s.tapes cap w p m source out)
      (CompetitorSameBucketGroupCompare.output cap s.current s.ids s.same)=
      (compared s).tapes cap w p m source out := by
  funext i
  fin_cases i <;> simp only [install,compare_pick,comparePicks] <;>
    simp only [Store.tapes_at] <;> rfl

theorem copy_tapes (s : Store) (cap w p m : ℕ) (source out : List Bool) :
    install copySlots (s.tapes cap w p m source out)
      (CompetitorSameBucketGroupArithmetic.copyOutput cap s.ids)=
      (copied s).tapes cap w p m source out := by
  funext i
  fin_cases i <;> simp only [install,copy_pick,copyPicks] <;>
    simp only [Store.tapes_at] <;> rfl

theorem read_run (s : Store) (cap w p m : ℕ) (pre suffix out : List Bool) (e : Entry)
    (hm : s.magnitude.length≤p) (hi : s.ids.length≤2*m) :
    Run readProgram (4*p+8*m+12) cap w p m pre.length (pre.length+2*p+4*m+5)
      (pre++StablePartition.recordBits (e.record p m)++suffix) out out s (loaded s p m e) := by
  obtain ⟨base,hb,hbh,hbt,hbs⟩ := CompetitorSameBucketGroupRead.entry_run pre suffix
    (frame s.magnitude) (frame s.ids) [s.sign] p m cap e
    (by simp; omega) (by simp; omega) (by simp)
  obtain ⟨r,hr,hf,hs⟩ := focused_run readSlots read_injective _
    (heads pre.length out.length) (s.tapes cap w p m
      (pre++StablePartition.recordBits (e.record p m)++suffix) out) _ base hb
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨r,hr,?_,?_,hs.trans hbs⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp only [RecoveryFocus.config,read_pick,readPicks,hbh] <;> rfl
  · rw [hf]
    change install readSlots _ base.final.tapes=_
    rw [hbt]
    exact read_tapes s cap w p m _ out e

theorem compare_run (s : Store) (cap w p m pos : ℕ) (source out : List Bool)
    (hl : s.current.length=2*m) (hr : s.ids.length=2*m) (hc : 4*m+1≤cap) :
    Run compareProgram (8*m+4) cap w p m pos pos source out out s (compared s) := by
  have ready := CompetitorSameBucketGroupCompare.compare_ready cap (2*m) s.current s.ids s.same hl hr (by omega)
  have he : 4*(2*m)+4=8*m+4 := by omega
  rw [he] at ready
  obtain ⟨r,h,hh,ht,hs⟩ := HierarchyBinary.focused_run compareSlots compare_injective _ _ _ ready
    (heads pos out.length) (s.tapes cap w p m source out)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨r,h,hh,?_,hs⟩
  exact ht.trans (compare_tapes s cap w p m source out)

theorem copy_run (s : Store) (cap w p m pos : ℕ) (source out : List Bool)
    (hi : s.ids.length=2*m) (hcur : s.current.length≤2*m) (hc : 8*m+3≤cap) :
    Run copyProgram (16*m+8) cap w p m pos pos source out out s (copied s) := by
  have ready := CompetitorSameBucketGroupArithmetic.field_copy_ready cap s.ids (frame s.current)
    (by simp; omega) (by omega)
  rw [hi] at ready
  have he : 8*(2*m)+8=16*m+8 := by omega
  rw [he] at ready
  obtain ⟨r,h,hh,ht,hs⟩ := HierarchyBinary.focused_run copySlots copy_injective _ _ _ ready
    (heads pos out.length) (s.tapes cap w p m source out)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨r,h,hh,?_,hs⟩
  exact ht.trans (copy_tapes s cap w p m source out)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
