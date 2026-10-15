import Proof.Hierarchy.CompetitorSameBucketGroupTapeCases

/-! A completed cell is emitted as its exact fixed-width P/N pair and both
accumulators are physically reset before the next cell. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flush_injective (negative : Bool) : Function.Injective (flushSlots negative) := by
  cases negative <;> decide

def flushPicks (negative : Bool) : Fin 24 → Option (Fin 5) :=
  ![none,none,none,none,some 1,none,none,none,none,none,none,none,none,
    if negative then none else some 0,if negative then some 0 else none,some 3,some 2,some 4,
    none,none,none,none,none,none]

theorem flush_pick (negative : Bool) (i : Fin 24) :
    RecoveryFocus.pick (flushSlots negative) i=flushPicks negative i := by
  cases negative
  · fin_cases i
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (flushSlots false) (flush_injective _) 1
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (flushSlots false) (flush_injective _) 0
    · decide
    · exact RecoveryFocus.pick_slot (flushSlots false) (flush_injective _) 3
    · exact RecoveryFocus.pick_slot (flushSlots false) (flush_injective _) 2
    · exact RecoveryFocus.pick_slot (flushSlots false) (flush_injective _) 4
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · fin_cases i
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (flushSlots true) (flush_injective _) 1
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (flushSlots true) (flush_injective _) 0
    · exact RecoveryFocus.pick_slot (flushSlots true) (flush_injective _) 3
    · exact RecoveryFocus.pick_slot (flushSlots true) (flush_injective _) 2
    · exact RecoveryFocus.pick_slot (flushSlots true) (flush_injective _) 4
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

theorem flush_tapes (negative : Bool) (s : Store) (cap w p m : ℕ) (source out : List Bool) :
    install (flushSlots negative) (s.tapes cap w p m source out)
      (CompetitorSameBucketGroupFlush.data cap w 0 (out++binary w (selected s negative)))=
      (flushed s negative).tapes cap w p m source (out++binary w (selected s negative)) := by
  funext i
  cases negative <;> fin_cases i <;> simp only [install,flush_pick,flushPicks] <;>
    simp only [Store.tapes_at] <;> rfl

theorem flush_run (negative : Bool) (s : Store) (cap w p m pos : ℕ) (source out : List Bool)
    (hc : 4*w+3≤cap) :
    Run (flushProgram negative) (12*w+12) cap w p m pos pos source out
      (out++binary w (selected s negative)) s (flushed s negative) := by
  obtain ⟨base,hb,hbh,hbt,hbs⟩ := CompetitorSameBucketGroupFlush.flush_run cap w (selected s negative) out hc
  obtain ⟨r,hr,hf,hs⟩ := focused_run (flushSlots negative) (flush_injective negative) _
    (heads pos out.length) (s.tapes cap w p m source out) _ base hb
    (by intro i; cases negative <;> fin_cases i <;> rfl)
    (by intro i; cases negative <;> fin_cases i <;> rfl)
  refine ⟨r,hr,?_,?_,hs.trans hbs⟩
  · rw [hf]
    funext i
    cases negative <;> fin_cases i <;>
      simp only [RecoveryFocus.config,flush_pick,flushPicks,hbh] <;> rfl
  · rw [hf]
    change install (flushSlots negative) _ base.final.tapes=_
    rw [hbt]
    exact flush_tapes negative s cap w p m source out

theorem join_run {a b : ℕ} (first : Machine 24 a) (last : Machine 24 b)
    (tfirst tlast cap w p m pos middle finalpos : ℕ) (source out middleout finalout : List Bool)
    (s smid sfinal : Store)
    (hfirst : Run first tfirst cap w p m pos middle source out middleout s smid)
    (hlast : Run last tlast cap w p m middle finalpos source middleout finalout smid sfinal) :
    Run (Composition.machine first last) (tfirst+1+tlast) cap w p m pos finalpos
      source out finalout s sfinal := by
  obtain ⟨r,hr,hrh,hrt,hrs⟩ := hfirst
  obtain ⟨q,hq,hqh,hqt,hqs⟩ := hlast
  have hd : Composition.restart r.final last.start=
      RecoveryCalls.restarted last (heads middle middleout.length) (smid.tapes cap w p m source middleout) := by
    apply configuration_ext
    · rfl
    · exact hrh
    · exact hrt
  have hq' : runFrom last tlast (Composition.restart r.final last.start)=some q := by rw [hd]; exact hq
  have hj := Composition.run_join first last tfirst tlast _ r q hr hq'
  refine ⟨Composition.joinedReceipt r q,hj,hqh,hqt,?_⟩
  change r.steps+1+q.steps=_
  rw [hrs,hqs]

noncomputable def emitProgram := Composition.machine (flushProgram false) (flushProgram true)
def emitted (s : Store) : Store := {s with positive:=0,negative:=0}
def pair (w : ℕ) (s : Store) := binary w s.positive++binary w s.negative

theorem emit_run (s : Store) (cap w p m pos : ℕ) (source out : List Bool)
    (hc : 4*w+3≤cap) :
    Run emitProgram (24*w+25) cap w p m pos pos source out (out++pair w s) s (emitted s) := by
  have h := join_run (flushProgram false) (flushProgram true) (12*w+12) (12*w+12)
    cap w p m pos pos pos source out (out++binary w s.positive)
    ((out++binary w s.positive)++binary w s.negative) s (flushed s false) (emitted s)
    (flush_run false s cap w p m pos source out hc)
    (flush_run true (flushed s false) cap w p m pos source (out++binary w s.positive) hc)
  have he : (12*w+12)+1+(12*w+12)=24*w+25 := by omega
  simpa only [he,emitProgram,pair,List.append_assoc] using h

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
