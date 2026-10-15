import Proof.Hierarchy.CompetitorSameBucketPairGuard
import Proof.Hierarchy.CompetitorSameBucketKeys

/-! Actual signed-payload and tagged-ID contribution appending. The three
framed fields and their physical width templates are retained; only the
global contribution cursor advances. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketKeyAppend
open LocalBitMultitape SignedSortKey Streaming RankBody RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (payload : List Bool) (k right left cap : ℕ) (out : List Bool) : Configuration 8 s :=
  ⟨q,fun i => if i=6 then out.length else 0,
    ![frame payload,frame (List.replicate payload.length false),frame (binary k right),frame (binary k 0),
      frame (binary k left),frame (binary k 0),out,List.replicate cap false]⟩
def mark : Machine 8 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => some ⟨if q=0 then 1 else 2,fun i => if i=6 then some true else none,
    fun i => if i=6 then .right else .stay⟩

theorem mark_step (q : Fin 2) (payload : List Bool) (k right left cap : ℕ) (out : List Bool) :
    step mark (cfg (q.castAdd 1) payload k right left cap out)=
      some (cfg ⟨q.val+1,by omega⟩ payload k right left cap (out++[true])) := by
  simp only [step,mark,Option.map_some,Option.some.injEq]
  apply configuration_ext
  · fin_cases q <;> rfl
  · funext i
    fin_cases i <;> simp [applyAction,cfg,HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction,cfg,write_append]

theorem mark_run (payload : List Bool) (k right left cap : ℕ) (out : List Bool) :
    ∃ r,runFrom mark 2 (cfg 0 payload k right left cap out)=some r ∧
      r.final=cfg 2 payload k right left cap (out++[true,true]) ∧ r.steps=2 := by
  have first := Timed.single (by rfl) (mark_step 0 payload k right left cap out)
  have last := Timed.single (by rfl) (mark_step 1 payload k right left cap (out++[true]))
  have path := first.trans last
  simpa [cfg,List.append_assoc] using path.run (by rfl)

def payloadSlots : Fin 4 → Fin 8 := ![0,1,6,7]
def idSlots : Fin 6 → Fin 8 := ![2,3,4,5,6,7]
theorem payload_injective : Function.Injective payloadSlots := by decide
theorem id_injective : Function.Injective idSlots := by decide
noncomputable def payloadProgram := RecoveryFocus.machine payloadSlots KeyPrefix.machine
noncomputable def idProgram := RecoveryFocus.machine idSlots KeyPair.machine

theorem payload_pick (i : Fin 8) : RecoveryFocus.pick payloadSlots i=
    (![some 0,some 1,none,none,none,none,some 2,some 3] : Fin 8 → Option (Fin 4)) i := by
  classical
  fin_cases i
  · exact RecoveryFocus.pick_slot payloadSlots payload_injective 0
  · exact RecoveryFocus.pick_slot payloadSlots payload_injective 1
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot payloadSlots payload_injective 2
  · exact RecoveryFocus.pick_slot payloadSlots payload_injective 3

theorem id_pick (i : Fin 8) : RecoveryFocus.pick idSlots i=
    (![none,none,some 0,some 1,some 2,some 3,some 4,some 5] : Fin 8 → Option (Fin 6)) i := by
  classical
  fin_cases i
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot idSlots id_injective 0
  · exact RecoveryFocus.pick_slot idSlots id_injective 1
  · exact RecoveryFocus.pick_slot idSlots id_injective 2
  · exact RecoveryFocus.pick_slot idSlots id_injective 3
  · exact RecoveryFocus.pick_slot idSlots id_injective 4
  · exact RecoveryFocus.pick_slot idSlots id_injective 5

theorem payload_run (payload : List Bool) (k right left cap : ℕ) (out : List Bool) (hc : 2*payload.length≤cap) :
    ∃ r,runFrom payloadProgram (4*payload.length+2) (cfg 0 payload k right left cap out)=some r ∧
      r.final=cfg 3 payload k right left cap (out++marks payload) ∧ r.steps=4*payload.length+2 := by
  obtain ⟨base,hb,hf,hs,_⟩ := KeyPrefix.field_run payload [false] (List.replicate payload.length false) out cap (by simp) hc
  rw [marks_frame] at hb hf
  let entry := cfg (0 : Fin 4) payload k right left cap out
  have hi : RecoveryFocus.config payloadSlots entry.heads entry.tapes
      (KeyPrefix.ready (0 : Fin 4) (frame payload) (frame (List.replicate payload.length false)) out cap)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨actual,hr,hfinal,hsteps⟩ := RecoveryFocus.run_config payloadSlots payload_injective KeyPrefix.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  refine ⟨actual,hr,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i
    simp only [RecoveryFocus.config,payload_pick]
    fin_cases i <;> simp [entry,cfg,KeyPrefix.ready]
  · funext i
    simp only [RecoveryFocus.config,payload_pick]
    fin_cases i <;> simp [entry,cfg,KeyPrefix.ready]

theorem id_run (payload : List Bool) (k right left cap : ℕ) (out : List Bool) (hc : 2*k≤cap) :
    ∃ r,runFrom idProgram (8*k+7) (cfg 0 payload k right left cap out)=some r ∧
      r.final=cfg 9 payload k right left cap (out++frame (binary k right++binary k left)) ∧ r.steps≤8*k+7 := by
  obtain ⟨base,hb,hf,hs,_⟩ := KeyPair.pair_run (binary k right) [false] (binary k 0)
    (binary k left) [false] (binary k 0) out cap (by simp) (by simp) (by simpa using hc) (by simpa using hc)
  rw [marks_frame,marks_frame] at hb hf
  simp only [binary_length] at hb hs
  have he : 4*(k+k)+7=8*k+7 := by omega
  rw [he] at hb hs
  let entry := cfg (0 : Fin 10) payload k right left cap out
  have hi : RecoveryFocus.config idSlots entry.heads entry.tapes
      (KeyPair.config (0 : Fin 10) (frame (binary k right)) (frame (binary k 0))
        (frame (binary k left)) (frame (binary k 0)) out cap)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨actual,hr,hfinal,hsteps⟩ := RecoveryFocus.run_config idSlots id_injective KeyPair.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  refine ⟨actual,hr,?_,hsteps.trans_le hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i
    simp only [RecoveryFocus.config,id_pick]
    fin_cases i <;> simp [entry,cfg,KeyPair.config]
  · funext i
    simp only [RecoveryFocus.config,id_pick]
    fin_cases i <;> simp [entry,cfg,KeyPair.config]

noncomputable def tail := Composition.machine payloadProgram idProgram
noncomputable def machine := Composition.machine mark tail

theorem append_run (payload : List Bool) (k right left cap : ℕ) (out : List Bool)
    (hp : 2*payload.length≤cap) (hk : 2*k≤cap) :
    ∃ r,runFrom machine (4*payload.length+8*k+13) (cfg machine.start payload k right left cap out)=some r ∧
      r.final.heads=(cfg machine.start payload k right left cap
        (out++frame (true::(payload++binary k right++binary k left)))).heads ∧
      r.final.tapes=(cfg machine.start payload k right left cap
        (out++frame (true::(payload++binary k right++binary k left)))).tapes ∧
      r.steps≤4*payload.length+8*k+13 := by
  obtain ⟨r0,h0,hf0,hs0⟩ := mark_run payload k right left cap out
  obtain ⟨r1,h1,hf1,hs1⟩ := payload_run payload k right left cap (out++[true,true]) hp
  obtain ⟨r2,h2,hf2,hs2⟩ := id_run payload k right left cap ((out++[true,true])++marks payload) hk
  have mid12 : Composition.restart r1.final idProgram.start=cfg 0 payload k right left cap ((out++[true,true])++marks payload) := by rw [hf1]; rfl
  rw [←mid12] at h2
  have ht := Composition.run_join payloadProgram idProgram _ _ _ r1 r2 h1 h2
  let rt := Composition.joinedReceipt r1 r2
  have mid0 : Composition.restart r0.final tail.start=
      Composition.leftConfig 10 (cfg (0 : Fin 4) payload k right left cap (out++[true,true])) := by rw [hf0]; rfl
  rw [←mid0] at ht
  have hall := Composition.run_join mark tail 2 ((4*payload.length+2)+1+(8*k+7)) _ r0 rt h0 ht
  have time : 2+1+((4*payload.length+2)+1+(8*k+7))=4*payload.length+8*k+13 := by omega
  rw [time] at hall
  have hout : ((out++[true,true])++marks payload)++frame (binary k right++binary k left)=
      out++frame (true::(payload++binary k right++binary k left)) := by
    simp only [List.append_assoc,frame_append,frame]
    rfl
  refine ⟨Composition.joinedReceipt r0 rt,hall,?_,?_,?_⟩
  · change r2.final.heads=_
    rw [hf2,hout]
    rfl
  · change r2.final.tapes=_
    rw [hf2,hout]
    rfl
  · change r0.steps+1+(r1.steps+1+r2.steps)≤_
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketKeyAppend
