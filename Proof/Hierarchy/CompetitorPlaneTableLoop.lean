import Proof.Hierarchy.CompetitorPlaneTableStep

/-! The actual complete stream of signed plane pairs. A physical pair-count
driver controls repetition; every iteration loads its next two packets,
updates both retained accumulator banks and preserves the packet cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneStream CompetitorPlanePacketPass
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream {n : ℕ} (b : ℕ) (planes : List (Plane n)) := planes.flatMap (Plane.word b)
def evaluate {n : ℕ} : List (Plane n) → State n → State n
  | [],state => state
  | plane::planes,state => evaluate planes (plane.apply state)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 34 → Bool) := true
noncomputable def machine := RepeatMachine.machine CompetitorPlanePacketPair.machine accepted
def tableBudget (w n count : ℕ) := count*(pairFuel w n+3)+3

theorem table_driver_run {n : ℕ} (b p total pos : ℕ) (planes : List (Plane n)) (state : State n)
    (pre suffix : List Bool) (ambient : Fin 34 → List Bool)
    (hpos : pos+planes.length=total) (htotal : total≤p)
    (hvalid : ∀ a∈planes,a.Valid b p)
    (hstate : Bounded b p (2*pos) state)
    (hcontext : TableContext b (CompetitorPlaneWidth.width b p) state ambient)
    (hsource : ambient 32=pre++stream b planes++suffix) :
    ∃ r out,runFrom machine (planes.length*(pairFuel (CompetitorPlaneWidth.width b p) n+2)+total+3)
      (RepeatMachine.cfg 0
        (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start pre.length ambient) total (pos+1))=some r ∧
      r.steps≤planes.length*(pairFuel (CompetitorPlaneWidth.width b p) n+2)+total+3 ∧
      r.final=RepeatMachine.cfg 3
        (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start (pre.length+(stream b planes).length) out) total 1 ∧
      TableContext b (CompetitorPlaneWidth.width b p) (evaluate planes state) out ∧
      out 32=pre++stream b planes++suffix ∧ Bounded b p (2*total) (evaluate planes state) := by
  induction planes generalizing pos state pre ambient with
  | nil =>
    have hp : pos=total := by simpa using hpos
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust CompetitorPlanePacketPair.machine accepted
      (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start pre.length ambient) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,ambient,by simpa [machine] using hr,by simpa using hs.le,?_,hcontext,?_,hstate⟩
    · simpa [stream] using hf
    · exact hsource
  | cons plane planes ih =>
    have hp := hvalid plane (by simp)
    obtain ⟨body,hbody,hbh,_,hbsrc,hbctx,hbbound,hbstep⟩ := uniform_pair_run pre (stream b planes++suffix)
      b p pos plane state ambient hcontext (by simpa [stream,List.append_assoc] using hsource)
      (by simp only [List.length_cons] at hpos; omega) hp hstate
    have iteration := RepeatMachine.iteration CompetitorPlanePacketPair.machine accepted
      (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start pre.length ambient)
      total pos body rfl (by simp only [List.length_cons] at hpos; omega) hbody
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start
          (pre++plane.word b).length body.final.tapes) total (pos+2) := by
      apply configuration_ext
      · rfl
      · simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hbh,CompetitorPlanePacketDock.cfg,List.length_append]
      · rfl
    rw [hend] at iteration
    obtain ⟨tail,out,htail,hts,htf,htctx,htsrc,htbound⟩ := ih (pos+1) (plane.apply state)
      (pre++plane.word b) body.final.tapes (by simp only [List.length_cons] at hpos; omega)
      (fun a ha => hvalid a (by simp [ha])) hbbound hbctx
      (by rw [hbsrc,hsource]; simp [stream,List.append_assoc])
    have htail' : runFrom machine (planes.length*(pairFuel (CompetitorPlaneWidth.width b p) n+2)+total+3)
        (RepeatMachine.cfg 0 (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start
          (pre++plane.word b).length body.final.tapes) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail htail'
    have htime : (body.steps+2)+(planes.length*(pairFuel (CompetitorPlaneWidth.width b p) n+2)+total+3)≤
        (plane::planes).length*(pairFuel (CompetitorPlaneWidth.width b p) n+2)+total+3 := by
      simp only [List.length_cons]
      nlinarith
    have hmore := runFrom_moreFuel machine _
      ((plane::planes).length*(pairFuel (CompetitorPlaneWidth.width b p) n+2)+total+3-
        ((body.steps+2)+(planes.length*(pairFuel (CompetitorPlaneWidth.width b p) n+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,out,hmore,?_,?_,htctx,?_,htbound⟩
    · rw [hs]
      simp only [List.length_cons]
      nlinarith
    · rw [hf,htf]
      simp [stream,List.length_append,Nat.add_assoc]
    · simpa [stream,List.append_assoc] using htsrc

theorem table_loop_run {n : ℕ} (b p : ℕ) (planes : List (Plane n)) (state : State n)
    (pre suffix : List Bool) (ambient : Fin 34 → List Bool)
    (hlength : planes.length≤p) (hvalid : ∀ a∈planes,a.Valid b p)
    (hstate : Bounded b p 0 state)
    (hcontext : TableContext b (CompetitorPlaneWidth.width b p) state ambient)
    (hsource : ambient 32=pre++stream b planes++suffix) :
    ∃ r out,runFrom machine (tableBudget (CompetitorPlaneWidth.width b p) n planes.length)
      (RepeatMachine.cfg 0
        (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start pre.length ambient) planes.length 1)=some r ∧
      r.steps≤tableBudget (CompetitorPlaneWidth.width b p) n planes.length ∧
      r.final=RepeatMachine.cfg 3
        (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start (pre.length+(stream b planes).length) out) planes.length 1 ∧
      TableContext b (CompetitorPlaneWidth.width b p) (evaluate planes state) out ∧
      out 32=pre++stream b planes++suffix ∧ Bounded b p (2*planes.length) (evaluate planes state) := by
  obtain ⟨r,out,hr,hs,hf,hc,hsrc,hb⟩ := table_driver_run b p planes.length 0 planes state pre suffix ambient
    (by omega) hlength hvalid (by simpa using hstate) hcontext hsource
  have he : planes.length*(pairFuel (CompetitorPlaneWidth.width b p) n+2)+planes.length+3=
      tableBudget (CompetitorPlaneWidth.width b p) n planes.length := by unfold tableBudget; ring
  exact ⟨r,out,by simpa only [he] using hr,by simpa only [he] using hs,hf,hc,hsrc,hb⟩

end NearCubicWires.RepairOrdinary.CompetitorPlaneTable
