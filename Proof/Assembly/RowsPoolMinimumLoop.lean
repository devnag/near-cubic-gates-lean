import Proof.Assembly.RowsPoolMinimumBody

/-! The original arity driver executes the live-negative accumulation over
every serialized weight. Source and mask cursors advance together; the one
scalar workspace and its paid C driver are reusable at every iteration. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairRepresentation
open RepairSource.VerifierDecoding CloseoutRowsPoolWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def negSum (xs : List Item):=(xs.map (fun x=>(-x.1).toNat)).sum
def liveSum (xs : List Item):=(xs.map (fun x=>if x.2 then (-x.1).toNat else 0)).sum
noncomputable def loop:=RepeatMachine.machine body (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (membership : List Bool) (mpos w C a total driver : ℕ):=
  RepeatMachine.cfg phase (⟨body.start,heads pos mpos,data source membership w C a⟩) total driver

theorem remaining (xs : List Item) (pre tail mpre mtail : List Bool)
    (w C a total pos : ℕ) (hn : pos+xs.length=total)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hf : a+negSum xs<2^w) :
    ∃ time≤xs.length*(uniformBudget w C+2)+total+3,Timed loop time
      (cfg 0 (pre++word xs++tail) pre.length (mpre++mask xs++mtail) mpre.length w C a total (pos+1))
      (cfg 3 (pre++word xs++tail) (pre.length+(word xs).length)
        (mpre++mask xs++mtail) (mpre.length+xs.length) w C (a+liveSum xs) total 1):=by
  induction xs generalizing pre mpre a pos with
  | nil=>
    have he:pos=total:=by simpa using hn
    subst pos
    refine ⟨total+3,by simp,?_⟩
    simpa [cfg,loop,word,mask,liveSum] using RepeatMachine.exhaust body (fun _ _=>true)
      (⟨body.start,heads pre.length mpre.length,data (pre++tail) (mpre++mtail) w C a⟩) total
  | cons x xs ih=>
    have hx:=hw x (by simp)
    have htail:∀ y∈xs,natBitLength y.1.natAbs≤w:=fun y hy=>hw y (by simp [hy])
    have hf':a+((-x.1).toNat+negSum xs)<2^w:=by
      simpa only [negSum,List.map_cons,List.sum_cons] using hf
    have hpiece:(if x.2 then (-x.1).toNat else 0)≤(-x.1).toNat:=by
      cases x.2 <;> simp
    obtain ⟨r,hr,rh,rt,rs⟩:=body_run pre (word xs++tail) mpre (mask xs++mtail)
      x.1 x.2 w C a hx hc (by omega)
    have one:=RepeatMachine.iteration body (fun _ _=>true)
      ⟨body.start,heads pre.length mpre.length,
        data (pre++intWord x.1++(word xs++tail)) (mpre++x.2::(mask xs++mtail)) w C a⟩
      total pos r rfl (by simp only [List.length_cons] at hn;omega) hr
    simp only [↓reduceIte] at one
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (⟨body.start,heads (pre.length+(intWord x.1).length) (mpre.length+1),
        data (pre++intWord x.1++(word xs++tail)) (mpre++x.2::(mask xs++mtail)) w C
          (a+if x.2 then (-x.1).toNat else 0)⟩) total (pos+2) rh rt] at one
    obtain ⟨t,ht,rest⟩:=ih (pre++intWord x.1) (mpre++[x.2])
      (a+if x.2 then (-x.1).toNat else 0) (pos+1)
      (by simp only [List.length_cons] at hn;omega) htail (by omega)
    have hp:(pre++intWord x.1).length=pre.length+(intWord x.1).length:=List.length_append
    have hm:(mpre++[x.2]).length=mpre.length+1:=by simp
    simp only [cfg,List.append_assoc,List.singleton_append,hp,hm,show pos+1+1=pos+2 by omega] at rest
    simp only [List.append_assoc,List.cons_append] at one rest
    have all:=one.trans rest
    refine ⟨r.steps+2+t,?_,?_⟩
    · have hb:=rs.trans (body_bound x.1 w C hx)
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [loop,cfg,word,mask,liveSum,List.flatMap_cons,List.map_cons,List.sum_cons,
        List.length_append,List.length_cons,List.append_assoc,List.cons_append,Nat.add_assoc,
        Nat.add_comm 1 xs.length] using all

def loopBudget (xs : List Item) (w C : ℕ):=xs.length*(uniformBudget w C+3)+3

theorem minimum_run (xs : List Item) (pre tail mpre mtail : List Bool) (w C a : ℕ)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C) (hf : a+negSum xs<2^w) :
    ∃ r,runFrom loop (loopBudget xs w C)
      (cfg 0 (pre++word xs++tail) pre.length (mpre++mask xs++mtail) mpre.length w C a xs.length 1)=some r ∧
      r.final=cfg 3 (pre++word xs++tail) (pre.length+(word xs).length)
        (mpre++mask xs++mtail) (mpre.length+xs.length) w C (a+liveSum xs) xs.length 1 ∧
      r.steps≤loopBudget xs w C:=by
  obtain ⟨t,ht,h⟩:=remaining xs pre tail mpre mtail w C a xs.length 0 (by omega) hw hc hf
  obtain ⟨r,hr,hfinal,hs⟩:=h.run (by simp [loop,cfg,RepeatMachine.machine,RepeatMachine.cfg,
    controlConfig,RepeatMachine.phaseCode])
  have hb:t≤loopBudget xs w C:=by
    unfold loopBudget
    have he:xs.length*(uniformBudget w C+2)+xs.length+3=
        xs.length*(uniformBudget w C+3)+3:=by ring
    omega
  have more:=runFrom_moreFuel loop t (loopBudget xs w C-t) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,hfinal,hs.le.trans hb⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
