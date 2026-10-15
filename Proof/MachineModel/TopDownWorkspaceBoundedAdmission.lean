import Proof.MachineModel.TopDownWorkspaceGuardedWorker
import Proof.CaseAnalysis.WitnessBoundedFamilyBudget

/-! A sealed state-count package for the existing bounded parser, exposing its
actual total receipt without normalizing the source compiler's state arithmetic
through every later composition. No new parser or semantic advice is added. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceBoundedAdmission
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal
open WorkspaceGuardedWorker (input entry)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine

def tapes (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k D G E : Nat) : Nat :=
  HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1

@[irreducible] def program (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen : Nat)
    (delta : Rat) (code : List Bool) : Sigma (fun s => Machine (tapes source a k D G E) s) :=
  ⟨_,BoundedFamilySupport.actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen
    (CloseoutMassThreshold.literalWidth delta copies) delta
    (CloseoutSampledWitness.massCap delta copies) code⟩

theorem source_run (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen : Nat)
    (delta : Rat) (code : List Bool) {n : Nat} (x : BitInput n) (bits : List Bool)
    (hpad : k+3 ≤ Cpad) (hD : 1 ≤ D) (hsym : 0 < symDen) (hthr : 0 < thrDen)
    (hK : 0 < K) (hcut : 2^a.minimumArity ≤ cutoff)
    (hd : 0 < delta) (hh : delta < 1/2) (hc : 1 ≤ copies)
    (hbudget : ∀ N, FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)
      ≤ K*(N+1)^E) :
    ∃ H A,Step (program source a k CH Cpad cutoff D G copies E K symDen thrDen delta code).2
      (2*BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad)
      (fun _ => 0) (BoundedFamilySupport.input source a k D G E (List.ofFn x) bits) H A ∧
      H (BoundedFamilySupport.flag source a k D G E)=0 ∧
      readTapeBit (A (BoundedFamilySupport.flag source a k D G E)) 0 =
        BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad := by
  obtain ⟨actual,hrun,hsteps,hhead,hflag,_selected,_cache⟩ :=
    CloseoutFinalC10ColdCacheAtAdmission.bounded_cache source a k CH Cpad cutoff D G copies E K
      symDen thrDen delta code x bits hpad hD hsym hthr hK hcut hd hh hc hbudget
  refine ⟨actual.final.heads,actual.final.tapes,?_,hhead,hflag⟩
  unfold program
  exact ⟨actual,hrun,rfl,rfl,hsteps⟩

theorem input_eq (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k D G E : Nat) (x bits : List Bool) :
    BoundedFamilySupport.input source a k D G E x bits = input x bits := by
  funext j
  change SupportDock.lift (HeaderDock.input (BoundedFamily.workspace source a k D G E)
    (CompetitorWitnessBounded.input x bits)) [] j = _
  refine Fin.addCases (m:=HeaderDock.tapes (BoundedFamily.workspace source a k D G E)) (n:=1) ?_ ?_ j
  · intro j
    rw [SupportDock.lift,Fin.addCases_left]
    refine Fin.addCases (m:=150) (n:=BoundedFamily.workspace source a k D G E+1) ?_ ?_ j
    · intro j
      simp only [HeaderDock.input,Fin.addCases_left,input,Fin.val_castAdd]
      exact CompetitorWitnessBounded.input_eq x bits j
    · intro j
      simp only [HeaderDock.input,Fin.addCases_right,input,Fin.val_castAdd,Fin.val_natAdd]
      rw [if_neg (by omega),if_neg (by omega)]
  · intro j
    simp only [SupportDock.lift,Fin.addCases_right,input,Fin.val_natAdd]
    rw [if_neg (by dsimp [HeaderDock.tapes];omega),if_neg (by dsimp [HeaderDock.tapes];omega)]

def uniformFuel (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) {k : Nat} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad cutoff D G copies E K symDen thrDen : Nat) (delta : Rat) (n : Nat) : Nat :=
  2*(ColdNative.bound source a D G copies cutoff delta (HierarchyBudget.scale source H Cpad n)+
    BoundedFamily.outerBound source a G D copies E K symDen thrDen delta n)

theorem uniform_run (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) {k : Nat} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad cutoff D G copies E K symDen thrDen : Nat) (delta : Rat)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad)
    (hD : 1 ≤ D) (hsym : 0 < symDen) (hthr : 0 < thrDen)
    (hK : 0 < K) (hcut : 2^a.minimumArity ≤ cutoff)
    (hd : 0 < delta) (hh : delta < 1/2) (hc : 1 ≤ copies)
    (hbudget : ∀ N,FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)
      ≤ K*(N+1)^E) (n : Nat) (x : BitInput n) (bits : List Bool) :
    ∃ heads A,Step (program source a k H.coefficient Cpad cutoff D G copies E K symDen thrDen delta
      (VerifierEncoding.code H.verifier)).2
      (uniformFuel source a H Cpad cutoff D G copies E K symDen thrDen delta n)
      (fun _ => 0) (input (List.ofFn x) bits) heads A ∧
      readTapeBit (A (BoundedFamilySupport.flag source a k D G E))
        (heads (BoundedFamilySupport.flag source a k D G E)) =
        BoundedFamily.passed source a k H.coefficient Cpad cutoff D G copies symDen thrDen delta
          (VerifierEncoding.code H.verifier) x bits hpad := by
  obtain ⟨heads,A,hr,hhead,hflag⟩ := source_run source a k H.coefficient Cpad cutoff D G copies E K
    symDen thrDen delta (VerifierEncoding.code H.verifier) x bits hpad hD hsym hthr hK hcut hd hh hc hbudget
  rw [input_eq] at hr
  refine ⟨heads,A,hr.enlarge ?_,?_⟩
  · exact Nat.mul_le_mul_left 2 (BoundedFamily.budget_le source a H Cpad cutoff D G copies E K
      symDen thrDen delta hcoeff hpad hcut hbudget ⟨n,x⟩ bits)
  · rw [hhead,hflag]

end
end NearCubicWires.P1TopDown.WorkspaceBoundedAdmission
