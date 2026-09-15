import NavierStokes.CounterProof.TerminalCertificate
import NavierStokes.CrossBasedMeanComposition
import NavierStokes.ActualCycleResidualBounds

/-!
# Signed-mean source interface

This module is the downstream attachment point prescribed by the companion
note.  It imports completed proofs for the literal signed update, cross defect,
iteration ledger, and physical residual machinery from `NavierStokes/` rather
than reproving them or introducing a surrogate covariance model.  Concrete
counter-proof modules should add adapters and new obstruction theorems while
retaining those imported results as their source foundation.

Future phases should add theorem adapters here in this order:

1. differentiate the actual reconstructed state;
2. identify the reduced cross response;
3. expand the hidden response defined by subtraction;
4. propagate inverse and physical-jet losses;
5. instantiate a dual or relative-contraction certificate;
6. control the complete future tail; and
7. expose the surviving mismatch in the physical residual.
-/

namespace NavierStokes.CounterProof.SignedMeanInterface

/-- Upstream source revision audited by the downstream companion note. -/
def pinnedUpstreamCommit : String :=
  "f9e8bc5b38b6e212696e8a30e3e91517af887bbd"

export NavierStokes.SignedMeanGain
  (incrementTensor_split waveStage_covariance waveStage_theta_change
    waveStage_gr_change waveStage_axial_change signed_tensor_bounds)

export NavierStokes.CrossBasedMeanComposition
  (cross_cancels_with_defect signed_mean_gain_of_cross_defects)

end NavierStokes.CounterProof.SignedMeanInterface
