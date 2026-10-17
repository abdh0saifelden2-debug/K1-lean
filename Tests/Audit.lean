import K1Lean.Parseval
import K1Lean.Surrogate

#check @Surrogate.isProjector
#print axioms Surrogate.projector_idempotent

#check @K1Lean.dft_star
#check @K1Lean.dft_ofReal_conj
#print axioms K1Lean.dft_star
#print axioms K1Lean.dft_ofReal_conj

#check @K1Lean.invDFT_selfConj
#check @K1Lean.invDFT_im_eq_zero
#check @K1Lean.invDFT_eq_ofReal_re
#print axioms K1Lean.invDFT_selfConj
#print axioms K1Lean.invDFT_im_eq_zero
#print axioms K1Lean.invDFT_eq_ofReal_re
