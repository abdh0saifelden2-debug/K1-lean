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

#check @K1Lean.surrogateSpectrum
#check @K1Lean.surrogateSpectrum_star
#check @K1Lean.dft_invDFT
#check @K1Lean.norm_surrogateSpectrum
#check @K1Lean.norm_dft_invDFT_surrogateSpectrum
#check @K1Lean.phase_surrogateSpectrum
#print axioms K1Lean.surrogateSpectrum_star
#print axioms K1Lean.dft_invDFT
#print axioms K1Lean.norm_surrogateSpectrum
#print axioms K1Lean.norm_dft_invDFT_surrogateSpectrum
#print axioms K1Lean.phase_surrogateSpectrum
