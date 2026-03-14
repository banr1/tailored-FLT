import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.Basic.FreyPackage
import LeanAtlas.Metadata.Attribute.Meta

variable (P : FreyPackage)

open GaloisRepresentation

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- We cannot hope to make a constructive decidable equality on `AlgebraicClosure ℚ` because
it is defined in a completely nonconstructive way, so we add the classical instance. -/
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

set_option linter.style.whitespace false in
set_option linter.style.longLine false in
@[formalMeta "Frey torsion is hardly ramified" "The p-torsion Galois representation of the Frey curve is hardly ramified" mainTheorem]
theorem FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    IsHardlyRamified P.hp_odd sorry
      (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry

theorem FreyCurve.torsion_not_isIrreducible :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  sorry -- TODO prove this
